/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import Lean
import FxyLang.Implementation.AST
import FxyLang.Implementation.Syntax

open Lean

/-- Parsing a literal syntax -/
def mkLiteral : Syntax → Except String _root_.Literal
  | `(literal| $[-%$neg]?$n:num) =>
    if neg.isNone
      then return .int $ Int.ofNat n.toNat
      else return .int $ Int.negOfNat n.toNat
  | `(literal| true)   => return .bool Bool.true
  | `(literal| false)  => return .bool Bool.false
  | `(literal| $s:str) => match s.isStrLit? with
    | some s => return .str s
    | none   => unreachable!
  | `(literal| $[-%$neg]?$f:scientific) => match f.isScientificLit? with
    | some (m, s, e) =>
      if neg.isNone
        then return .float $ OfScientific.ofScientific m s e
        else return .float $ - OfScientific.ofScientific m s e
    | none           => unreachable!
  | _ => throw "error: can't parse value"

/-- Parsing a binary operator syntax -/
def mkBinOp : Syntax → Except String BinOp
  | `(binop| +)  => return BinOp.add
  | `(binop| *)  => return BinOp.mul
  | `(binop| <)  => return BinOp.lt
  | `(binop| <=) => return BinOp.le
  | `(binop| >)  => return BinOp.gt
  | `(binop| >=) => return BinOp.ge
  | `(binop| =)  => return BinOp.eq
  | `(binop| !=) => return BinOp.ne
  | _ => throw "error: can't parse binary operator"

/-- Parsing an expression syntax -/
partial def mkExpression : Syntax → Except String Expression
  | `(expression| $v:literal)     => return .lit (← mkLiteral v)
  | `(expression| !$e:expression) => return .unOp .not (← mkExpression e)
  | `(expression| $n:ident)       => return .var n.getId.toString
  | `(expression| $e:expression $[$es:expression]*) => do
    match ← es.data.mapM mkExpression with
    | []      => unreachable! -- because `es` uses `+` in the syntax definition
    | e' :: es => return .app (← mkExpression e) (es.toNEList e')
  | `(expression| $l:expression $o:binop $r:expression) =>
    return .binOp (← mkBinOp o) (← mkExpression l) (← mkExpression r)
  | `(expression| [$ls:literal,*]) =>
    return .list $ ← ls.getElems.data.mapM mkLiteral
  | `(expression| ($e:expression)) => mkExpression e
  | _ => throw "error: can't parse expression"

/-- Parsing a program syntax -/
partial def mkProgram : Syntax → Except String Program
  | `(program| skip)  => return Program.skip
  | `(program| $e:expression) =>
    return .eval (← mkExpression e)
  | `(programSeq| $p:program $[$ps:program]*) => do
    ps.foldlM (init := ← mkProgram p) fun a b =>
      return .seq a (← mkProgram b)
  | `(program| $n:ident $ns:ident* := $p:programSeq) =>
    let ns := ns.data.map $ fun i => i.getId.toString
    match ns with
    | []       => return .decl n.getId.toString (← mkProgram p)
    | n' :: ns =>
      let n := n.getId.toString
      let nl := ns.toNEList n'
      if h : nl.noDup then -- here we need to check for duplications
        return .decl n $ .eval $ .lam $ .mk nl h (← mkProgram p)
      else throw $ s!"error: definition of curried function {n} has " ++
        "duplicated variables"
  | `(program| if $e:expression then $p:programSeq $[else $q:programSeq]?) => do
    let q ← match q with
    | none   => pure $ Program.skip -- `else` was ommitted. Simulate a `skip`
    | some q => mkProgram q
    return .fork (← mkExpression e) (← mkProgram p) q
  | `(program| while $e:expression do $p:programSeq) =>
    return .loop (← mkExpression e) (← mkProgram p)
  | `(program| !print $e:expression) => return .print (← mkExpression e)
  | _ => throw "error: can't parse program"

/-- Removes comentaries and replaces tabs by empty spaces -/
def cleanseLine (l : String) : String :=
  l.splitOn "#" |>.headD "" |>.trimRight.replace "\t" " "

/-- Glues the elements of a `List String` with a separator -/
def joinedOn (on : String) : List String → String
  | []            => ""
  | [s]           => s
  | s :: s' :: ss => s ++ on ++ joinedOn on (s' :: ss)

/-- Cleanse each line and joins them with a "\n" -/
def cleanseCode (c : String) : String :=
  joinedOn "\n" $
    (c.splitOn "\n" |>.map cleanseLine).filter fun l => ¬ l.isEmpty

/-- Let's parse our program *as if* we were parsing Lean code -/
def parseProgram : Environment → String → Except String Program
  | env, s => do mkProgram (← Parser.runParserCategory env `programSeq s)

/-- Calls `parseProgram` with a clean code -/
def parse : String → Environment → Option String × Program
  | s, env => match parseProgram env (cleanseCode s) with
    | .error msg => (some msg, default)
    | .ok    p   => (none, p)
