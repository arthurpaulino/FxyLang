/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import Lean
import FxyLang.Implementation.AST
import FxyLang.Implementation.Syntax

/- This file deals with terms of type `Syntax` from Lean's internals, so we're
going to use the API with functions such as `toNat`, `isStrLit?`, `getId` etc -/

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
    | none   => unreachable! -- because of `s:str`
  | `(literal| $[-%$neg]?$f:scientific) => match f.isScientificLit? with
    | some (m, s, e) =>
      if neg.isNone
        then return .float $ OfScientific.ofScientific m s e
        else return .float $ - OfScientific.ofScientific m s e
    | none           => unreachable! -- because of `f:scientific`
  | _ => throw "error: can't parse value"

/-- Parsing a binary operator syntax -/
def mkBinOp : Syntax → Except String BinOp
  | `(binop| + ) => return BinOp.add
  | `(binop| * ) => return BinOp.mul
  | `(binop| < ) => return BinOp.lt
  | `(binop| <=) => return BinOp.le
  | `(binop| > ) => return BinOp.gt
  | `(binop| >=) => return BinOp.ge
  | `(binop| = ) => return BinOp.eq
  | `(binop| !=) => return BinOp.ne
  | _ => throw "error: can't parse binary operator"

/-- Parsing an expression syntax -/
partial def mkExpression : Syntax → Except String Expression
  | `(expression| $v:literal)     => return .lit (← mkLiteral v)
  | `(expression| !$e:expression) => return .unOp .not (← mkExpression e)
  | `(expression| $n:ident)       => return .var n.getId.toString
  | `(expression| $e:expression $[$es:expression]*) => do
    match ← es.data.mapM mkExpression with
    | []       => unreachable! -- because `es` uses `+` in the syntax definition
    | e' :: es => return .app (← mkExpression e) (es.toNEList e')
  | `(expression| $l:expression $o:binop $r:expression) =>
    return .binOp (← mkBinOp o) (← mkExpression l) (← mkExpression r)
  | `(expression| [$ls:literal,*]) =>
    return .list $ ← ls.getElems.data.mapM mkLiteral
  | `(expression| ($e:expression)) => mkExpression e
  | _ => throw "error: can't parse expression"

/-- Parsing a program syntax -/
partial def mkProgram : Syntax → Except String Program
  | `(program| skip) => return Program.skip
  | `(program| $e:expression) => return .eval (← mkExpression e)
  | `(programSeq| $p:program $[$ps:program]*) => do
    -- call `mkProgram` recursively and join each pair of consecutive programs
    -- as a `seq` program
    ps.foldlM (init := ← mkProgram p) fun a b => return .seq a (← mkProgram b)
  | `(program| $nm:ident $ns:ident* := $p:programSeq) =>
    let ns : List String := ns.data.map $ fun i => i.getId.toString
    match ns with
    | []       => return .decl nm.getId.toString (← mkProgram p) -- no arguments
    | n :: ns => -- arguments signal that a function is being declared
      let nm := nm.getId.toString -- the name of the function
      let nl := ns.toNEList n     -- the list of arguments
      if h : nl.noDup then -- here we need to check for duplicated arguments
        return .decl nm $ .eval $ .lam $ .mk nl h (← mkProgram p)
      else throw $ s!"error: the definition of the function {nm} has " ++
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

/-- Cleanse each line and joins them with a "\n" -/
def cleanseCode (c : String) : String :=
  "\n".intercalate $
    (c.splitOn "\n" |>.map cleanseLine).filter fun l => ¬ l.isEmpty

/-- Let's parse our program *as if* we were parsing Lean code -/
def parseProgram (s : String) (env : Environment) : Except String Program := do
  mkProgram (← Parser.runParserCategory env `programSeq s)

/-- Calls `parseProgram` with a clean code -/
def parse (s : String) (env : Environment) : Option String × Program :=
  match parseProgram (cleanseCode s) env with
    | .error msg => (some msg, default)
    | .ok    p   => (none, p)
