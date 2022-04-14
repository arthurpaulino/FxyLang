/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import Lean
import FxyLang.Execution
import FxyLang.Syntax

open Lean

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

partial def mkExpression : Syntax → Except String Expression
  | `(expression| $v:literal)     => return .lit (← mkLiteral v)
  | `(expression| !$e:expression) => return .unOp .not (← mkExpression e)
  | `(expression| $n:ident)       => return .var n.getId.toString
  | `(expression| $n:ident $[$es:expression]*) => do
    match ← es.data.mapM mkExpression with
    | []      => unreachable!
    | e :: es => return .app n.getId.toString (es.toNEList e)
  | `(expression| $l:expression $o:binop $r:expression) =>
    return .binOp (← mkBinOp o) (← mkExpression l) (← mkExpression r)
  | `(expression| [$ls:literal,*]) =>
    return .list $ ← ls.getElems.data.mapM mkLiteral
  | `(expression| ($e:expression)) => mkExpression e
  | _ => throw "error: can't parse expression"

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
      if h : nl.noDup then
        return .decl n $ .eval $ .lam $ .mk nl h (← mkProgram p)
      else throw $ s!"error: definition of curried function {n} has " ++
        "duplicated variables"
  | `(program| if $e:expression then $p:programSeq $[else $q:programSeq]?) => do
    let q ← match q with
    | none   => pure $ Program.skip
    | some q => mkProgram q
    return .fork (← mkExpression e) (← mkProgram p) q
  | `(program| while $e:expression do $p:programSeq) =>
    return .loop (← mkExpression e) (← mkProgram p)
  | `(program| !print $e:expression) => return .print (← mkExpression e)
  | _ => throw "error: can't parse program"

partial def parseProgram : Environment → String → Except String Program
  | env, s => do mkProgram (← Parser.runParserCategory env `programSeq s)

def joinedOn (on : String) : List String → String
  | []            => ""
  | [s]           => s
  | s :: s' :: ss => s ++ on ++ joinedOn on (s' :: ss)

def cleanseLine (l : String) : String :=
  l.splitOn "#" |>.headD "" |>.trimRight.replace "\t" " "

def cleanseCode (c : String) : String :=
  joinedOn "\n" $
    (c.splitOn "\n" |>.map cleanseLine).filter fun l => ¬ l.isEmpty

def metaParse : String → Environment → MetaM (Option String × Program)
  | c, env => match parseProgram env (cleanseCode c) with
    | .error msg => return (some msg, default)
    | .ok    p   => return (none, p)

def parse : String → Environment → IO (Option String × Program)
  | c, env => Prod.fst <$> (metaParse c env).run'.toIO {} default

-- def code := "
-- ((x := 1)
--  (a := 2))
-- "

-- def code := "
-- x := 1
-- a := 2
-- "

-- def code := "
-- s := 0
-- a := 0
-- while a < 5 do
--   a := a + 1
--   s := s + a
-- s
-- "

-- def code := "
-- f x y := x + y
-- f3 := f 3
-- f32 := f3 2
-- "

-- def code := "
-- succ x := x + 1
-- app1 f x := f x #sdfsf
-- a := 7     # afa
-- app1 succ a
-- "

def code := "
x x := x + 5
x 4
[1, \"oi\", 1.5]
"

def cCode := cleanseCode code
#eval cCode
#eval show MetaM _ from do
  let p := parseProgram (← getEnv) cCode
  match p with
    | Except.ok p =>
      let (c, r) := p.run
      IO.println r
      IO.println "------context-------"
      IO.println c
      IO.println "------program-------"
      IO.println p
      IO.println "--------AST---------"
    | _ => pure ()
  return p
