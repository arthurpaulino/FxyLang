/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import Lean
import FunnyLang.AST
import FunnyLang.Syntax

open Lean

def mkValue : Syntax → Except String Value
  | `(value|$n:numLit) => return .int n.toNat
  | _ => throw "error: can't parse value"

partial def mkExpression : Syntax → Except String Expression
  | `(expression| $v:value)       => return .atom (← mkValue v)
  | `(expression| !$e:expression) => return .not (← mkExpression e)
  | `(expression| $n:ident $[$es:expression]*) => do
    match ← es.data.mapM mkExpression with
    | []      => return .var n.getId.toString
    | e :: es => return .app n.getId.toString (es.toNEList e)
  | `(expression| $l:expression + $r:expression) =>
    return .add (← mkExpression l) (← mkExpression r)
  | `(expression| $l:expression * $r:expression) =>
    return .mul (← mkExpression l) (← mkExpression r)
  | `(expression| $l:expression = $r:expression) =>
    return .eq (← mkExpression l) (← mkExpression r)
  | `(expression| $l:expression != $r:expression) =>
    return .ne (← mkExpression l) (← mkExpression r)
  | `(expression| $l:expression < $r:expression) =>
    return .lt (← mkExpression l) (← mkExpression r)
  | `(expression| $l:expression <= $r:expression) =>
    return .le (← mkExpression l) (← mkExpression r)
  | `(expression| $l:expression > $r:expression) =>
    return .gt (← mkExpression l) (← mkExpression r)
  | `(expression| $l:expression >= $r:expression) =>
    return .ge (← mkExpression l) (← mkExpression r)
  | `(expression| ($e:expression)) => mkExpression e
  | _ => throw "error: can't parse expression"

partial def mkProgram : Syntax → Except String Program
  | `(programSeq| $p:program $[$ps:program]*) => do
    ps.foldlM (init := ← mkProgram p) fun a b => do
      return .sequence a (← mkProgram b)
  | `(program| skip) => return Program.skip
  | `(program| $n:ident $ns:ident* := $p:programSeq) =>
    match ns.data.map $ fun i => i.getId.toString with
    | []       => return .attribution n.getId.toString (← mkProgram p)
    | n' :: ns =>
      return .attribution n.getId.toString $
        .evaluation $ .atom $
          .curry (ns.toNEList n') (← mkProgram p)
  | `(program| if $e:expression then $p:programSeq $[else $q:programSeq]?) => do
    let q ← match q with
    | none   => pure $ Program.skip
    | some q => mkProgram q
    return .ifElse (← mkExpression e) (← mkProgram p) q
  | `(program| while $e:expression do $p:programSeq) =>
    return .whileLoop (← mkExpression e) (← mkProgram p)
  | `(program| $e:expression) =>
    return .evaluation (← mkExpression e)
  | `(program| ($p:programSeq)) => mkProgram p
  | _ => throw "error: can't parse program"

partial def parseProgram : Environment → String → Except String Program
  | env, s => do mkProgram (← Parser.runParserCategory env `programSeq s)

def joinedOn (on : String) : List String → String
  | []            => ""
  | [s]           => s
  | s :: s' :: ss => s ++ on ++ joinedOn on (s' :: ss)

def removeComments (l : String) : String :=
  l.splitOn "#" |>.headD ""

def replaceTabs (s : String) : String :=
  s.replace "\t" " "

def cleanseLine (l : String) : String :=
  (replaceTabs $ removeComments l).trimRight

def cleanseCode (c : String) : String :=
  joinedOn "\n" $
    (c.splitOn "\n" |>.map cleanseLine).filter fun l => ¬ l.isEmpty

def metaParse (c : String) : MetaM (Option String × Program) := do
  match parseProgram (← getEnv) (cleanseCode c) with
  | .error msg => return (some msg, default)
  | .ok    p   => return (none, p)

def parse (c : String) (env : Environment) : IO (Option String × Program) := do
  Prod.fst <$> (metaParse c).run'.toIO {} {env}

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

def code := "
if 1 = 1 then
  x := 1
else
  x := 2

if 1=1 then
  y := 2
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
