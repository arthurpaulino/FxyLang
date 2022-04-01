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
    let es ← es.data.mapM mkExpression
    if h : ¬ es.isEmpty
      then return .app n.getId.toString (es.toNEList h)
      else return .var n.getId.toString
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
  | `(program| skip) =>
    return Program.skip
  | `(program| $p:program; $q:program) =>
    return .sequence (← mkProgram p) (← mkProgram q)
  | `(program| $n:ident $ns:ident* := $p:program) =>
    let ns := ns.data.map $ fun i => i.getId.toString
    if h : ¬ ns.isEmpty
      then return .attribution n.getId.toString $
        .evaluation $ .atom $
          .curry (ns.toNEList h) (← mkProgram p)
      else return .attribution n.getId.toString (← mkProgram p)
  | `(program| if $e:expression then $p:program else $q:program) =>
    return .ifElse (← mkExpression e)
      (← mkProgram p) (← mkProgram q)
  | `(program| while $e:expression do $p:program) =>
    return .whileLoop (← mkExpression e) (← mkProgram p)
  | `(program| $e:expression) =>
    return .evaluation (← mkExpression e)
  | `(program| ($p:program)) => mkProgram p
  | _ => throw "error: can't parse program"

partial def parseProgram : Environment → String → Except String Program
  | env, s => do mkProgram (← Parser.runParserCategory env `program s)

def joinedOn (on : String) : List String → String
  | []            => ""
  | [s]           => s
  | s :: s' :: ss => s ++ on ++ joinedOn on (s' :: ss)

def removeComments (l : String) : String :=
  l.splitOn "#" |>.headD ""

def replaceTabs (s : String) : String :=
  s.replace "\t" " "

def cleanseLine (l : String) : String :=
  replaceTabs $ removeComments l |>.trimRight

def cleanseCode (c : String) : String :=
  joinedOn "\n" $
    (c.splitOn "\n" |>.map cleanseLine).filter fun l => ¬ l.isEmpty

def metaParse (c : String) : MetaM (Option String × Program) := do
  match parseProgram (← getEnv) (cleanseCode c) with
  | .error msg => return (some msg, default)
  | .ok    p   => return (none, p)

def parse (c : String) (env : Environment) : IO (Option String × Program) := do
  Prod.fst <$> (metaParse c).run'.toIO {} {env}

-- def code := "s := 0; a := 0; (while a < 5 do a := a + 1; s := s + a); s"
def code := "f x y := x + y; f3 := f 3; f32 := f3 2; a"
-- def code := "a := 1 + 1; a = 2"

#eval show MetaM _ from do
  let p := parseProgram (← getEnv) (cleanseCode code)
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
