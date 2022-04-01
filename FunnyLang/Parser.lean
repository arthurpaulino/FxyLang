/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import Lean
import FunnyLang.AST

/-! example
a := 4         # int

f x y := x + y # function _ → _ → _

fa := f a      # function int → int

fa3 := fa 3    # 7 : int

g n :=
  s := 0
  while > 0
    s := s + n
    n := n - 1
  s

print g 5      # 15
-/

declare_syntax_cat value
syntax ("-" noWs)? num : value
syntax str : value
syntax "true" : value
syntax "false" : value
syntax ("-" noWs)? num noWs "." (noWs num)? : value
syntax " [ " value* " ] " : value

declare_syntax_cat expression
syntax value : expression
syntax expression " + " expression : expression
syntax expression " * " expression : expression
syntax " ! " expression : expression
syntax expression " = " expression : expression
syntax expression " != " expression : expression
syntax expression " < " expression : expression
syntax expression " <= " expression : expression
syntax expression " > " expression : expression
syntax expression " >= " expression : expression
syntax ident expression* : expression
syntax " ( " expression " ) " : expression

declare_syntax_cat program
syntax "skip" : program
syntax:25 program " ; " program : program
syntax ident ident* " := " program:75 : program
syntax expression : program
syntax "if" expression "then" program "else" program : program
syntax "while" expression "do" program : program
syntax " ( " program " ) " : program

open Lean Parser

def elabValue : Syntax → Except String Value
  | `(value|$x:numLit) => return Value.int x.toNat
  | _ => throw "error: can't parse value"

partial def elabExpression : Syntax → Except String Expression
  | `(expression| $x:value) =>
    return Expression.atom (← elabValue x)
  | `(expression| $x:expression + $y:expression) =>
    return Expression.add (← elabExpression x) (← elabExpression y)
  | `(expression| $x:expression * $y:expression) =>
    return Expression.mul (← elabExpression x) (← elabExpression y)
  | `(expression| ! $x:expression) =>
    return Expression.not (← elabExpression x)
  | `(expression| $x:ident $[$ys:expression]*) => do
    let ys := (← ys.mapM elabExpression).data
    if h : ¬ ys.isEmpty
      then return Expression.app x.getId.toString (ys.toNEList h)
      else return Expression.var x.getId.toString
  | `(expression| $x:expression = $y:expression) =>
    return Expression.eq (← elabExpression x) (← elabExpression y)
  | `(expression| $x:expression != $y:expression) =>
    return Expression.ne (← elabExpression x) (← elabExpression y)
  | `(expression| $x:expression < $y:expression) =>
    return Expression.lt (← elabExpression x) (← elabExpression y)
  | `(expression| $x:expression <= $y:expression) =>
    return Expression.le (← elabExpression x) (← elabExpression y)
  | `(expression| $x:expression > $y:expression) =>
    return Expression.gt (← elabExpression x) (← elabExpression y)
  | `(expression| $x:expression >= $y:expression) =>
    return Expression.ge (← elabExpression x) (← elabExpression y)
  | `(expression| ($x:expression)) => elabExpression x
  | _ => throw "error: can't parse expression"

partial def elabProgram : Syntax → Except String Program
  | `(program| skip) =>
    return Program.skip
  | `(program| $x:program; $y:program) =>
    return Program.sequence (← elabProgram x) (← elabProgram y)
  | `(program| $x:ident $xs:ident* := $y:program) =>
    let xs := (xs.map $ fun i => i.getId.toString).data
    if h : ¬ xs.isEmpty
      then return Program.attribution x.getId.toString $
        Program.evaluation $ Expression.atom $
          Value.curry (xs.toNEList h) (← elabProgram y)
      else return Program.attribution x.getId.toString (← elabProgram y)
  | `(program| if $e:expression then $p:program else $q:program) =>
    return Program.ifElse (← elabExpression e) (← elabProgram p)
      (← elabProgram q)
  | `(program| while $e:expression do $p:program) =>
    return Program.whileLoop (← elabExpression e) (← elabProgram p)
  | `(program| $x:expression) =>
    return Program.evaluation (← elabExpression x)
  | `(program| ($p:program)) => elabProgram p
  | _ => throw "error: can't parse program"

partial def parseProgram (env : Environment) (s : String) :
    Except String Program := do
  elabProgram (← runParserCategory env `program s)

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
  | Except.error msg => return (some msg, default)
  | Except.ok p      => return (none, p)

def parse (c : String) (env : Environment) : IO (Option String × Program) := do
  Prod.fst <$> (metaParse c).run'.toIO {} {env}

def code := "s := 0; a := 0; (while a < 5 do a := a + 1; s := s + a); s"
-- def code := "f x y := x + y; f3 := f 3; f32 := f3 2; a"

-- #exit
#eval cleanseCode code
#eval show MetaM _ from do
  let p := parseProgram (← getEnv) (cleanseCode code)
  match p with
    | Except.ok p =>
      let (c, r) := p.run default
      IO.println r
      IO.println "-------------"
      IO.println c
      IO.println "-------------"
      IO.println p
    | _ => pure ()
  return p
