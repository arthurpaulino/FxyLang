/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import Lean
import FunnyLang.AST
-- import FunnyLang.Syntax

declare_syntax_cat                            value
syntax ("-" noWs)? num                      : value
syntax str                                  : value
syntax "true"                               : value
syntax "false"                              : value
syntax ("-" noWs)? num noWs "." (noWs num)? : value
syntax withPosition("[ " colGt value* " ]") : value
syntax "nil"                                : value

declare_syntax_cat                    expression
syntax value                        : expression
syntax " ! " expression             : expression
syntax expression " + "  expression : expression
syntax expression " * "  expression : expression
syntax expression " = "  expression : expression
syntax expression " != " expression : expression
syntax expression " < "  expression : expression
syntax expression " <= " expression : expression
syntax expression " > "  expression : expression
syntax expression " >= " expression : expression
syntax ident expression*            : expression
syntax "( " expression " )"         : expression

declare_syntax_cat                                           program
syntax "skip"                                              : program
syntax:25 program program                                  : program
syntax withPosition(ident+ " := " colGt program:75)        : program
syntax expression                                          : program
syntax withPosition("if" expression (colGt "then"
  program) "else" (colGt program))                         : program
syntax withPosition("while" expression "do" colGt program) : program
syntax " ( " program " ) "                                 : program

open Lean Elab Meta

def mkApp' (name : Name) (e : Expr) : Expr :=
  mkApp (mkConst name) e

def elabValue : Syntax → TermElabM Expr
  | `(value|$n:numLit) =>
    mkAppM ``Value.int #[mkApp' ``Int.ofNat (mkNatLit n.toNat)]
  | _ => throwUnsupportedSyntax

def elabStringOfIdent (id : Syntax) : Expr :=
  mkStrLit id.getId.toString

partial def elabExpression : Syntax → TermElabM Expr
  | `(expression| $v:value) => do mkAppM ``Expression.atom #[← elabValue v]
  | `(expression| ! $e:expression) => do
    mkAppM ``Expression.not #[← elabExpression e]
  | `(expression| $n:ident $[$es:expression]*) => do
    let es ← es.data.mapM elabExpression
    match es with
    | []      => mkAppM ``Expression.var #[elabStringOfIdent n]
    | e :: es =>
      let l  ← mkListLit (Lean.mkConst ``Expression) es
      let nl ← mkAppM ``List.toNEList #[e, l]
      mkAppM ``Expression.app #[elabStringOfIdent n, nl]
  | `(expression| $l:expression + $r:expression) => do
    mkAppM ``Expression.add #[← elabExpression l, ← elabExpression r]
  | `(expression| $l:expression * $r:expression) => do
    mkAppM ``Expression.mul #[← elabExpression l, ← elabExpression r]
  | `(expression| $l:expression = $r:expression) => do
    mkAppM ``Expression.eq #[← elabExpression l, ← elabExpression r]
  | `(expression| $l:expression != $r:expression) => do
    mkAppM ``Expression.ne #[← elabExpression l, ← elabExpression r]
  | `(expression| $l:expression < $r:expression) => do
    mkAppM ``Expression.lt #[← elabExpression l, ← elabExpression r]
  | `(expression| $l:expression <= $r:expression) => do
    mkAppM ``Expression.le #[← elabExpression l, ← elabExpression r]
  | `(expression| $l:expression > $r:expression) => do
    mkAppM ``Expression.gt #[← elabExpression l, ← elabExpression r]
  | `(expression| $l:expression >= $r:expression) => do
    mkAppM ``Expression.ge #[← elabExpression l, ← elabExpression r]
  | `(expression| ($e:expression)) => elabExpression e
  | _ => throwUnsupportedSyntax

partial def elabProgram : Syntax → TermElabM Expr
  | `(program| skip) => return mkConst ``Program.skip
  | `(program| $p:program $q:program) => do
    mkAppM ``Program.sequence #[← elabProgram p, ← elabProgram q]
  | `(program| $n:ident $ns:ident* := $p:program) => do
    match ns.data.map elabStringOfIdent with
    | []      =>
      mkAppM ``Program.attribution #[elabStringOfIdent n, ← elabProgram p]
    | n' :: ns =>
      let l  ← mkListLit (Lean.mkConst ``String) ns
      let nl ← mkAppM ``List.toNEList #[n', l]
      mkAppM ``Program.attribution #[
        elabStringOfIdent n,
        mkApp' ``Program.evaluation $
          mkApp' ``Expression.atom $
            ← mkAppM ``Value.curry #[nl, ← elabProgram p]
      ]
  | `(program| if $e:expression then $p:program else $q:program) => do
    mkAppM ``Program.ifElse
      #[← elabExpression e, ← elabProgram p, ← elabProgram q]
  | `(program| while $e:expression do $p:program) => do
    mkAppM ``Program.whileLoop #[← elabExpression e, ← elabProgram p]
  | `(program| $e:expression) => do
    mkAppM ``Program.evaluation #[← elabExpression e]
  | `(program| ($p:program)) => elabProgram p
  | _ => throwUnsupportedSyntax

------- ↓↓ testing area ↓↓

elab ">>" ppLine p:program ppLine "<<" : term => elabProgram p

open Lean.Elab.Command Lean.Elab.Term in
elab "#assert " x:term:60 " = " y:term:60 : command =>
  liftTermElabM `assert do
    let x ← elabTerm x none
    let y ← elabTerm y none
    synthesizeSyntheticMVarsNoPostponing
    unless (← isDefEq x y) do
      throwError "{← reduce x}\n------------------------\n{← reduce y}"

def p1 := >>
min x y :=
  if x < y
    then x
    else y
min 5 3
<<.toString

def p2 := >>
(min x y :=
  if x < y
    then x
    else y)
min 5 3
<<.toString

#assert p1 = p2

def p3 := >>
while 1 < a do
  x := 2
a < 3
<<.toString

def p4 := >>
while 1 < a do x := 2
a < 3
<<.toString

def p5 := >>
(while 1 < a do x := 2)
a < 3
<<.toString

#assert p3 = p4
#assert p4 = p5

def p6 := >>
(f x y :=
  x + y)
(f3 := f 3)
f32 := f3 2
<<.toString

def p7 := >>
(f x y := x + y)
(f3 := f 3)
f32 := f3 2
<<.toString

#assert p6 = p7

def p8 := >>
f x y := x + y
f3 := f 3
f32 := f3 2
<<.toString

#assert p7 = p8


def p9 := >>
a :=
  x := 5
  y = 5
2 + 5
<<.toString

def p9' := >>
(a :=
  x := 5
  y = 5)
2 + 5
<<.toString

def p10 := >>
a :=
  (x := 5
  y = 5)
2 + 5
<<.toString

def p11 := >>
(a :=
  ((x := 5)
  y = 5))
2 + 5
<<.toString

#assert p9 = p9'
#assert p9 = p10
#assert p10 = p11
