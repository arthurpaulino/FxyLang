/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import Lean
import FxyLang.AST
import FxyLang.Syntax

open Lean Elab Meta

def mkApp' (name : Name) (e : Expr) : Expr :=
  mkApp (mkConst name) e

def elabValue : Syntax → TermElabM Expr
  | `(value|$n:num) =>
    mkAppM ``Value.int #[mkApp' ``Int.ofNat (mkNatLit n.toNat)]
  | _ => throwUnsupportedSyntax

def elabStringOfIdent (id : Syntax) : Expr :=
  mkStrLit id.getId.toString

partial def elabExpression : Syntax → TermElabM Expr
  | `(expression| $v:value) => do mkAppM ``Expression.atom #[← elabValue v]
  | `(expression| ! $e:expression) => do
    mkAppM ``Expression.not #[← elabExpression e]
  | `(expression| $n:ident) => mkAppM ``Expression.var #[elabStringOfIdent n]
  | `(expression| $n:ident $[$es:expression]*) => do
    match ← es.data.mapM elabExpression with
    | []      => unreachable!
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
  | `(program| skip)  => return mkConst ``Program.skip
  | `(program| break) => return mkApp' ``Program.halt $ mkConst ``Halting.brk
  | `(programSeq| $p:program $[$ps:program]*) => do
    ps.foldlM (init := ← elabProgram p) fun a b => do
      mkAppM ``Program.sequence #[a, ← elabProgram b]
  | `(program| $n:ident $ns:ident* := $p:programSeq) => do
    match ns.data.map elabStringOfIdent with
    | [] => mkAppM ``Program.attribution #[elabStringOfIdent n, ← elabProgram p]
    | n' :: ns =>
      let l  ← mkListLit (Lean.mkConst ``String) ns
      let nl ← mkAppM ``List.toNEList #[n', l]
      mkAppM ``Program.attribution #[
        elabStringOfIdent n,
        mkApp' ``Program.evaluation $
          mkApp' ``Expression.atom $
            ← mkAppM ``Value.curry #[nl, ← elabProgram p]
      ]
  | `(program| if $e:expression then $p:programSeq $[else $q:programSeq]?) => do
    let q ← match q with
    | none => pure $ mkConst ``Program.skip
    | some q => elabProgram q
    mkAppM ``Program.ifElse
      #[← elabExpression e, ← elabProgram p, q]
  | `(program| while $e:expression do $p:programSeq) => do
    mkAppM ``Program.whileLoop #[← elabExpression e, ← elabProgram p]
  | `(program| $e:expression) => do
    mkAppM ``Program.evaluation #[← elabExpression e]
  | `(program| ($p:programSeq)) => elabProgram p
  | _ => throwUnsupportedSyntax

------- ↓↓ testing area ↓↓

elab ">>" ppLine p:programSeq ppLine "<<" : term => elabProgram p

open Lean.Elab.Command Lean.Elab.Term in
elab "#assert " x:term:60 " = " y:term:60 : command =>
  liftTermElabM `assert do
    let x ← elabTerm x none
    let y ← elabTerm y none
    synthesizeSyntheticMVarsNoPostponing
    unless (← isDefEq x y) do
      throwError "{← reduce x}\n------------------------\n{← reduce y}"

#eval >>
a := 0
while a < 10 do
  a := a + 1
  if a = 2 then break
break
<<.run!

#eval >>
a := break
<<.run!

#eval >>
f x :=
  a := 0
  while a = a do
    if a > x + 5 then
      break
    else
      a := a + 1
  a
f 10
<<.run!

def px := >>
((x := 1)
 (a := 2))
<<.toString

def px' := >>
x := 1
a := 2
<<.toString

def px'' := >>
(x := 1)
a := 2
<<.toString

#assert px = px'
#assert px' = px''

def pw := >>
x := 1
s := 0
a := 0
while a < 5 do
  a := a + 1
  s := s + a
  x := 1
s
<<

def pw' := >>
x := 1
s := 0
a := 0
while a < 5 do
  ((a := a + 1
    s := s + a)
    x := 1)
s
<<

#assert pw = pw'

def p1 := >>
min x y :=
  if x < y
    then x
    else y
min 5 3
<<.toString

def p1' := >>
min x y :=
  if x < y then x
  else y
min 5 3
<<.toString

def p1'' := >>
min x y :=
  if x < y
  then x
  else y
min 5 3
<<.toString

def p1''' := >>
min x y :=
  if x < y then
    x
  else
    y
min 5 3
<<.toString

def p2 := >>
(min x y :=
  if x < y
    then x
    else y)
min 5 3
<<.toString

#assert p1 = p1'
#assert p1 = p1''
#assert p1 = p1'''
#assert p1 = p2

def pIf := >>
if a = 5 then
  b := 3
<<

def pIf' := >>
if a = 5 then
  b := 3
else skip
<<

#assert pIf = pIf'

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

def p6' := >>
((f x y := x + y)
 f3 := f 3)
f32 := f3 2
<<.toString

def p7 := >>
(f x y := x + y)
(f3 := f 3)
f32 := f3 2
<<.toString

def p8 := >>
f x y := x + y
f3 := f 3
f32 := f3 2
<<.toString

#assert p6 = p6'
#assert p6 = p7
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
