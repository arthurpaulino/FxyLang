/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import Lean
import FxyLang.Execution
import FxyLang.Syntax

open Lean Elab Meta

def mkApp' (name : Name) (e : Expr) : Expr :=
  mkApp (mkConst name) e

def negFloat (f : Float) : Float :=
  -1.0 * f

def elabLiteral : Syntax → TermElabM Expr
  | `(literal| $n:num) =>
    mkAppM ``Literal.int #[mkApp' ``Int.ofNat (mkNatLit n.toNat)]
  | `(literal| true)  => mkAppM ``Literal.bool #[mkConst ``Bool.true]
  | `(literal| false) => mkAppM ``Literal.bool #[mkConst ``Bool.false]
  | `(literal| $s:str) => mkAppM ``Literal.str #[mkStrLit $ s.isStrLit?.getD ""]
  | `(literal| $[-%$neg]?$f:scientific) => do
      if neg.isNone then
        mkAppM ``Literal.float #[← Term.elabScientificLit f (mkConst ``Float)]
      else
        let f ← Term.elabScientificLit f (mkConst ``Float)
        mkAppM ``Literal.float #[mkApp' ``negFloat f]
  | _ => throwUnsupportedSyntax

def elabStringOfIdent (id : Syntax) : Expr :=
  mkStrLit id.getId.toString

def elabBinOp : Syntax → TermElabM Expr
  | `(binop| +)  => return mkConst ``BinOp.add
  | `(binop| *)  => return mkConst ``BinOp.mul
  | `(binop| <)  => return mkConst ``BinOp.lt
  | `(binop| <=) => return mkConst ``BinOp.le
  | `(binop| >)  => return mkConst ``BinOp.gt
  | `(binop| >=) => return mkConst ``BinOp.ge
  | `(binop| =)  => return mkConst ``BinOp.eq
  | `(binop| !=) => return mkConst ``BinOp.ne
  | _ => throwUnsupportedSyntax

partial def elabExpression : Syntax → TermElabM Expr
  | `(expression| $v:literal) => do mkAppM ``Expression.lit #[← elabLiteral v]
  | `(expression| $n:ident) => mkAppM ``Expression.var #[elabStringOfIdent n]
  | `(expression| $e:expression $[$es:expression]*) => do
    match ← es.data.mapM elabExpression with
    | []      => unreachable!
    | e' :: es =>
      let l  ← mkListLit (Lean.mkConst ``Expression) es
      let nl ← mkAppM ``List.toNEList #[e', l]
      mkAppM ``Expression.app #[← elabExpression e, nl]
  | `(expression| ! $p:expression) => do
    mkAppM ``Expression.unOp #[mkConst ``UnOp.not, ← elabExpression p]
  | `(expression| $eₗ:expression $o:binop $eᵣ:expression) => do
    mkAppM ``Expression.binOp
      #[← elabBinOp o, ← elabExpression eₗ, ← elabExpression eᵣ]
  | `(expression| [$ls:literal,*]) => do
    let l ← ls.getElems.data.mapM elabLiteral
    mkAppM ``Expression.list #[← mkListLit (Lean.mkConst ``_root_.Literal) l]
  | `(expression| ($e:expression)) => elabExpression e
  | _ => throwUnsupportedSyntax

partial def elabProgram : Syntax → TermElabM Expr
  | `(program| skip)  => return mkConst ``Program.skip
  | `(program| $e:expression) => do
    mkAppM ``Program.eval #[← elabExpression e]
  | `(programSeq| $p:program $[$ps:program]*) => do
    ps.foldlM (init := ← elabProgram p) fun a b => do
      mkAppM ``Program.seq #[a, ← elabProgram b]
  | `(program| $n:ident $ns:ident* := $p:programSeq) => do
    let ns := ns.data
    if ¬ ((ns.map fun n => n.getId.toString).noDup) then
      throwError s!"definition of curried function {n.getId.toString} has " ++
        "duplicated variables"
    let ns := ns.map elabStringOfIdent -- each element represents a String
    match ns with
    | [] => mkAppM ``Program.decl #[elabStringOfIdent n, ← elabProgram p]
    | n' :: ns =>
      let l  ← mkListLit (Lean.mkConst ``String) ns     -- List String
      let nl ← mkAppM ``List.toNEList #[n', l]          -- NEList String
      let h  ← mkEqRefl (← mkAppM ``NEList.noDup #[nl]) -- proof of noDup
      mkAppM ``Program.decl #[
        elabStringOfIdent n,
        mkApp' ``Program.eval $
          mkApp' ``Expression.lam $
            ← mkAppM ``Lambda.mk #[nl, h, ← elabProgram p]
      ]
  | `(program| if $e:expression then $p:programSeq $[else $q:programSeq]?) => do
    let q ← match q with
    | none   => pure $ mkConst ``Program.skip
    | some q => elabProgram q
    mkAppM ``Program.fork
      #[← elabExpression e, ← elabProgram p, q]
  | `(program| while $e:expression do $p:programSeq) => do
    mkAppM ``Program.loop #[← elabExpression e, ← elabProgram p]
  | `(program| !print $e:expression) => do
      return mkApp' ``Program.print (← elabExpression e)
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
a := 1 + 1
[1, 2, 3, 1.3, "oi"] + 3
<<.run

#eval >>
f x y z := x + y + z
q := f 3 4
q 5
x := 1
<<.run

#eval >>
f x y z := x + y + z
f 3 4 5
<<.run

#eval >>
f x y z := x + y + z
(f 3 4) 5
<<.run

#eval >>
a x := x
b x := 2 * x
(b 1) > (a 1)
<<.run

#eval >>
a := 0
while a < 5 do
  a := a + 1
<<.run

#eval >>
if 1 < 0 then
  a := 1
else
  a := 4
<<.run

#eval >>
if true * false then
  a := 1
else
  a := 4
<<.run

#eval >>
if true * (false) then
  a := 1
else
  a := 4
<<

#eval >>
if (true * (false)) then
  a := 1
else
  a := 4
<<

#eval >>
x x := x
x 4
<<.run

#eval >>
g x y := x + y
f x :=
  a := 1
  b := 2
  c := g a b -- uncomment this line to see the bug
  x

q := f 3
q
<<.run

#eval >>
f n :=
  s := 0
  i := 0
  while i < n do
    i := i + 1
    s := s + i
  s
x := f 5
x
<<.run

def px := >>
x := 1
 a := 2
<<.toString

def px' := >>
x := 1
a := 2
<<.toString

def px'' := >>
x := 1
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
  a := a + 1
    s := s + a
    x := 1
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
min x y :=
  if x < y
    then x
    else y
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
while 1 < a do x := 2
a < 3
<<.toString

#assert p3 = p4
#assert p4 = p5

def p6 := >>
f x y :=
  x + y
f3 := f 3
f32 := f3 2
<<.toString

def p6' := >>
f x y := x + y
 f3 := f 3
f32 := f3 2
<<.toString

def p7 := >>
f x y := x + y
  f3 := f 3
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
a :=
  x := 5
  y = 5
2 + 5
<<.toString

def p10 := >>
a :=
  x := 5
   y = 5
2 + 5
<<.toString

def p11 := >>
a :=
    x := 5
    y = 5
2 + 5
<<.toString

#assert p9 = p9'
#assert p9 = p10
#assert p10 = p11
