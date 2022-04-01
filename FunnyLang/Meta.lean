/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import Lean
import FunnyLang.AST
import FunnyLang.Syntax

open Lean Elab Meta

def mkApp' (name : Name) (e : Expr) : Expr :=
  mkApp (mkConst name) e

def elabValue : Syntax → TermElabM Expr
  | `(value|$n:numLit) =>
    mkAppM ``Value.int #[mkApp' `Int.ofNat (mkNatLit n.toNat)]
  | _ => throwUnsupportedSyntax

def elabStringOfIdent (id : Syntax) : Expr :=
  mkStrLit id.getId.toString

partial def elabExpression : Syntax → TermElabM Expr
  | `(expression| $v:value) => do mkAppM ``Expression.atom #[← elabValue v]
  | `(expression| ! $e:expression) => do
    mkAppM ``Expression.not #[← elabExpression e]
  | `(expression| $n:ident $[$es:expression]*) => do
    let es ← es.data.mapM elabExpression
    if h : ¬ es.isEmpty then
      let l ← mkListLit (mkConst ``Expression) es -- term of type `List Expression`
      mkAppM ``Expression.app #[elabStringOfIdent n, l]
    else mkAppM ``Expression.var #[elabStringOfIdent n]
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
  | `(program| $p:program; $q:program) => do
    mkAppM ``Program.sequence #[← elabProgram p, ← elabProgram q]
  | `(program| $n:ident $ns:ident* := $p:program) => do
    let ns := ns.data.map elabStringOfIdent
    if h : ¬ ns.isEmpty then
      let l ← mkListLit (mkConst ``String) ns -- term of type `List String`
      mkAppM ``Program.attribution #[
        elabStringOfIdent n,
        mkApp' ``Program.evaluation $
          mkApp' ``Expression.atom $
            ← mkAppM ``Value.curry #[l, ← elabProgram p]
      ]
      else mkAppM ``Program.attribution #[elabStringOfIdent n, ← elabProgram p]
  | `(program| if $e:expression then $p:program else $q:program) => do
    mkAppM ``Program.ifElse
      #[← elabExpression e, ← elabProgram p, ← elabProgram q]
  | `(program| while $e:expression do $p:program) => do
    mkAppM ``Program.whileLoop #[← elabExpression e, ← elabProgram p]
  | `(program| $e:expression) => do
    mkAppM ``Program.evaluation #[← elabExpression e]
  | `(program| ($p:program)) => elabProgram p
  | _ => throwUnsupportedSyntax

elab ">>" ppLine p:program ppLine "<<" : term => elabProgram p

#eval >> f x y := 0 <<.run
#eval >> f 1 1 <<.run
