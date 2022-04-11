/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import FxyLang.AST

def Literal.typeStr : Literal → String
  | bool  _ => "bool"
  | int   _ => "int"
  | float _ => "float"
  | str   _ => "str"
  | inv     => "invalid type"

protected def Literal.toString : Literal → String
  | bool  b => toString b
  | int   i => toString i
  | float f => toString f
  | str   s => s
  | inv     => "«invalid»"

def Lambda.toString (l : Lambda) : String :=
  "«function»"

protected def Value.toString : Value → String
  | nil     => "«nil»"
  | lit  l  => l.toString
  | list l  => toString $ l.map Literal.toString
  | lam  l  => l.toString
  | error s => s!"error: {s}"

def Lambda.typeStr : Lambda → String
  | mk l .. => (l.foldl (init := "") fun acc _ => acc ++ "_ → ") ++ "thunk"

def Value.typeStr : Value → String
  | nil     => "nil"
  | lit   l => l.typeStr
  | error _ => "error"
  | list  _ => "list"
  | lam   l => l.typeStr

mutual

  partial def unfoldExpressions (es : NEList Expression) : String :=
    (es.map fun e => Expression.toString e).unfoldStrings

  protected partial def Expression.toString : Expression → String
    | var  n    => n
    | lit  l    => l.toString
    | list l    => toString $ l.map Literal.toString
    | lam  l    => l.toString
    | app  n es => s!"({n} {unfoldExpressions es})"

end

instance : ToString Expression := ⟨Expression.toString⟩
instance : ToString Value      := ⟨Value.toString⟩

def Literal.add : Literal → Literal → Literal
  | bool  bₗ, bool  bᵣ => bool  $ bₗ || bᵣ
  | int   iₗ, int   iᵣ => int   $ iₗ +  iᵣ
  | float fₗ, float fᵣ => float $ fₗ +  fᵣ
  | int   iₗ, float fᵣ => float $ (.ofInt iₗ) +  fᵣ
  | float fₗ, int   iᵣ => float $ fₗ +  (.ofInt iᵣ)
  | str   sₗ, str   sᵣ => str   $ sₗ ++ sᵣ
  | l       , r        => inv

def Literal.mul : Literal → Literal → Literal
  | bool  bₗ, bool  bᵣ => bool  $ bₗ && bᵣ
  | int   iₗ, int   iᵣ => int   $ iₗ *  iᵣ
  | float fₗ, float fᵣ => float $ fₗ *  fᵣ
  | int   iₗ, float fᵣ => float $ (.ofInt iₗ) *  fᵣ
  | float fₗ, int   iᵣ => float $ fₗ *  (.ofInt iᵣ)
  | l       , r        => inv

def Bool.toNat : Bool → Nat
  | false => 0
  | true  => 1

def Literal.lt : Literal → Literal → Literal
  | bool  bₗ, bool  bᵣ => bool $ bₗ.toNat < bᵣ.toNat
  | int   iₗ, int   iᵣ => bool $ iₗ < iᵣ
  | float fₗ, float fᵣ => bool $ fₗ < fᵣ
  | int   iₗ, float fᵣ => bool $ (.ofInt iₗ) < fᵣ
  | float fₗ, int   iᵣ => bool $ fₗ < (.ofInt iᵣ)
  | str   sₗ, str   sᵣ => bool $ sₗ < sᵣ
  | _       , _        => inv

def Literal.le : Literal → Literal → Literal
  | bool  bₗ, bool  bᵣ => bool $ bₗ.toNat ≤ bᵣ.toNat
  | int   iₗ, int   iᵣ => bool $ iₗ ≤ iᵣ
  | float fₗ, float fᵣ => bool $ fₗ ≤ fᵣ
  | int   iₗ, float fᵣ => bool $ (.ofInt iₗ) ≤ fᵣ
  | float fₗ, int   iᵣ => bool $ fₗ ≤ (.ofInt iᵣ)
  | str   sₗ, str   sᵣ => bool $ sₗ < sᵣ || sₗ == sᵣ 
  | _       , _        => inv

def Literal.gt : Literal → Literal → Literal
  | bool  bₗ, bool  bᵣ => bool $ bₗ.toNat > bᵣ.toNat
  | int   iₗ, int   iᵣ => bool $ iₗ > iᵣ
  | float fₗ, float fᵣ => bool $ fₗ > fᵣ
  | int   iₗ, float fᵣ => bool $ (.ofInt iₗ) > fᵣ
  | float fₗ, int   iᵣ => bool $ fₗ > (.ofInt iᵣ)
  | str   sₗ, str   sᵣ => bool $ sₗ > sᵣ
  | _       , _        => inv

def Literal.ge : Literal → Literal → Literal
  | bool  bₗ, bool  bᵣ => bool $ bₗ.toNat ≥ bᵣ.toNat
  | int   iₗ, int   iᵣ => bool $ iₗ ≥ iᵣ
  | float fₗ, float fᵣ => bool $ fₗ ≥ fᵣ
  | int   iₗ, float fᵣ => bool $ (.ofInt iₗ) ≥ fᵣ
  | float fₗ, int   iᵣ => bool $ fₗ ≥ (.ofInt iᵣ)
  | str   sₗ, str   sᵣ => bool $ sₗ > sᵣ || sₗ == sᵣ
  | _       , _        => inv

def Literal.eq : Literal → Literal → Literal
  | bool  bₗ, bool  bᵣ => bool $ bₗ.toNat == bᵣ.toNat
  | int   iₗ, int   iᵣ => bool $ iₗ == iᵣ
  | float fₗ, float fᵣ => bool $ fₗ == fᵣ
  | int   iₗ, float fᵣ => bool $ (.ofInt iₗ) == fᵣ
  | float fₗ, int   iᵣ => bool $ fₗ == (.ofInt iᵣ)
  | str   sₗ, str   sᵣ => bool $ sₗ == sᵣ
  | _       , _        => bool false

def Literal.isEq (l r : Literal) : Bool :=
  match h : l.eq r with
  | .bool b => b
  | x       => unreachable! --todo: eliminate this option with some proof

def listLiteralEq : List Literal → List Literal → Bool
  | [], [] => true
  | a :: a' :: as, b :: b' :: bs =>
    a.isEq b && listLiteralEq (a' :: as) (b' :: bs)
  | _, _   => false

def appError (app l r : String) : String :=
  s!"invalid application of '{app}' between '{l}' and '{r}'"

def appError' (app v : String) : String :=
  s!"invalid application of '{app}' on '{v}'"

def Value.not : Value → Value
  | er@(error _)  => er
  | lit $ .bool b => lit $ .bool !b
  | v             => error $ appError' "!" v.typeStr

def Value.add : Value → Value → Value
  | er@(error _),  _        => er
  | _      ,  er@(error _)  => er
  | lit  lₗ, lit lᵣ   => match lₗ.add lᵣ with
    | .inv => error $ appError "+" lₗ.typeStr lᵣ.typeStr
    | l    => lit l
  | list lₗ, list  lᵣ => list  $ lₗ ++ lᵣ
  | list l,  lit r    => list  $ l.concat r
  | l,        r       => error $ appError "+" l.typeStr r.typeStr

def Value.mul : Value → Value → Value
  | error s,  _        => error s
  | _      ,  error s  => error s
  | lit   lₗ, lit lᵣ   => match lₗ.mul lᵣ with
    | .inv => error $ appError "*" lₗ.typeStr lᵣ.typeStr
    | l    => lit l
  | l,        r        => error $ appError "*" l.typeStr r.typeStr

def Value.lt : Value → Value → Value
  | error s,  _       => error s
  | _,        error s => error s
  | lit  lₗ, lit lᵣ   => match lₗ.lt lᵣ with
    | .bool b => lit $ .bool b
    | _       => error $ appError "<" lₗ.typeStr lᵣ.typeStr
  | list lₗ, list  lᵣ => lit $ .bool $ lₗ.length < lᵣ.length
  | l,         r      => error $ appError "<" l.typeStr r.typeStr

def Value.le : Value → Value → Value
  | error s,  _       => error s
  | _,        error s => error s
  | lit  lₗ, lit lᵣ   => match lₗ.le lᵣ with
    | .bool b => lit $ .bool b
    | _       => error $ appError "<=" lₗ.typeStr lᵣ.typeStr
  | list lₗ, list  lᵣ => lit $ .bool $ lₗ.length ≤ lᵣ.length
  | l,         r      => error $ appError "<=" l.typeStr r.typeStr

def Value.gt : Value → Value → Value
  | error s,  _       => error s
  | _,        error s => error s
  | lit  lₗ, lit lᵣ   => match lₗ.gt lᵣ with
    | .bool b => lit $ .bool b
    | _       => error $ appError ">" lₗ.typeStr lᵣ.typeStr
  | list lₗ, list  lᵣ => lit $ .bool $ lₗ.length > lᵣ.length
  | l,         r      => error $ appError ">" l.typeStr r.typeStr

def Value.ge : Value → Value → Value
  | error s,  _       => error s
  | _,        error s => error s
  | lit  lₗ, lit lᵣ   => match lₗ.ge lᵣ with
    | .bool b => lit $ .bool b
    | _       => error $ appError ">=" lₗ.typeStr lᵣ.typeStr
  | list lₗ, list  lᵣ => lit $ .bool $ lₗ.length ≥ lᵣ.length
  | l,         r      => error $ appError ">=" l.typeStr r.typeStr

def Value.eq : Value → Value → Value
  | error s, _        => error s
  | _,       error s  => error s
  | nil,     nil      => lit $ .bool true
  | lit  lₗ, lit lᵣ   => match lₗ.eq lᵣ with
    | .bool b => lit $ .bool b
    | _       => unreachable! --todo: eliminate this option with some proof
  | list lₗ, list  lᵣ => lit $ .bool (listLiteralEq lₗ lᵣ)
  | lam .. , lam ..   => error "can't compare functions" --todo
  | _,       _        => lit $ .bool false

def Value.ne : Value → Value → Value
  | error s, _        => error s
  | _,       error s  => error s
  | nil,     nil      => lit $ .bool false
  | lit  lₗ, lit lᵣ   => match lₗ.eq lᵣ with
    | .bool b => lit $ .bool !b
    | _       => unreachable! --todo: eliminate this option with some proof
  | list lₗ, list  lᵣ => lit $ .bool !(listLiteralEq lₗ lᵣ)
  | lam ..,  lam ..   => error "can't compare functions" -- todo
  | _,       _        => lit $ .bool false

def Value.unOp : Value → UnOp → Value
  | v, .not => v.not

def Value.binOp : Value → Value → BinOp → Value
  | l, r, .add => l.add r
  | l, r, .mul => l.mul r
  | l, r, .lt  => l.lt r
  | l, r, .le  => l.le r
  | l, r, .gt  => l.gt r
  | l, r, .ge  => l.ge r
  | l, r, .eq  => l.eq r
  | l, r, .ne  => l.ne r

def Value.toProgram : Value → Program
  | nil     => .skip
  | lit   l => .eval $ .lit l
  | list  l => .eval $ .list l
  | error m => .fail m
  | lam   l => .eval $ .lam l

def Program.getCurryNames? : Program → Option (NEList String)
  | eval (.app _ ns )                  => none
  | seq (decl _ (eval (.app _ ns ))) _ => none
  | _                                  => none

def Program.isSequence : Program → Bool
  | seq .. => true
  | _      => false

def blank (n : Nat) : String :=
  let rec blankAux (cs : List Char) : Nat → List Char
    | 0     => cs
    | n + 1 => ' ' :: ' ' :: (blankAux cs n)
  ⟨blankAux [] n⟩

def Program.toString (p : Program) : String :=
  let rec aux (l : Nat) : Program → String
    | skip              => s!"{blank l}skip"
    | seq    p q   =>
      s!"{blank (l-2)}{aux l p}\n{aux l q}"
    | decl n p   =>
      let pString := if p.isSequence
        then s!"\n{aux (l+2) p}"
        else s!" {aux (l-2) p}"
      match p.getCurryNames? with
      | none    => s!"{blank l}{n} :=" ++ pString
      | some ns => s!"{blank l}{n} {ns.unfoldStrings} :=" ++ pString
    | eval  e     => s!"{blank l}{e}"
    | loop  p? p   =>
      s!"{blank l}while {p?.toString} do\n{aux (l+2) p}"
    | fork      p? p q =>
      s!"{blank l}if {p?.toString} then\n{aux (l+2) p}\n" ++
        s!"else\n{aux (l+2) q}"
    | fail s          => s!"raise {s}"
    | .unOp .not p    => s!"(! {aux 0 p})"
    | .binOp .add l r => s!"({aux 0 l} + {aux 0 r})"
    | .binOp .mul l r => s!"({aux 0 l} * {aux 0 r})"
    | .binOp .eq  l r => s!"({aux 0 l} = {aux 0 r})"
    | .binOp .ne  l r => s!"({aux 0 l} != {aux 0 r})"
    | .binOp .lt  l r => s!"({aux 0 l} < {aux 0 r})"
    | .binOp .le  l r => s!"({aux 0 l} <= {aux 0 r})"
    | .binOp .gt  l r => s!"({aux 0 l} > {aux 0 r})"
    | .binOp .ge  l r => s!"({aux 0 l} >= {aux 0 r})"
  aux 0 p