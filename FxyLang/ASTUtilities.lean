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

protected def Literal.toString : Literal → String
  | bool  b => toString b
  | int   i => toString i
  | float f => toString f
  | str   s => s

def Lambda.toString (l : Lambda) : String :=
  "«function»"

protected def Value.toString : Value → String
  | nil     => "«nil»"
  | lit  l  => l.toString
  | list l  => toString $ l.map Literal.toString
  | lam  l  => l.toString

def Lambda.typeStr : Lambda → String
  | mk l .. => (l.foldl (init := "") fun acc _ => acc ++ "_ → ") ++ "_"

def Value.typeStr : Value → String
  | nil     => "nil"
  | lit   l => l.typeStr
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
    | .unOp  .not p   =>s!"(! {Expression.toString p})"
    | .binOp .add l r =>s!"({Expression.toString l} + {Expression.toString r})"
    | .binOp .mul l r =>s!"({Expression.toString l} * {Expression.toString r})"
    | .binOp .eq  l r =>s!"({Expression.toString l} = {Expression.toString r})"
    | .binOp .ne  l r =>s!"({Expression.toString l} != {Expression.toString r})"
    | .binOp .lt  l r =>s!"({Expression.toString l} < {Expression.toString r})"
    | .binOp .le  l r =>s!"({Expression.toString l} <= {Expression.toString r})"
    | .binOp .gt  l r =>s!"({Expression.toString l} > {Expression.toString r})"
    | .binOp .ge  l r =>s!"({Expression.toString l} >= {Expression.toString r})"

end

instance : ToString Expression := ⟨Expression.toString⟩
instance : ToString Value      := ⟨Value.toString⟩

def Literal.eq : Literal → Literal → Bool
  | bool  bₗ, bool  bᵣ => bₗ == bᵣ
  | int   iₗ, int   iᵣ => iₗ == iᵣ
  | float fₗ, float fᵣ => fₗ == fᵣ
  | int   iₗ, float fᵣ => (.ofInt iₗ) == fᵣ
  | float fₗ, int   iᵣ => fₗ == (.ofInt iᵣ)
  | str   sₗ, str   sᵣ => sₗ == sᵣ
  | _       , _        => false

def listLiteralEq : List Literal → List Literal → Bool
  | [], [] => true
  | a :: a' :: as, b :: b' :: bs =>
    a.eq b && listLiteralEq (a' :: as) (b' :: bs)
  | _, _   => false

def appError (app l r : String) : String :=
  s!"invalid application of '{app}' between '{l}' and '{r}'"

def appError' (app v : String) : String :=
  s!"invalid application of '{app}' on '{v}'"

def Value.not : Value → Except String Value
  | lit $ .bool b => pure $ lit $ .bool !b
  | v             => throw $ appError' "!" v.typeStr

def Value.add : Value → Value → Except String Value
  | lit $ .bool  bₗ, lit $ .bool  bᵣ => return lit $ .bool $ bₗ || bᵣ
  | lit $ .int   iₗ, lit $ .int   iᵣ => return lit $ .int  $ iₗ +  iᵣ
  | lit $ .float fₗ, lit $ .float fᵣ => return lit $ .float $ fₗ +  fᵣ
  | lit $ .int   iₗ, lit $ .float fᵣ => return lit $ .float $ (.ofInt iₗ) +  fᵣ
  | lit $ .float fₗ, lit $ .int   iᵣ => return lit $ .float $ fₗ +  (.ofInt iᵣ)
  | lit $ .str   sₗ, lit $ .str   sᵣ => return lit $ .str   $ sₗ ++ sᵣ
  | list         lₗ, list         lᵣ => return list  $ lₗ ++ lᵣ
  | list         l,  lit          r  => return list  $ l.concat r
  | l,               r               => throw $ appError "+" l.typeStr r.typeStr

def Value.mul : Value → Value → Except String Value
  | lit $ .bool  bₗ, lit $ .bool  bᵣ => return .lit $ .bool  $ bₗ && bᵣ
  | lit $ .int   iₗ, lit $ .int   iᵣ => return .lit $ .int   $ iₗ *  iᵣ
  | lit $ .float fₗ, lit $ .float fᵣ => return .lit $ .float $ fₗ *  fᵣ
  | lit $ .int   iₗ, lit $ .float fᵣ => return .lit $ .float $ (.ofInt iₗ) *  fᵣ
  | lit $ .float fₗ, lit $ .int   iᵣ => return .lit $ .float $ fₗ *  (.ofInt iᵣ)
  | l,               r               => throw $ appError "*" l.typeStr r.typeStr

def Bool.toNat : Bool → Nat
  | false => 0
  | true  => 1

def Value.lt : Value → Value → Except String Value
  | lit $ .bool  bₗ, lit $ .bool  bᵣ => return lit $ .bool $ bₗ.toNat < bᵣ.toNat
  | lit $ .int   iₗ, lit $ .int   iᵣ => return lit $ .bool $ iₗ < iᵣ
  | lit $ .float fₗ, lit $ .float fᵣ => return lit $ .bool $ fₗ < fᵣ
  | lit $ .int   iₗ, lit $ .float fᵣ => return lit $ .bool $ (.ofInt iₗ) < fᵣ
  | lit $ .float fₗ, lit $ .int   iᵣ => return lit $ .bool $ fₗ < (.ofInt iᵣ)
  | lit $ .str   sₗ, lit $ .str   sᵣ => return lit $ .bool $ sₗ < sᵣ
  | list lₗ, list lᵣ => return lit $ .bool $ lₗ.length < lᵣ.length
  | l,               r               => throw $ appError "<" l.typeStr r.typeStr

def Value.le : Value → Value → Except String Value
  | lit $ .bool  bₗ, lit $ .bool  bᵣ => return lit $ .bool $ bₗ.toNat ≤ bᵣ.toNat
  | lit $ .int   iₗ, lit $ .int   iᵣ => return lit $ .bool $ iₗ ≤ iᵣ
  | lit $ .float fₗ, lit $ .float fᵣ => return lit $ .bool $ fₗ ≤ fᵣ
  | lit $ .int   iₗ, lit $ .float fᵣ => return lit $ .bool $ (.ofInt iₗ) ≤ fᵣ
  | lit $ .float fₗ, lit $ .int   iᵣ => return lit $ .bool $ fₗ ≤ (.ofInt iᵣ)
  | lit $ .str   sₗ, lit $ .str   sᵣ => return lit $ .bool $ sₗ < sᵣ || sₗ == sᵣ
  | list lₗ, list  lᵣ => return lit $ .bool $ lₗ.length ≤ lᵣ.length
  | l,         r      => throw $ appError "<=" l.typeStr r.typeStr

def Value.gt : Value → Value → Except String Value
  | lit $ .bool  bₗ, lit $ .bool  bᵣ => return lit $ .bool $ bₗ.toNat > bᵣ.toNat
  | lit $ .int   iₗ, lit $ .int   iᵣ => return lit $ .bool $ iₗ > iᵣ
  | lit $ .float fₗ, lit $ .float fᵣ => return lit $ .bool $ fₗ > fᵣ
  | lit $ .int   iₗ, lit $ .float fᵣ => return lit $ .bool $ (.ofInt iₗ) > fᵣ
  | lit $ .float fₗ, lit $ .int   iᵣ => return lit $ .bool $ fₗ > (.ofInt iᵣ)
  | lit $ .str   sₗ, lit $ .str   sᵣ => return lit $ .bool $ sₗ > sᵣ
  | list lₗ, list lᵣ => return lit $ .bool $ lₗ.length > lᵣ.length
  | l,       r       => throw $ appError ">" l.typeStr r.typeStr

def Value.ge : Value → Value → Except String Value
  | lit $ .bool  bₗ, lit $ .bool  bᵣ => return lit $ .bool $ bₗ.toNat ≥ bᵣ.toNat
  | lit $ .int   iₗ, lit $ .int   iᵣ => return lit $ .bool $ iₗ ≥ iᵣ
  | lit $ .float fₗ, lit $ .float fᵣ => return lit $ .bool $ fₗ ≥ fᵣ
  | lit $ .int   iₗ, lit $ .float fᵣ => return lit $ .bool $ (.ofInt iₗ) ≥ fᵣ
  | lit $ .float fₗ, lit $ .int   iᵣ => return lit $ .bool $ fₗ ≥ (.ofInt iᵣ)
  | lit $ .str   sₗ, lit $ .str   sᵣ => return lit $ .bool $ sₗ > sᵣ || sₗ == sᵣ
  | list lₗ, list  lᵣ => return lit $ .bool $ lₗ.length ≥ lᵣ.length
  | l,       r        => throw $ appError ">=" l.typeStr r.typeStr

def Value.eq : Value → Value → Except String Value
  | nil,     nil      => return lit $ .bool true
  | lit  lₗ, lit lᵣ   => return lit $ .bool $ lₗ.eq lᵣ
  | list lₗ, list  lᵣ => return lit $ .bool (listLiteralEq lₗ lᵣ)
  | lam .. , lam ..   => throw "can't compare functions" --todo
  | _,       _        => return lit $ .bool false

def Value.ne : Value → Value → Except String Value
  | nil,     nil      => return lit $ .bool false
  | lit  lₗ, lit lᵣ   => return lit $ .bool $ !(lₗ.eq lᵣ)
  | list lₗ, list  lᵣ => return lit $ .bool !(listLiteralEq lₗ lᵣ)
  | lam ..,  lam ..   => throw "can't compare functions" -- todo
  | _,       _        => return lit $ .bool true

def Value.unOp : Value → UnOp → Except String Value
  | v, .not => v.not

def Value.binOp : Value → Value → BinOp → Except String Value
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
  aux 0 p

instance : ToString Program := ⟨Program.toString⟩
