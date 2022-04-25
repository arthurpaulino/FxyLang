/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import FxyLang.Implementation.AST

def Literal.typeStr : Literal → String
  | bool  _ => "bool"
  | int   _ => "int"
  | float _ => "float"
  | str   _ => "str"

def removeRightmostZeros (s : String) : String :=
  let rec aux (buff res : List Char) : List Char → List Char
    | []      => res.reverse
    | a :: as =>
      if a != '0'
        then aux [] (a :: (buff ++ res)) as
        else aux (a :: buff) res as
  ⟨aux [] [] s.data⟩

protected def Literal.toString : Literal → String
  | bool  b => toString b
  | int   i => toString i
  | float f => removeRightmostZeros $ toString f
  | str   s => s

def Lambda.typeStr : Lambda → String
  | mk l .. => (l.foldl (init := "") fun acc _ => acc ++ "_ → ") ++ "_"

def Value.typeStr : Value → String
  | nil    => "nil"
  | lit  l => l.typeStr
  | list _ => "list"
  | lam  l => l.typeStr

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

def opError (app l r : String) : String :=
  s!"I can't perform a '{app}' operation between '{l}' and '{r}'"

def opError1 (app v : String) : String :=
  s!"I can't perform a '{app}' operation on '{v}'"

def Value.not : Value → Except String Value
  | lit $ .bool b => return lit $ .bool !b
  | v             => throw $ opError1 "!" v.typeStr

def Value.add : Value → Value → Except String Value
  | lit $ .bool  bₗ, lit $ .bool  bᵣ => return lit $ .bool $ bₗ || bᵣ
  | lit $ .int   iₗ, lit $ .int   iᵣ => return lit $ .int  $ iₗ +  iᵣ
  | lit $ .float fₗ, lit $ .float fᵣ => return lit $ .float $ fₗ +  fᵣ
  | lit $ .int   iₗ, lit $ .float fᵣ => return lit $ .float $ (.ofInt iₗ) +  fᵣ
  | lit $ .float fₗ, lit $ .int   iᵣ => return lit $ .float $ fₗ +  (.ofInt iᵣ)
  | lit $ .str   sₗ, lit $ .str   sᵣ => return lit $ .str   $ sₗ ++ sᵣ
  | list         lₗ, list         lᵣ => return list  $ lₗ ++ lᵣ
  | list         l,  lit          r  => return list  $ l.concat r
  | l,               r               => throw $ opError "+" l.typeStr r.typeStr

def Value.mul : Value → Value → Except String Value
  | lit $ .bool  bₗ, lit $ .bool  bᵣ => return .lit $ .bool  $ bₗ && bᵣ
  | lit $ .int   iₗ, lit $ .int   iᵣ => return .lit $ .int   $ iₗ *  iᵣ
  | lit $ .float fₗ, lit $ .float fᵣ => return .lit $ .float $ fₗ *  fᵣ
  | lit $ .int   iₗ, lit $ .float fᵣ => return .lit $ .float $ (.ofInt iₗ) *  fᵣ
  | lit $ .float fₗ, lit $ .int   iᵣ => return .lit $ .float $ fₗ *  (.ofInt iᵣ)
  | l,               r               => throw $ opError "*" l.typeStr r.typeStr

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
  | l,               r               => throw $ opError "<" l.typeStr r.typeStr

def Value.le : Value → Value → Except String Value
  | lit $ .bool  bₗ, lit $ .bool  bᵣ => return lit $ .bool $ bₗ.toNat ≤ bᵣ.toNat
  | lit $ .int   iₗ, lit $ .int   iᵣ => return lit $ .bool $ iₗ ≤ iᵣ
  | lit $ .float fₗ, lit $ .float fᵣ => return lit $ .bool $ fₗ ≤ fᵣ
  | lit $ .int   iₗ, lit $ .float fᵣ => return lit $ .bool $ (.ofInt iₗ) ≤ fᵣ
  | lit $ .float fₗ, lit $ .int   iᵣ => return lit $ .bool $ fₗ ≤ (.ofInt iᵣ)
  | lit $ .str   sₗ, lit $ .str   sᵣ => return lit $ .bool $ sₗ < sᵣ || sₗ == sᵣ
  | list lₗ, list  lᵣ => return lit $ .bool $ lₗ.length ≤ lᵣ.length
  | l,         r      => throw $ opError "<=" l.typeStr r.typeStr

def Value.gt : Value → Value → Except String Value
  | lit $ .bool  bₗ, lit $ .bool  bᵣ => return lit $ .bool $ bₗ.toNat > bᵣ.toNat
  | lit $ .int   iₗ, lit $ .int   iᵣ => return lit $ .bool $ iₗ > iᵣ
  | lit $ .float fₗ, lit $ .float fᵣ => return lit $ .bool $ fₗ > fᵣ
  | lit $ .int   iₗ, lit $ .float fᵣ => return lit $ .bool $ (.ofInt iₗ) > fᵣ
  | lit $ .float fₗ, lit $ .int   iᵣ => return lit $ .bool $ fₗ > (.ofInt iᵣ)
  | lit $ .str   sₗ, lit $ .str   sᵣ => return lit $ .bool $ sₗ > sᵣ
  | list lₗ, list lᵣ => return lit $ .bool $ lₗ.length > lᵣ.length
  | l,       r       => throw $ opError ">" l.typeStr r.typeStr

def Value.ge : Value → Value → Except String Value
  | lit $ .bool  bₗ, lit $ .bool  bᵣ => return lit $ .bool $ bₗ.toNat ≥ bᵣ.toNat
  | lit $ .int   iₗ, lit $ .int   iᵣ => return lit $ .bool $ iₗ ≥ iᵣ
  | lit $ .float fₗ, lit $ .float fᵣ => return lit $ .bool $ fₗ ≥ fᵣ
  | lit $ .int   iₗ, lit $ .float fᵣ => return lit $ .bool $ (.ofInt iₗ) ≥ fᵣ
  | lit $ .float fₗ, lit $ .int   iᵣ => return lit $ .bool $ fₗ ≥ (.ofInt iᵣ)
  | lit $ .str   sₗ, lit $ .str   sᵣ => return lit $ .bool $ sₗ > sᵣ || sₗ == sᵣ
  | list lₗ, list  lᵣ => return lit $ .bool $ lₗ.length ≥ lᵣ.length
  | l,       r        => throw $ opError ">=" l.typeStr r.typeStr

def Value.eq : Value → Value → Except String Value
  | nil,     nil      => return lit $ .bool true
  | lit  lₗ, lit lᵣ   => return lit $ .bool $ lₗ.eq lᵣ
  | list lₗ, list  lᵣ => return lit $ .bool (listLiteralEq lₗ lᵣ)
  | lam .. , lam ..   => throw "I can't compare functions"
  | _,       _        => return lit $ .bool false

def Value.ne : Value → Value → Except String Value
  | nil,     nil      => return lit $ .bool false
  | lit  lₗ, lit lᵣ   => return lit $ .bool $ !(lₗ.eq lᵣ)
  | list lₗ, list  lᵣ => return lit $ .bool !(listLiteralEq lₗ lᵣ)
  | lam ..,  lam ..   => throw "I can't compare functions"
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

mutual

  partial def unfoldExpressions (es : NEList Expression) : String :=
    (es.map exprToString).unfoldStrings

  partial def exprToString : Expression → String
    | .var  n    => n
    | .lit  l    => l.toString
    | .list l    => toString $ l.map Literal.toString
    | .lam  _    => "«function»"
    | .app  e es => s!"({exprToString e} {unfoldExpressions es})"
    | .unOp  .not e   => s!"!{exprToString e}"
    | .binOp .add l r => s!"({exprToString l} + {exprToString r})"
    | .binOp .mul l r => s!"({exprToString l} * {exprToString r})"
    | .binOp .eq  l r => s!"({exprToString l} = {exprToString r})"
    | .binOp .ne  l r => s!"({exprToString l} != {exprToString r})"
    | .binOp .lt  l r => s!"({exprToString l} < {exprToString r})"
    | .binOp .le  l r => s!"({exprToString l} <= {exprToString r})"
    | .binOp .gt  l r => s!"({exprToString l} > {exprToString r})"
    | .binOp .ge  l r => s!"({exprToString l} >= {exprToString r})"

end

instance : ToString Expression := ⟨exprToString⟩

def valToString : Value → String
    | .nil    => "«nil»"
    | .lit  l => l.toString
    | .list l => toString $ l.map Literal.toString
    | .lam  _ => "«function»"

instance : ToString Value := ⟨valToString⟩
