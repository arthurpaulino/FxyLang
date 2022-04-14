/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import FxyLang.NEList

inductive Literal
  | bool  : Bool   → Literal
  | int   : Int    → Literal
  | float : Float  → Literal
  | str   : String → Literal

inductive BinOp
  | add | mul | eq | ne | lt | le | gt | ge

inductive UnOp
  | not

mutual

  inductive Lambda
    | mk : (l : NEList String) → l.noDup → Program → Lambda

  inductive Expression
    | lit   : Literal → Expression
    | var   : String → Expression
    | lam   : Lambda → Expression
    | list  : List Literal → Expression
    | app   : Expression → NEList Expression → Expression
    | unOp  : UnOp  → Expression → Expression
    | binOp : BinOp → Expression → Expression → Expression

  inductive Program
    | skip  : Program
    | eval  : Expression → Program
    | decl  : String  → Program → Program
    | seq   : Program → Program → Program
    | fork  : Expression → Program → Program → Program
    | loop  : Expression → Program → Program
    | print : Expression → Program
    deriving Inhabited

end

inductive Value
  | nil  : Value
  | lit  : Literal → Value
  | list : List Literal → Value
  | lam  : Lambda → Value
  deriving Inhabited
