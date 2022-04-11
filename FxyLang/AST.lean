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
  | inv   : Literal

inductive BinOp
  | add | mul | eq | ne | lt | le | gt | ge

inductive UnOp
  | not

mutual

  inductive Lambda
    | mk : (l : NEList String) → l.noDup → Program → Lambda

  inductive Expression
    | lit  : Literal → Expression
    | var  : String → Expression
    | lam  : Lambda → Expression
    | list : List Literal → Expression
    | app  : String → NEList Expression → Expression

  inductive Program
    | skip  : Program
    | fail  : String  → Program
    | eval  : Expression → Program
    | decl  : String  → Program → Program
    | seq   : Program → Program → Program
    | loop  : Program → Program → Program
    | fork  : Program → Program → Program → Program
    | binOp : BinOp → Program → Program → Program
    | unOp  : UnOp  → Program → Program

  inductive Value
    | nil   : Value
    | lit   : Literal → Value
    | list  : List Literal → Value
    | error : String → Value
    | lam   : Lambda → Value
    deriving Inhabited

end
