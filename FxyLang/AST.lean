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
    | list : List Literal → Expression
    -- | not  : Expression → Expression
    -- | add  : Expression → Expression → Expression
    -- | mul  : Expression → Expression → Expression
    -- | eq   : Expression → Expression → Expression
    -- | ne   : Expression → Expression → Expression
    -- | lt   : Expression → Expression → Expression
    -- | le   : Expression → Expression → Expression
    -- | gt   : Expression → Expression → Expression
    -- | ge   : Expression → Expression → Expression
    | lam  : Lambda → Expression
    | app  : String → NEList Expression → Expression

  inductive Program
    | skip  : Program
    | fail  : String  → Program
    | eval  : Expression → Program
    | decl  : String  → Program → Program
    | seq   : Program → Program → Program
    | loop  : Program → Program → Program
    | fork  : Program → Program → Program → Program
    | binop : Binop → Program → Program → Program
    | unop  : UnOp  → Program → Program

  inductive Value
    | nil   : Value
    | lit   : Literal → Value
    | list  : List Literal → Value
    | error : String → Value
    | lam   : Lambda → Value
    -- | thunk : Program → Value
    | inv   : Value
    deriving Inhabited

end
