/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

/-
This file contains the basic types to support the representation of Fxy
programs, their memory states
-/

import FxyLang.Implementation.NEList
import Std

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

abbrev Context := Std.HashMap String Value

inductive Continuation
  | nil    : Continuation
  | exit   : Continuation → Continuation
  | seq    : Program → Continuation → Continuation
  | decl   : String → Continuation → Continuation
  | fork   : Expression → Program → Program → Continuation → Continuation
  | loop   : Expression → Program → Continuation → Continuation
  | unOp   : UnOp → Expression → Continuation → Continuation
  | binOp₁ : BinOp → Expression → Continuation → Continuation
  | binOp₂ : BinOp → Value → Continuation → Continuation
  | app    : Expression → NEList Expression → Continuation → Continuation
  | block  : Context → Continuation → Continuation
  | print  : Continuation → Continuation
  deriving Inhabited

inductive ErrorType
  | name | type | runTime

inductive State
  | ret   : Context → Continuation → Value      → State
  | prog  : Context → Continuation → Program    → State
  | expr  : Context → Continuation → Expression → State
  | error : Context → Continuation → ErrorType  → String → State
  | done  : Context → Continuation → Value      → State

inductive Result
  | val : Value → Result
  | err : ErrorType → String → Result
  deriving Inhabited
