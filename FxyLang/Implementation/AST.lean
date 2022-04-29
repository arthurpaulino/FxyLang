/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

/-
This file contains the basic types to support the representation of Fxy
programs, their memory states and output.
-/

import FxyLang.Implementation.NEList
import Std

/-- Literals are the most basic units of memory -/
inductive Literal
  | bool  : Bool   → Literal
  | int   : Int    → Literal
  | float : Float  → Literal
  | str   : String → Literal

/-- Binary opperators for addition, multiplication, equality and inequality -/
inductive BinOp
  | add | mul | eq | ne | lt | le | gt | ge

/-- Unary operation for the boolean negation -/
inductive UnOp
  | not

mutual

  /-- The `Lambda` type is used in two scenarios:
  * To represent the definition of a function as an expression
  * To store a function in memory

  Note that a proof of `noDup` is required in order to construct a term of this
  type. It encodes the idea that the argument names of a function cannot be
  duplicated. Adding this restriction in the type itself calls for a response at
  parsing time rather than at execution time. -/
  inductive Lambda
    | mk : (l : NEList String) → l.noDup → Program → Lambda

  /-- Expressions represent fragments of code that can be to be evaluated, that
  is, reduced to a term of `Value` -/
  inductive Expression
    | lit   : Literal → Expression
    | var   : String → Expression
    | lam   : Lambda → Expression
    | list  : List Literal → Expression
    | app   : Expression → NEList Expression → Expression
    | unOp  : UnOp  → Expression → Expression
    | binOp : BinOp → Expression → Expression → Expression

  /-- `Program` is the main building block for Fxy programs:
  * `skip`  does nothing
  * `eval`  is a pure evaluation of an expression, mostly used for return values
  * `decl`  represents an attribution, being able to alter the context in memory
  * `seq`   is used to stack sequences of programs
  * `fork`  represents an "if/else" logic
  * `loop`  represents a "while" logic
  * `print` calls out a print routine -/
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

/-- The actual values of variables in memory -/
inductive Value
  | nil  : Value
  | lit  : Literal → Value
  | list : List Literal → Value
  | lam  : Lambda → Value
  deriving Inhabited

/-- Used to keep track of what's stored in variables -/
abbrev Context := Std.HashMap String Value

/-- `Continuation` can be understood as a stack, meant to represent what needs
to be done once a certain computation finishes. For instance, when an expression
is evaluated, the top of the stack will contain the information as to *why* such
expression was evaluated in the first place. Are we in a loop? A fork? Are we
adding up two numbers? -/
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

/-- The type of error that may occur during a  -/
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
