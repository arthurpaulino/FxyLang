/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import FxyLang.Implementation.Execution
import Lean

def State.isProg : State → Bool
  | prog .. => true
  | _       => false

def State.isEnd : State → Bool
  | done  .. => true
  | error .. => true
  | _        => false

def State.stepN : State → Nat → State
  | s, 0     => s
  | s, n + 1 => s.step.stepN n

notation s "^" "[" n "]" => State.stepN s n

def State.reachesWith (s₁ s₂ : State) (f : State → Prop) : Prop :=
  ∃ n, s₁^[n] = s₂ ∧ ∀ i, i ≤ n → f (s₁^[i])

inductive Continuation.extends (k : Continuation) : Continuation → Prop
  | byId     : «extends» k k
  | bySeq    : «extends» k k' → «extends» k (.seq      _ k')
  | byDecl   : «extends» k k' → «extends» k (.decl     _ k')
  | byFork   : «extends» k k' → «extends» k (.fork _ _ _ k')
  | byLoop   : «extends» k k' → «extends» k (.loop   _ _ k')
  | byUnOp   : «extends» k k' → «extends» k (.unOp   _ _ k')
  | byBinOp₁ : «extends» k k' → «extends» k (.binOp₁ _ _ k')
  | byBinOp₂ : «extends» k k' → «extends» k (.binOp₂ _ _ k')
  | byApp    : «extends» k k' → «extends» k (.app    _ _ k')
  | byBlock  : «extends» k k' → «extends» k (.block    _ k')
  | byPrint  : «extends» k k' → «extends» k (.print      k')

def Continuation.height : Continuation → Nat
  | exit         => 1
  | seq      _ k => k.height + 1
  | decl     _ k => k.height + 1
  | fork _ _ _ k => k.height + 1
  | loop   _ _ k => k.height + 1
  | unOp   _ _ k => k.height + 1
  | binOp₁ _ _ k => k.height + 1
  | binOp₂ _ _ k => k.height + 1
  | app    _ _ k => k.height + 1
  | block    _ k => k.height + 1
  | print      k => k.height + 1

def State.extends (k₀ : Continuation) : State → Prop
| ret  _ _ k => k₀.extends k
| prog _ _ k => k₀.extends k
| expr _ _ k => k₀.extends k
| error ..   => True
| done  ..   => False

def State.canContinue : State → Bool
  | ret  .. => true
  | expr .. => true
  | prog .. => true
  | _       => false

def bigStep (c : Context) (p : Program) (c' : Context) (v : Value) : Prop :=
  ∀ k, (State.prog p c k).reachesWith (.ret v c' k) (·.«extends» k)

notation "⟦" c ", " p "⟧" " » " "⟦" c' ", " v "⟧" => bigStep c p c' v
