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

def Continuation.depth : Continuation → Nat
  | exit       k
  | seq      _ k
  | decl     _ k
  | fork _ _ _ k
  | loop   _ _ k
  | unOp   _ _ k
  | binOp₁ _ _ k
  | binOp₂ _ _ k
  | app    _ _ k
  | block    _ k
  | print      k => k.depth + 1
  | nil          => 1

def State.continuation : State → Continuation
  | ret   _ k _
  | prog  _ k _
  | expr  _ k _
  | error _ k _ _
  | done  _ k _   => k

def State.extends (s s₀ : State) : Prop :=
  s.continuation.extends s₀.continuation

def State.reaches (s₁ s₂ : State) : Prop :=
  ∃ n, s₁^[n] = s₂ ∧ ∀ i, i ≤ n → State.extends (s₁^[i]) s₁

notation s₁ " ↠ " s₂ => State.reaches s₁ s₂

def bigStep (c : Context) (p : Program) (c' : Context) (v : Value) : Prop :=
  ∀ k, .prog c k p ↠ .ret c' k v

notation "⟦" c ", " p "⟧" " » " "⟦" c' ", " v "⟧" => bigStep c p c' v
