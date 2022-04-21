/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import FxyLang.Implementation.Execution

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

def State.reaches (s₁ s₂ : State) : Prop :=
  ∃ n, s₁.stepN n = s₂

notation s  "^" "[" n "]" => State.stepN s n
notation s₁ " ↠ " s₂ => State.reaches s₁ s₂

def bigStep (c : Context) (p : Program) (c' : Context) (v : Value) : Prop :=
  ∀ k, .prog p c k ↠ .ret v c' k

notation "(" c ", " p ")" " » " "(" c' ", " v ")" => bigStep c p c' v

theorem State.skip : (c, .skip) » (c, .nil) :=
  fun _ => ⟨1 , by simp only [stepN, step]⟩

theorem State.decl : (c, .decl nm p) » (c', v) → c = c.insert nm v := by
  sorry

theorem State.eval : (c, .eval e) » (c', v) → c = c' := by
  intro h
  simp only [bigStep, reaches] at h
  have k : Continuation := default
  specialize h k
  cases h with | intro n h =>
  sorry

theorem State.print : (c, .print e) » (c', v) → c = c' := by
  intro h
  rw [bigStep] at h
  sorry

theorem State.stepNComp : (s^[n₁])^[n₂] = s^[n₁ + n₂] := by
  induction n₁ generalizing s with
  | zero => simp [stepN]
  | succ n hi =>
    have := @hi (s^[1])
    simp only [stepN] at this
    rw [stepN, this]
    have : n.succ + n₂ = (n + n₂).succ := by
      simp only [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]; rfl
    rw [this, stepN]

theorem State.reachTransitive (h₁₂ : s₁ ↠ s₂) (h₂₃ : s₂ ↠ s₃) : s₁ ↠ s₃ := by
  simp [reaches] at *
  cases h₁₂ with | intro n₁₂ h₁₂ =>
  cases h₂₃ with | intro n₂₃ h₂₃ =>
  rw [← h₁₂, stepNComp] at h₂₃
  exact ⟨n₁₂ + n₂₃, h₂₃⟩

theorem State.progression : ∃ n, (s^[n]).isEnd ∨ (s^[n]).isProg := by
  cases s with
  | prog  => exact ⟨0, by simp [stepN, isProg]⟩
  | done  => exact ⟨0, by simp [stepN,  isEnd]⟩
  | error => exact ⟨0, by simp [stepN,  isEnd]⟩
  | ret  v c k => sorry
  | expr e c k => sorry
