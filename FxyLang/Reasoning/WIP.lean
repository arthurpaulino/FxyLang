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

def State.reaches (s₁ s₂ : State) : Prop :=
  ∃ n, s₁.stepN n = s₂

notation s  "^" "[" n "]" => State.stepN s n
notation s₁ " ↠ " s₂ => State.reaches s₁ s₂

def bigStep (c : Context) (p : Program) (c' : Context) (v : Value) : Prop :=
  ∀ k, .prog p c k ↠ .ret v c' k

notation "⟦" c ", " p "⟧" " » " "⟦" c' ", " v "⟧" => bigStep c p c' v

theorem State.doneLoop : done v c^[n] = done v c := by
  induction n with
  | zero      => rw [stepN]
  | succ _ hi => rw [stepN, step]; exact hi

macro "big_step " k:ident " with " n:ident " at " h:ident : tactic => do
  `(tactic| have $k:ident : Continuation := default;
            specialize $h:ident $k:ident;
            cases $h:ident with | intro $n:ident $h:ident => ?_)

open Lean.Elab.Tactic in
set_option hygiene false in
elab "step_next " n:ident " at " h:ident : tactic => do
  evalTactic $ ←`(tactic| cases $n:ident with
                          | zero => simp [step, stepN] at $h:ident
                          | succ $n:ident => ?_)
  evalTactic $ ← `(tactic| simp [step, stepN] at $h:ident)

theorem State.skip : ⟦c, .skip⟧ » ⟦c, .nil⟧ :=
  fun _ => ⟨1 , by simp only [stepN, step]⟩

theorem State.decl (h : ⟦c, .decl nm p⟧ » ⟦c', v⟧) : c = c.insert nm v := by
  sorry

theorem State.eval (h : ⟦c, .eval e⟧ » ⟦c', v⟧) : c = c' := by
  big_step k with n at h
  step_next n at h
  cases e with
  | lit l =>
    step_next n at h
    cases n with
    | zero =>
      simp [stepN, step] at h
      exact h.2
    | succ n =>
      simp [stepN] at h
      sorry
  | _ => sorry

theorem State.print (h : ⟦c, .print e⟧ » ⟦c', v⟧) : c = c' := by
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

theorem State.retProgression :
    ∃ n, (ret v c k^[n]).isEnd ∨ (ret v c k^[n]).isProg := by
  sorry

theorem State.exprProgression :
    ∃ n, (expr e c k^[n]).isEnd ∨ (expr e c k^[n]).isProg := by
  cases e with
  | lit l =>
    induction k with
    | exit  => exact ⟨2, by simp [stepN, step, isEnd]⟩
    | seq   => exact ⟨2, by simp [stepN, step, isProg]⟩
    | decl  => sorry
    | print => sorry
    | _ => sorry
  | _ => sorry

theorem State.progression : ∃ n, (s^[n]).isEnd ∨ (s^[n]).isProg := by
  cases s with
  | prog  => exact ⟨0, by simp [stepN, isProg]⟩
  | done  => exact ⟨0, by simp [stepN,  isEnd]⟩
  | error => exact ⟨0, by simp [stepN,  isEnd]⟩
  | ret  v c k => exact retProgression
  | expr e c k => exact exprProgression
