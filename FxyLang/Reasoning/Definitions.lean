/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import FxyLang.Implementation.Execution

def Context.equiv (cₗ cᵣ : Context) : Prop :=
  ∀ n, cₗ[n] = cᵣ[n]

def Context.diffBy (cₗ cᵣ : Context) (nm : String) : Prop :=
  ∀ nm', nm' ≠ nm → cₗ[nm'] = cᵣ[nm']

def State.ctx : State → Context
  | ret   _ c _ => c
  | prog  _ c _ => c
  | expr  _ c _ => c
  | error _ c _ => c
  | done  _ c   => c

def State.isProg : State → Prop
  | prog .. => True
  | _       => False

def State.isEnd : State → Prop
  | done  .. => True
  | error .. => True
  | _        => False

def State.stepN : State → Nat → State
  | s, 0     => s
  | s, n + 1 => s.step.stepN n

def State.reaches (s₁ s₂ : State) : Prop :=
  ∃ n, s₁.stepN n = s₂

notation cₗ " ≃ " cᵣ:21 => Context.equiv cₗ cᵣ 
notation cₗ " ≈ " cᵣ " | " nm => Context.diffBy cₗ cᵣ nm
notation s  "¨" n:51 => State.stepN s n
notation s₁ " ↠ " s₂ => State.reaches s₁ s₂

def Program.terminates (p : Program) (c : Context) (k : Continuation) : Prop :=
  ∃ n, ((State.prog p c k)¨n).isEnd

def State.terminates (s : State) : Prop :=
  ∃ n, (s¨n).isEnd

theorem Context.equivSelf {c : Context} : c ≃ c := by
  intro _; rfl

-- theorem Context.eqOfEquiv {cₗ cᵣ : Context} (h : cₗ ≃ cᵣ) : cₗ = cᵣ := sorry

-- theorem Context.equivIff {cₗ cᵣ : Context} : cₗ ≃ cᵣ ↔ cₗ = cᵣ := by
--   constructor
--   · intro h; exact eqOfEquiv h
--   · intro h; rw [h]; exact equivSelf

theorem Context.eqComm {cₗ cᵣ : Context} (h : cₗ ≃ cᵣ) : cᵣ ≃ cₗ := by
  intro _; rw [h]

theorem Context.diffBySelf : c ≈ c | nm := by
  intro _ _; rfl

open Std.HashMap in
theorem Context.diffByOfInsert (h : c' = c.insert nm v) : c' ≈ c | nm := by
  intro nm' hne
  rw [h]
  simp [getOp, find?]
  sorry

theorem State.skipStep (h : s = (prog .skip c k).step) : s.ctx ≃ c := by
  have : s.ctx = c := by rw [h, step, ctx]
  simp only [this, Context.equivSelf]

theorem State.skipClean : (prog .skip c .exit) ↠ (done .nil c) := by
  refine ⟨2 , by simp only [stepN, step]⟩

theorem State.declStep (h : s = (prog (.decl nm p) c k).step) :
    s.ctx ≃ c := by
  rw [h]
  simp only [ctx, step]
  exact Context.equivSelf

theorem State.declClean (h : (prog (.decl nm p) c k) ↠ (done v c')) :
    c' ≈ c | nm := by
  cases h with | intro n h =>
  sorry

theorem State.stepNComp : (s¨n₁)¨n₂ = s¨(n₁ + n₂) := by
  induction n₁ generalizing s with
  | zero => simp [stepN]
  | succ n hi =>
    have := @hi (s¨1)
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

theorem State.continuous : ∃ n, (s¨n).isEnd ∨ (s¨n).isProg := sorry
