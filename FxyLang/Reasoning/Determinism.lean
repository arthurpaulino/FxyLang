/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import FxyLang.Reasoning.Defs

theorem State.stepNComp : (s^[n₁])^[n₂] = s^[n₁ + n₂] := by
  induction n₁ generalizing s with
  | zero => simp [stepN]
  | succ n hi =>
    rw [stepN, @hi s.step]
    have : n.succ + n₂ = (n + n₂).succ := by
      simp only [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]; rfl
    rw [this, stepN]

theorem State.extendsForward {s : State} (hs : s.extends s₀) :
    s.step.extends s₀ := by
  sorry

theorem State.reachDeterministic' (h : ret c₁ k v₁ ↠ ret c₂ k v₂) :
    v₁ = v₂ ∧ c₁ = c₂ := by
  sorry

theorem State.reachDeterministic {s: State}
  (h₁ : s ↠ ret c₁ k v₁) (h₂ : s ↠ ret c₂ k v₂) :
    v₁ = v₂ ∧ c₁ = c₂ := by
  sorry

theorem Determinism (h₁ : ⟦c, p⟧ » ⟦c₁, v₁⟧) (h₂ : ⟦c, p⟧ » ⟦c₂, v₂⟧) :
  v₁ = v₂ ∧ c₁ = c₂ := State.reachDeterministic (h₁ default) (h₂ default)
