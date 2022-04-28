/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import FxyLang.Reasoning.Defs

theorem State.extendsForward {s : State}
  (hs : s.extends k) (hc : s.canContinue) :
    s.step.extends k := by
  sorry

theorem State.reachDeterministic'
  (h : (ret v₁ c₁ k).reachesWith (ret v₂ c₂ k) (·.«extends» k)) :
    v₁ = v₂ ∧ c₁ = c₂ := by
  sorry

theorem reachDeterministic {s: State} 
  (h₁ : s.reachesWith (.ret v₁ c₁ k) (·.«extends» k))
  (h₂ : s.reachesWith (.ret v₂ c₂ k) (·.«extends» k)) :
    v₁ = v₂ ∧ c₁ = c₂ := by
  sorry

theorem Determinism (h₁ : ⟦c, p⟧ » ⟦c₁, v₁⟧) (h₂ : ⟦c, p⟧ » ⟦c₂, v₂⟧) :
  v₁ = v₂ ∧ c₁ = c₂ := reachDeterministic (h₁ default) (h₂ default)
