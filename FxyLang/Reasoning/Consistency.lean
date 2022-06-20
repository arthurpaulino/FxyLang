/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import FxyLang.Reasoning.Defs

open Continuation.extends

theorem Continuation.depthOfExtends {k k' : Continuation} (h : k.extends k') :
    k.depth ≤ k'.depth := by
  induction h with
  | byId          => simp
  | bySeq    _ hi => exact Nat.le_step hi
  | byDecl   _ hi => exact Nat.le_step hi
  | byFork   _ hi => exact Nat.le_step hi
  | byLoop   _ hi => exact Nat.le_step hi
  | byUnOp   _ hi => exact Nat.le_step hi
  | byBinOp₁ _ hi => exact Nat.le_step hi
  | byBinOp₂ _ hi => exact Nat.le_step hi
  | byApp    _ hi => exact Nat.le_step hi
  | byBlock  _ hi => exact Nat.le_step hi
  | byPrint  _ hi => exact Nat.le_step hi

theorem State.skip : ⟦c, .skip⟧ » ⟦c, .nil⟧ := by
  intro k
  refine ⟨1, ?_⟩
  simp [stepN, step]
  intro i hᵢ
  cases i with
  | zero => rw [stepN]; exact byId
  | succ i =>
    cases i with
    | zero => rw [stepN]; exact byId
    | succ i =>
    have : i.succ.succ > 1 := by
      by_cases h : i.succ.succ ≤ 1
      · by_cases h' : i.succ.succ > 1
        · exact h'
        · contradiction
      · exact Nat.gt_of_not_le h  
    contradiction

-- set_option hygiene false in
macro "big_step " h:ident " with "
    k:ident n:ident h₁:ident h₂:ident : tactic => do
  `(tactic| have $k:ident : Continuation := default;
            have $h₁:ident := $h:ident $k:ident;
            cases $h₁:ident with | intro $n:ident FOO__ => ?_;
            have $h₁:ident := FOO__.1;
            have $h₂:ident := FOO__.2;
            clear FOO__)

open Lean.Elab.Tactic in
set_option hygiene false in
elab "small_step " n:ident " at " h:ident : tactic => do
  evalTactic $ ←`(tactic| cases $n:ident with
                          | zero => simp [step, stepN] at $h:ident
                          | succ $n:ident => ?_)
  evalTactic $ ←`(tactic| simp [step, stepN] at $h:ident)

theorem State.eval (h : ⟦c, .eval e⟧ » ⟦c', v⟧) : c = c' := by
  big_step h with k n h₁ h₂
  cases e with
  | lit l =>
    small_step n at h₁
    small_step n at h₁
    sorry
  | _ => sorry

theorem State.decl (h : ⟦c, p⟧ » ⟦c', v⟧) :
    ⟦c, .decl nm p⟧ » ⟦c.insert nm v, .nil⟧ := by
  big_step h with k n h₁ h₂
  sorry
