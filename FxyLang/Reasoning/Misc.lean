/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import FxyLang.Reasoning.Defs

theorem Continuation.heightOfExtends {k k' : Continuation} (h : k.extends k') :
    k.height ≤ k'.height := by
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

theorem State.stepNComp : (s^[n₁])^[n₂] = s^[n₁ + n₂] := by
  induction n₁ generalizing s with
  | zero => simp [stepN]
  | succ n hi =>
    have := @hi s.step
    rw [stepN, this]
    have : n.succ + n₂ = (n + n₂).succ := by
      simp only [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]; rfl
    rw [this, stepN]

theorem State.doneLoop : done v c^[n] = done v c := by
  induction n with
  | zero      => rw [stepN]
  | succ _ hi => rw [stepN, step]; exact hi

theorem State.errorLoop : error t v c^[n] = error t v c := by
  induction n with
  | zero      => rw [stepN]
  | succ _ hi => rw [stepN, step]; exact hi
