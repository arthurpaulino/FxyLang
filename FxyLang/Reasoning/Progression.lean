/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import FxyLang.Reasoning.Defs

theorem State.doneLoop : done c k v^[n] = done c k v := by
  induction n with
  | zero      => rw [stepN]
  | succ _ hi => rw [stepN, step]; exact hi

theorem State.errorLoop : error c k t v^[n] = error c k t v := by
  induction n with
  | zero      => rw [stepN]
  | succ _ hi => rw [stepN, step]; exact hi

open Lean.Parser.Tactic in
syntax "step_induction " ident (" using " term,+)?
  (" with " simpLemma)? : tactic

open Lean.Elab.Tactic in
set_option hygiene false in
elab_rules : tactic
  | `(tactic| step_induction $hi $[using $ts,*]? $[with $h]?) => do
    match ts with
    | none    => pure ()
    | some ts => evalTactic $ ← `(tactic| have $hi:ident := @$hi:ident $ts*)
    evalTactic $ ← `(tactic| cases $hi:ident with | intro n $hi:ident => ?_)
    match h with
    | none   => evalTactic $
      ← `(tactic| exact ⟨n + 1, by simp only [stepN, step]; exact $hi:ident⟩)
    | some h => evalTactic $
      ← `(tactic| exact ⟨n + 1, by simp only [stepN, step, $h];exact $hi:ident⟩)

theorem State.retProgression :
    ∃ n, (ret c k v^[n]).isEnd ∨ (ret c k v^[n]).isProg := by
  induction k generalizing c v with
  | exit => exact ⟨1, by simp [stepN, step, isEnd]⟩
  | seq  => exact ⟨1, by simp [stepN, step, isProg]⟩
  | decl nm _ hi => step_induction hi using (c.insert nm v), .nil
  | fork =>
    cases v with
    | lit l =>
      cases l with
      | bool b => cases b <;> exact ⟨1, by simp [stepN, step, isProg]⟩
      | _ => exact ⟨1, by simp [stepN, step, isEnd]⟩
    | _ => exact ⟨1, by simp [stepN, step, isEnd]⟩
  | loop _ _ _ hi =>
    cases v with
    | lit l =>
      cases l with
      | bool b =>
        cases b with
        | true  => exact ⟨1, by simp [stepN, step, isProg]⟩
        | false => step_induction hi using c, .nil
      | _ => exact ⟨1, by simp [stepN, step, isEnd]⟩
    | _ => exact ⟨1, by simp [stepN, step, isEnd]⟩
  | unOp o _ hi =>
    cases h : v.unOp o with
    | error => exact ⟨1, by simp [stepN, step, h, isEnd]⟩
    | ok v' => step_induction hi using c, v' with h
  | block c' _ hi => step_induction hi using c', v
  | print _ hi => step_induction hi using c, .nil with dbgTrace
  | binOp₂ o v₂ _ hi =>
    cases h : v₂.binOp v o with
    | error => exact ⟨1, by simp [stepN, step, h, isEnd]⟩
    | ok v' => step_induction hi using c, v' with h
  | binOp₁ o e k hi =>
    sorry
    -- cases @exprProgression e c (Continuation.binOp₂ o v k) with | intro n h =>
    -- exact ⟨n + 1, by simp only [stepN, step]; exact h⟩
  | app e es k hi =>
    cases v with
    | lam lm =>
      cases lm with
      | mk ns h p =>
        cases h' : consume p ns es with
        | none =>
          exists 1
          simp only [stepN, step]
          split
          next h'' => simp only [h'] at h''
          next h'' => simp only [h'] at h''
          simp [isEnd]
        | some x =>
          match x with
          | (some l, p') =>
            cases @hi c (.lam $ .mk l (noDupOfConsumeNoDup h h') p') with
            | intro n hi =>
              exists n + 1
              simp [stepN, step]
              split
              next h'' =>
                simp [h'] at h''
                simp [← h'', hi]
              all_goals { next h'' => simp [h''] at h' }
          | (none, _) =>
            exists 1
            simp only [stepN, step]
            split
            next h'' => simp [h'] at h''
            simp [isProg]
            simp [isEnd]
    | _ => exact ⟨1, by simp [stepN, step, isEnd]⟩

open Lean.Parser.Tactic in
syntax "step_ret " num " using " term ", " term ", " term
  (" with " simpLemma)? : tactic

open Lean.Elab.Tactic in
set_option hygiene false in
elab_rules : tactic
  | `(tactic| step_ret $n using $v, $c, $k $[with $h]?) => do
    evalTactic $
      ← `(tactic| cases @retProgression $v $c $k with | intro n_ h_ => ?_)
    match h with
    | none => evalTactic $
      ← `(tactic| exact ⟨n_ + $n, by simp only [stepN, step]; exact h_⟩)
    | some h => evalTactic $
      ← `(tactic| exact ⟨n_ + $n, by simp only [stepN, step, $h]; exact h_⟩)

theorem State.exprProgression :
    ∃ n, (expr c k e^[n]).isEnd ∨ (expr c k e^[n]).isProg := by
  cases e with
  | lit l =>
    cases k with
    | exit => exact ⟨2, by simp [stepN, step, isEnd]⟩
    | seq  => exact ⟨2, by simp [stepN, step, isProg]⟩
    | decl nm k => step_ret 2 using c.insert nm (.lit l), k, .nil
    | print k => step_ret 2 using c, k, .nil
    | fork e pT pF k => step_ret 1 using c, .fork e pT pF k, .lit l
    | loop e p k => step_ret 1 using c, .loop e p k, .lit l
    | unOp o k => step_ret 1 using c, .unOp o k, .lit l
    | binOp₁ o e₂ k => step_ret 1 using c, .binOp₁ o e₂ k, .lit l
    | binOp₂ o v₁ k => step_ret 1 using c, .binOp₂ o v₁ k, .lit l
    | app e es k => step_ret 1 using c, .app e es k, .lit l
    | block c' k => step_ret 1 using c, .block c' k, .lit l
  | list l =>
    cases k with
    | exit => exact ⟨2, by simp [stepN, step, isEnd]⟩
    | seq  => exact ⟨2, by simp [stepN, step, isProg]⟩
    | decl nm k => step_ret 2 using c.insert nm (.list l), k, .nil
    | print k => step_ret 2 using c, k, .nil
    | fork e pT pF k => step_ret 1 using c, .fork e pT pF k, .list l
    | loop e p k => step_ret 1 using c, .loop e p k, .list l
    | unOp o k => step_ret 1 using c, .unOp o k, .list l
    | binOp₁ o e₂ k => step_ret 1 using c, .binOp₁ o e₂ k, .list l
    | binOp₂ o v₁ k => step_ret 1 using c, .binOp₂ o v₁ k, .list l
    | app e es k => step_ret 1 using c, .app e es k, .list l
    | block c' k => step_ret 1 using c, .block c' k, .list l
  | var nm =>
    cases h' : c[nm] with
    | none => exact ⟨1, by simp [stepN, step, h', isEnd]⟩
    | some v =>
      cases k with
      | exit => exact ⟨2, by simp [stepN, step, h', isEnd]⟩
      | seq  => exact ⟨2, by simp [stepN, step, h', isProg]⟩
      | decl nm k => step_ret 2 using c.insert nm v, k, .nil with h'
      | print k => step_ret 2 using c, k, .nil with h'
      | fork e pT pF k => step_ret 1 using c, .fork e pT pF k, v with h'
      | loop e p k => step_ret 1 using c, .loop e p k, v with h'
      | unOp o k => step_ret 1 using c, .unOp o k, v with h'
      | binOp₁ o e₂ k => step_ret 1 using c, .binOp₁ o e₂ k, v with h'
      | binOp₂ o v₁ k => step_ret 1 using c, .binOp₂ o v₁ k, v with h'
      | app e es k => step_ret 1 using c, .app e es k, v with h'
      | block c' k => step_ret 1 using c, .block c' k, v with h'
  | lam l =>
    cases k with
    | exit => exact ⟨2, by simp [stepN, step, isEnd]⟩
    | seq  => exact ⟨2, by simp [stepN, step, isProg]⟩
    | decl nm k => step_ret 2 using c.insert nm (.lam l), k, .nil
    | print k => step_ret 2 using c, k, .nil
    | fork e pT pF k => step_ret 1 using c, .fork e pT pF k, .lam l
    | loop e p k => step_ret 1 using c, .loop e p k, .lam l
    | unOp o k => step_ret 1 using c, .unOp o k, .lam l
    | binOp₁ o e₂ k => step_ret 1 using c, .binOp₁ o e₂ k, .lam l
    | binOp₂ o v₁ k => step_ret 1 using c, .binOp₂ o v₁ k, .lam l
    | app e es k => step_ret 1 using c, .app e es k, .lam l
    | block c' k => step_ret 1 using c, .block c' k, .lam l
  | app e es =>
    sorry
    -- cases @exprProgression e c (.app e es k) with | intro n h =>
    -- exact ⟨n + 1, by rw [stepN, step]; exact h⟩
  | unOp o e =>
    sorry
    -- cases @exprProgression e c (.unOp o e k) with | intro n h =>
    -- exact ⟨n + 1, by rw [stepN, step]; exact h⟩
  | binOp o e₁ e₂ =>
    sorry
    -- cases @exprProgression e₁ c (.binOp₁ o e₂ k) with | intro n h =>
    -- exact ⟨n + 1, by rw [stepN, step]; exact h⟩

theorem State.Progression : ∃ n, (s^[n]).isEnd ∨ (s^[n]).isProg := by
  cases s with
  | prog  => exact ⟨0, by simp [stepN, isProg]⟩
  | done  => exact ⟨0, by simp [stepN,  isEnd]⟩
  | error => exact ⟨0, by simp [stepN,  isEnd]⟩
  | ret  v c k => exact retProgression
  | expr e c k => exact exprProgression
