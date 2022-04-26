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

theorem State.doneLoop : done v c^[n] = done v c := by
  induction n with
  | zero      => rw [stepN]
  | succ _ hi => rw [stepN, step]; exact hi

theorem State.errorLoop : error t v c^[n] = error t v c := by
  induction n with
  | zero      => rw [stepN]
  | succ _ hi => rw [stepN, step]; exact hi

-- macro "extract " n:ident " from " h:ident : tactic =>
--   `(tactic| cases $h:ident with | intro $n:ident $h:ident => ?_)

open Lean.Parser.Tactic in
syntax "step_induction " ident (" using " term,+)? (" with " simpLemma)? :tactic

open Lean.Elab.Tactic in
set_option hygiene false in
elab_rules : tactic
  | `(tactic| step_induction $hi $[using $ts,*]? $[with $h]?) => do
    match ts with
    | none    => evalTactic $ ← `(tactic| have $hi:ident := $hi:ident)
    | some ts => evalTactic $ ← `(tactic| have $hi:ident := @$hi:ident $ts*)
    evalTactic $ ← `(tactic| cases $hi:ident with | intro n $hi:ident => ?_)
    match h with
    | none   => evalTactic $
      ← `(tactic| exact ⟨n + 1, by simp only [stepN, step]; exact $hi:ident⟩)
    | some h => evalTactic $
      ← `(tactic| exact ⟨n + 1, by simp only [stepN, step, $h];exact $hi:ident⟩)

theorem State.retProgression :
    ∃ n, (ret v c k^[n]).isEnd ∨ (ret v c k^[n]).isProg := by
  induction k generalizing v c with
  | exit => exact ⟨1, by simp [stepN, step, isEnd]⟩
  | seq  => exact ⟨1, by simp [stepN, step, isProg]⟩
  | decl nm _ hi => step_induction hi using .nil, (c.insert nm v)
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
        | false => step_induction hi using .nil, c
      | _ => exact ⟨1, by simp [stepN, step, isEnd]⟩
    | _ => exact ⟨1, by simp [stepN, step, isEnd]⟩
  | unOp o _ _ hi =>
    cases h : v.unOp o with
    | error => refine ⟨1, by simp [stepN, step, h, isEnd]⟩
    | ok v' => step_induction hi using v', c with h
  | block c' _ hi => step_induction hi using v, c'
  | print _ hi => step_induction hi using .nil, c with dbgTrace
  | _ => sorry

#exit

theorem State.exprProgression :
    ∃ n, (expr e c k^[n]).isEnd ∨ (expr e c k^[n]).isProg := by
  cases e with
  | lit l =>
    cases k with
    | exit  => exact ⟨2, by simp [stepN, step, isEnd]⟩
    | seq   => exact ⟨2, by simp [stepN, step, isProg]⟩
    | decl _ k' => sorry
    | print  k' => 
      cases k' with
      | exit => exact ⟨3, by simp [stepN, step, dbgTrace, isEnd]⟩
      | seq  => exact ⟨3, by simp [stepN, step, dbgTrace, isProg]⟩
      | decl nm k'' =>
        -- cases hi with | intro n hi =>
        refine ⟨3, ?_⟩
        simp [stepN, step, dbgTrace]
        sorry
      | _ => sorry
    | _     => sorry
  | _     => sorry

open State in
theorem Progression : ∃ n, (s^[n]).isEnd ∨ (s^[n]).isProg := by
  cases s with
  | prog  => exact ⟨0, by simp [stepN, isProg]⟩
  | done  => exact ⟨0, by simp [stepN,  isEnd]⟩
  | error => exact ⟨0, by simp [stepN,  isEnd]⟩
  | ret  v c k => exact retProgression
  | expr e c k => exact exprProgression

def State.reachesWith (s₁ s₂ : State) (f : State → Prop) : Prop :=
  ∃ n, s₁^[n] = s₂ ∧ ∀ i, i ≤ n → f (s₁^[i])

inductive Continuation.derives (k₀ : Continuation) : Continuation → Prop
  | byId     : derives k₀ k₀
  | bySeq    : derives k₀ k → derives k₀ (.seq      _ k)
  | byDecl   : derives k₀ k → derives k₀ (.decl     _ k)
  | byFork   : derives k₀ k → derives k₀ (.fork _ _ _ k)
  | byLoop   : derives k₀ k → derives k₀ (.loop   _ _ k)
  | byUnOp   : derives k₀ k → derives k₀ (.unOp   _ _ k)
  | byBinOp₁ : derives k₀ k → derives k₀ (.binOp₁ _ _ k)
  | byBinOp₂ : derives k₀ k → derives k₀ (.binOp₂ _ _ k)
  | byApp    : derives k₀ k → derives k₀ (.app    _ _ k)
  | byBlock  : derives k₀ k → derives k₀ (.block    _ k)
  | byPrint  : derives k₀ k → derives k₀ (.print      k)

open Continuation.derives

def State.derivesFrom (k₀ : Continuation) : State → Prop
| ret  _ _ k => k₀.derives k
| prog _ _ k => k₀.derives k
| expr _ _ k => k₀.derives k
| error ..   => False
| done  ..   => False

def bigStep (c : Context) (p : Program) (c' : Context) (v : Value) : Prop :=
  ∀ k, (State.prog p c k).reachesWith (.ret v c' k) (·.derivesFrom k)

notation "⟦" c ", " p "⟧" " » " "⟦" c' ", " v "⟧" => bigStep c p c' v

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

theorem State.decl (h : ⟦c, .decl nm p⟧ » ⟦c', v⟧) : c' = c.insert nm v := by
  big_step h with k n h₁ h₂
  sorry

def State.canContinue : State → Bool
  | ret  .. => true
  | expr .. => true
  | prog .. => true
  | _       => false

theorem State.derivesForward {s : State}
  (hs : s.derivesFrom k) (hc : s.canContinue) :
    s.step.derivesFrom k := by
  sorry

theorem State.reachDeterministic'
  (h : (ret v₁ c₁ k).reachesWith (ret v₂ c₂ k) (·.derivesFrom k)) :
    v₁ = v₂ ∧ c₁ = c₂ := by
  cases k with
  | exit =>
    cases h with | intro n h =>
    have h := h.1
    cases n with
    | zero   => simp [stepN] at h; exact h
    | succ n => simp only [stepN, step, doneLoop] at h
  | seq p k' =>
    cases h with | intro n h =>
    have h' := h.2
    have h := h.1
    cases n with
    | zero   => simp [stepN] at h; exact h
    | succ n =>
      simp only [stepN, step] at h
      sorry
  | _ => sorry

theorem reachDeterministic {s: State} 
  (h₁ : s.reachesWith (.ret v₁ c₁ k) (·.derivesFrom k))
  (h₂ : s.reachesWith (.ret v₂ c₂ k) (·.derivesFrom k)) :
    v₁ = v₂ ∧ c₁ = c₂ := by
  sorry

theorem Determinism (h₁ : ⟦c, p⟧ » ⟦c₁, v₁⟧) (h₂ : ⟦c, p⟧ » ⟦c₂, v₂⟧) :
  v₁ = v₂ ∧ c₁ = c₂ := reachDeterministic (h₁ default) (h₂ default)
