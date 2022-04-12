/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import Std
import FxyLang.Utilities

def cantEvalAsBool  (v : Value) : String :=
  s!"can't evaluate {v} as bool. expression has type {v.typeStr}"

def notFound (n : String) : String :=
  s!"'{n}' not found"

def consume (p : Program) :
    NEList String → NEList Expression → (Option (NEList String)) × Program
  | .cons n ns, .cons e es => consume (.seq (.decl n (.eval e)) p) ns es
  | .cons n ns, .uno  e    => (some ns, .seq (.decl n (.eval e)) p)
  | .uno  n,    .uno  e    => (none, .seq (.decl n (.eval e)) p)
  | .uno  _,    .cons ..   => (none, .fail "incompatible number of parameters")

theorem noDupOfConsumeNoDup
  (h : ns.noDup) (h' : consume p' ns es = (some l, p)) : l.noDup = true := by
    induction ns generalizing p' es with
    | uno  _      => cases es <;> cases h'
    | cons _ _ hi =>
      simp [NEList.noDup] at h
      cases es with
      | uno  _   => simp [consume] at h'; simp only [h.2, ← h'.1]
      | cons _ _ => exact hi h.2 h'

abbrev Context := Std.HashMap String Value

protected def Context.toString (c : Context) : String :=
  c.toList.foldl (init := "")
    fun acc (n, val) => acc ++ s!"{n}:\t{val}\n"

instance : ToString Context := ⟨Context.toString⟩

-- inductive Result
--   | thk : Program → Result
--   | val : Value   → Result

-- def Context.reduce (ctx : Context) : Expression → Result
--   | .lit l    => .val $ .lit l
--   | .lam l    => .val $ .lam l
--   | .var n    => .val $ match ctx[n] with
--     | none   => .error $ notFound n
--     | some v => v
--   | .list  l  => .val $ .list l
--   | .app n es => match ctx[n] with
--     | none                     => .val $ .error $ notFound n
--     | some (.lam $ .mk ns h p) =>
--       match h' : consume p ns es with
--       | (some l, p) => .val $ .lam $ .mk l (noDupOfConsumeNoDup h h') p
--       | (none,   p) => .thk p
--     | _        => .val $ .error s!"'{n}' is not an uncurried function"
--   | .unOp o e => match ctx.reduce e with
--     | .val v => sorry --.val $ v.unOp o
--     | .thk p => sorry --.thk $ unOp o p

  -- | binOp o pₗ pᵣ => match (pₗ.step ctx, pᵣ.step ctx) with
  --   | ((_, .val vₗ), (_, .val vᵣ)) => (ctx, .val $ vₗ.binOp vᵣ o)
  --   | ((_, .thk t),  (_, .val v))  => (ctx, .thk $ binOp o t v.toProgram)
  --   | ((_, .val v),  (_, .thk t))  => (ctx, .thk $ binOp o v.toProgram t)
  --   | ((_, .thk tₗ), (_, .thk tᵣ)) => (ctx, .thk $ binOp o tₗ tᵣ)

-- def Program.step (ctx : Context) : Program → Context × Result
--   | skip   => (ctx, .val .nil)
--   | fail m => (ctx, .val $ .error m)
--   | eval e => (ctx, ctx.reduce e)


--   | seq p₁ p₂ => match p₁.step ctx with
--     | r@(_, .val $ .error _) => r
--     | (ctx, .val _)          => p₂.step ctx -- discarding value of p₁
--     | (ctx, .thk p₁)         => (ctx, .thk $ seq p₁ p₂)

--   | decl n p => match p.step ctx with
--     | (_, er@(.val $ .error _)) => (ctx, er)
--     | (_, .val v)               => (ctx.insert n v, .val .nil)
--     | (ctx', .thk p')           => (ctx', .thk $ decl n p')

--   | fork e p q => match ctx.reduce e with
--     | .val $ .error m       => (ctx, .val $ .error m)
--     | .val $ .lit $ .bool b => if b then p.step ctx else q.step ctx
--     | .val v                => (ctx, .val (.error (cantEvalAsBool v)))
--     | .thk p?               => (ctx, .thk $ fork p? p q)

--   | lp@(loop e p) => (ctx, .thk $ fork e (seq p lp) skip)

-- partial def Program.run (p : Program) (ctx : Context := default) :
--     Context × Value :=
--   -- dbg_trace ctx
--   -- dbg_trace "--------------"
--   -- dbg_trace p
--   -- dbg_trace "=============="
--   match p.step ctx with
--   | (ctx, .thk p) => p.run ctx
--   | (ctx, .val v) => (ctx, v)

inductive Continuation
  | exit : Continuation
  | seq : Program → Continuation → Continuation
  | decl : Context → String → Continuation → Continuation
  | fork : Program → Program → Continuation → Continuation

inductive State
  | ret : Context → Value → Continuation → State
  | prog : Context → Program → Continuation → State
  | expr : Context → Expression → Continuation → State
  | error : String → State
  | done : Value → State

inductive Reduction
  | val : Value   → Reduction
  | thk : Program → Reduction
  | err : String  → Reduction

def Context.reduce (ctx : Context) : Expression → Reduction
  | .lit l    => .val $ .lit l
  | .lam l    => .val $ .lam l
  | .var n    => match ctx[n] with
    | none   => .err $ notFound n
    | some v => .val v
  | .list  l  => .val $ .list l
  | .app n es => match ctx[n] with
    | none                     => .err $ notFound n
    | some (.lam $ .mk ns h p) =>
      match h' : consume p ns es with
      | (some l, p) => .val $ .lam $ .mk l (noDupOfConsumeNoDup h h') p
      | (none,   p) => .thk p
    | _        => .err s!"'{n}' is not an uncurried function"
  | .unOp o e => match ctx.reduce e with
    | .val v => match v.unOp o with
      | .error m => .err m
      | .ok    v => .val v
    | .thk p => .thk p
    | .err m => .err m

  | .binOp o eₗ eᵣ => match (ctx.reduce eₗ, ctx.reduce eᵣ) with
    | (.val vₗ, .val vᵣ) => match vₗ.binOp vᵣ o with
      | .error m => .err m
      | .ok    v => .val v
    | (.thk t,  .val v)  => sorry
    | (.val v,  .thk t)  => sorry
    | (.thk tₗ, .thk tᵣ) => sorry
    | (.err er, _) => .err er
    | (_, .err er) => .err er

def State.step : State → State
  | prog ctx .skip k => ret ctx .nil k
  | prog _ (.fail m) _ => error m
  | prog ctx (.eval e) k => expr ctx e k
  | prog ctx (.seq p₁ p₂) k => prog ctx p₁ (.seq p₂ k)
  | prog ctx (.decl n p) k => prog ctx p (.decl ctx n k)
  | prog ctx (.fork e pT pF) k => expr ctx e (.fork pT pF k)
  | prog ctx lp@(.loop e p) k => expr ctx e (.fork (.seq p lp) .skip k)
  | ret ctx _ (.seq p k) => prog ctx p k
  | ret ctx (.lit $ .bool true) (.fork pT _ k) => prog ctx pT k
  | ret ctx (.lit $ .bool false) (.fork _ pF k) => prog ctx pF k
  | ret _ v (.fork ..) => error s!"'{v}', of type {v.typeStr}, is not a bool"
  | ret _ v (.decl ctx n k) => ret (ctx.insert n v) .nil k
  | s@(error _) => s
  | s@(done _) => s
  | ret ctx v .exit => done v
  | expr ctx e k => match ctx.reduce e with
    | .val v => ret ctx v k
    | .thk p => prog ctx p k
    | .err m => error m