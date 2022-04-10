/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import Std
import FxyLang.ASTFunctions

def cantEvalAsBool (v : Value) : String :=
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

inductive Result
  | thk : Program → Result
  | val : Value   → Result

def Context.reduce (ctx : Context) : Expression → Result
  | .lit l    => .val $ .lit l
  | .lam l    => .val $ .lam l
  | .var n    => .val $ match ctx[n] with
    | none   => .error $ notFound n
    | some v => v
  | .list  l  => .val $ .list l
  | .app n es => match ctx[n] with
    | none                     => .val $ .error $ notFound n
    | some (.lam $ .mk ns h p) =>
      match h' : consume p ns es with
      | (some l, p) => .val $ .lam $ .mk l (noDupOfConsumeNoDup h h') p
      | (none,   p) => .thk p
    | _        => .val $ .error s!"'{n}' is not an uncurried function"
  -- | .not   e  => match ctx.reduce e with
  --   | .lit $ .bool b => .lit $ .bool !b
  --   | .thunk p       => .thunk $ .unop .not p
  --   | v              => .error $ cantEvalAsBool v
  -- | .add eL eR => (ctx.reduce eL).add $ ctx.reduce eR
  -- | .mul eL eR => (ctx.reduce eL).mul $ ctx.reduce eR
  -- | .eq  eL eR => (ctx.reduce eL).eq  $ ctx.reduce eR
  -- | .ne  eL eR => (ctx.reduce eL).ne  $ ctx.reduce eR
  -- | .lt  eL eR => (ctx.reduce eL).lt  $ ctx.reduce eR
  -- | .le  eL eR => (ctx.reduce eL).le  $ ctx.reduce eR
  -- | .gt  eL eR => (ctx.reduce eL).gt  $ ctx.reduce eR
  -- | .ge  eL eR => (ctx.reduce eL).ge  $ ctx.reduce eR

def Program.step (ctx : Context) : Program → Context × Result
  | skip   => (ctx, .val .nil)
  | fail m => (ctx, .val $ .error m)
  | eval e => (ctx, ctx.reduce e)

  | unop o p => sorry

  | binop o pₗ pᵣ => sorry

  | seq p₁ p₂ => match p₁.step ctx with
    | r@(_, .val $ .error _) => r
    | (ctx, .val _)          => (ctx, .thk p₂) -- discarding value of p₁
    | (ctx, .thk p₁)         => (ctx, .thk $ seq p₁ p₂)

  | decl n p    => match p.step ctx with
    | r@(_, .val $ .error _) => r
    | (_, .val v)            => (ctx.insert n v, .val .nil)
    | (_, .thk p)            => (ctx, .thk $ decl n p)

  | loop p@(fail _) _ => (ctx, .thk $ p)
  | loop (eval e) p   => match ctx.reduce e with
    | .val $ er@(.error _)  => (ctx, .val er)
    | .val $ .lit $ .bool b =>
      if b then (ctx, .thk (loop (eval e) p)) else (ctx, .val .nil)
    | .val v                => (ctx, .val (.error (cantEvalAsBool v)))
    | .thk p?               => (ctx, .thk $ loop p? p)
  | loop p? p         =>
    match p?.step ctx with
    | (_, .val $ .error m)       => (ctx, .thk $ .fail m)
    | (_, .val $ .lit $ .bool b) =>
      if b then (ctx, .thk (loop p? p)) else (ctx, .val .nil)
    | (_, .val v)                => (ctx, .val (.error (cantEvalAsBool v)))
    | (_, .thk $ p?)             => (ctx, .thk $ loop p? p)

  | fork p@(fail _) .. => (ctx, .thk $ p)
  | fork (eval e) p q  => match ctx.reduce e with
    | .val $ er@(.error _)  => (ctx, .val er)
    | .val $ .lit $ .bool b => if b then p.step ctx else q.step ctx
    | .val $ v              => (ctx, .val (.error (cantEvalAsBool v)))
    | .thk p?               => (ctx, .thk $ fork p? p q)
  | fork p? p q        =>
    match p?.step ctx with
    | (_, .val $ .error m)       => (ctx, .thk $ .fail m)
    | (_, .val $ .lit $ .bool b) => if b then p.step ctx else q.step ctx
    | (_, .val v)                => (ctx, .val (.error (cantEvalAsBool v)))
    | (_, .thk $ p?)            => (ctx, .thk $ fork p? p q)

partial def Program.run (p : Program) (ctx : Context := default) :
    Context × Value :=
  match p.step ctx with
  | (ctx, .thk p) => p.run ctx
  | (ctx, .val v) => (ctx, v)
