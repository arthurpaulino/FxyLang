/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import Std
import FxyLang.ASTUtilities

def cantEvalAsBool (e : Expression) (v : Value) : String :=
  s!"can't evaluate {v} as bool. expression {e} has type {v.typeStr}"

def notFound (n : String) : String :=
  s!"'{n}' not found"

def notUncurriedFunction (n : String) : String :=
  s!"'{n}' is not an uncurried function"

def consume (p : Program) :
    NEList String → NEList Expression →
      Except String ((Option (NEList String)) × Program)
  | .cons n ns, .cons e es => consume (.seq (.decl n (.eval e)) p) ns es
  | .cons n ns, .uno  e    => .ok (some ns, .seq (.decl n (.eval e)) p)
  | .uno  n,    .uno  e    => .ok (none, .seq (.decl n (.eval e)) p)
  | .uno  _,    .cons ..   => throw "incompatible number of parameters"

theorem noDupOfConsumeNoDup
  (h : ns.noDup) (h' : consume p' ns es = .ok (some l, p)) :
    l.noDup = true := by
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
  | val : Value → Result
  | err : String → Result
  deriving Inhabited

def Result.toString : Result → String
  | val v => v.toString
  | err m => s!"error: {m}"

instance : ToString Result := ⟨Result.toString⟩

mutual

  partial def reduce (ctx : Context) : Expression → Result
    | .lit  l   => .val $ .lit l
    | .list l   => .val $ .list l
    | .lam  l   => .val $ .lam l
    | .var  n   => match ctx[n] with
      | none   => .err $ notFound n
      | some v => .val $ v
    | .app n es => match ctx[n] with
      | none                     => .err $ notFound n
      | some (.lam $ .mk ns h p) =>
        match h' : consume p ns es with
        | .ok (some l, p) => .val $ .lam $ .mk l (noDupOfConsumeNoDup h h') p
        | .ok (none, p)   => (p.run! ctx).2
        | .error m        => .err m
      | _ => .err $ notUncurriedFunction n
    | .unOp o e => match reduce ctx e with
      | .val v      => match v.unOp o with
        | .ok    v => .val v
        | .error m => .err m
      | er@(.err m) => er
    | .binOp o eₗ eᵣ => match (reduce ctx eₗ, reduce ctx eᵣ) with
      | (.val vₗ, .val vᵣ) => match vₗ.binOp vᵣ o with
        | .ok    v => .val v
        | .error m => .err m
      | (.err m, _)        => .err m
      | (_, .err m)        => .err m

  partial def Program.run! (ctx : Context := default) :
      Program → Context × Result
    | skip      => (ctx, .val .nil)
    | eval e => (ctx, (reduce ctx e))
    | seq p₁ p₂ =>
      let res := p₁.run! ctx
      match res.2 with
      | .err _ => res
      | _      => p₂.run! res.1
    | decl n p => match (p.run! ctx).2 with
      | .err s => (ctx, .err s)
      | .val v => (ctx.insert n v, .val .nil)
    | fork e pT pF => match reduce ctx e with
      | .val $ .lit $ .bool b => if b then pT.run! ctx else pF.run! ctx
      | .val v                => (ctx, .err $ cantEvalAsBool e v)
      | .err m                => (ctx, .err m)
    | loop e p  => match reduce ctx e with
      | .val $ .lit $ .bool b =>
        if !b then (ctx, .val .nil) else
          match p.run! ctx with
          | er@(_, .err _) => er
          | (ctx, _)       => (loop e p).run! ctx
      | .val v      => (ctx, .err $ cantEvalAsBool e v)
      | er@(.err _) => (ctx, er)
    | print e   => match reduce ctx e with
      | .val v => dbg_trace v; (ctx, .val .nil)
      | er@(.err _) => (ctx, er)

end

inductive Continuation
  | exit   : Continuation
  | seq    : Program → Continuation → Continuation
  | decl   : Context → String → Continuation → Continuation
  | fork   : Expression → Program → Program → Continuation → Continuation
  | unOp   : UnOp → Expression → Continuation → Continuation
  | binOp1 : BinOp → Expression → Continuation → Continuation
  | binOp2 : BinOp → Value → Continuation → Continuation
  | print  : Continuation → Continuation

inductive State
  | ret   : Context → Value → Continuation → State
  | prog  : Context → Program → Continuation → State
  | expr  : Context → Expression → Continuation → State
  | error : Context → String → State
  | done  : Context → Value → State

def State.step : State → State
  | prog ctx .skip k => ret ctx .nil k
  | prog ctx (.eval e) k => expr ctx e k
  | prog ctx (.seq p₁ p₂) k => prog ctx p₁ (.seq p₂ k)
  | prog ctx (.decl n p) k => prog ctx p (.decl ctx n k)
  | prog ctx (.fork e pT pF) k => expr ctx e (.fork e pT pF k)
  | prog ctx lp@(.loop e p) k => expr ctx e (.fork e (.seq p lp) .skip k)
  | prog ctx (.print e) k => expr ctx e (.print k)
  | ret ctx v .exit => done ctx v
  | expr ctx (.lit l) k => ret ctx (.lit l) k
  | expr ctx (.list l) k => ret ctx (.list l) k
  | expr ctx (.var n) k => match ctx[n] with
    | none   => error ctx $ notFound n
    | some v => ret ctx v k
  | expr ctx (.lam l@(.mk ..)) k => ret ctx (.lam l) k
  | expr ctx (.app n es) k => match ctx[n] with
    | some (.lam $ .mk ns h p) =>
      match h' : consume p ns es with
      | .ok (some l, p) => ret ctx (.lam $ .mk l (noDupOfConsumeNoDup h h') p) k
      | .ok (none, p)   => prog ctx p k
      | .error m        => error ctx m
    | none => error ctx $ notFound n
    | _    => error ctx $ notUncurriedFunction n
  | expr ctx (.unOp o e) k => expr ctx e (.unOp o e k)
  | expr ctx (.binOp o e1 e2) k => expr ctx e1 (.binOp1 o e2 k)
  | ret ctx v (.print k) => dbg_trace v; ret ctx .nil k
  | ret ctx _ (.seq p k) => prog ctx p k
  | ret ctx (.lit $ .bool true) (.fork _ pT _ k) => prog ctx pT k
  | ret ctx (.lit $ .bool false) (.fork _ _ pF k) => prog ctx pF k
  | ret ctx v (.fork e ..) => error ctx $ cantEvalAsBool e v
  | ret _ v (.decl ctx n k) => ret (ctx.insert n v) .nil k
  | ret ctx v (.unOp o e k) => match v.unOp o with
    | .error m => error ctx m
    | .ok    v => ret ctx v k
  | ret ctx v1 (.binOp1 o e2 k) => expr ctx e2 (.binOp2 o v1 k)
  | ret ctx v2 (.binOp2 o v1 k) => match v1.binOp v2 o with
    | .error m => error ctx m
    | .ok    v => ret ctx v k
  | s@(error ..) => s
  | s@(done ..)  => s

partial def Program.run (p : Program) : Context × Result :=
  let rec run' (s : State) : Context × Result :=
    match s.step with
    | .error ctx m => (ctx, .err m)
    | .done  ctx v => (ctx, .val v)
    | s            => run' s
  run' $ State.prog {} p .exit
