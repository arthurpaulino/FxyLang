/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import FxyLang.Implementation.ASTUtilities

def cantEvalAsBool (e : Expression) (v : Value) : String :=
  s!"I can't evaluate '{e}' as a 'bool' because it reduces to '{v}', of " ++
    s!"type '{v.typeStr}'"

def notFound (n : String) : String :=
  s!"I can't find the definition of '{n}'"

def notAFunction (e : Expression) (v : Value) : String :=
  s!"I can't apply arguments to '{e}' because it evaluates to '{v}', of " ++
    s!"type '{v.typeStr}'"

def wrongNParameters (e : Expression) (allowed provided : Nat) : String :=
  s!"I can't apply {provided} arguments to '{e}' because the maximum " ++
    s!"allowed is {allowed}"

def consume (p : Program) :
    NEList String → NEList Expression →
      Option ((Option (NEList String)) × Program)
  | .cons n ns, .cons e es => consume (.seq (.decl n (.eval e)) p) ns es
  | .cons n ns, .uno  e    => some (some ns, .seq (.decl n (.eval e)) p)
  | .uno  n,    .uno  e    => some (none, .seq (.decl n (.eval e)) p)
  | .uno  _,    .cons ..   => none

theorem noDupOfConsumeNoDup
  (h : ns.noDup) (h' : consume p' ns es = some (some l, p)) :
    l.noDup = true := by
  induction ns generalizing p' es with
  | uno  _      => cases es <;> cases h'
  | cons _ _ hi =>
    simp [NEList.noDup] at h
    cases es with
    | uno  _   => simp [consume] at h'; simp only [h.2, ← h'.1]
    | cons _ _ => exact hi h.2 h'

mutual

  partial def reduce (ctx : Context) : Expression → Result
    | .lit  l => .val $ .lit  l
    | .list l => .val $ .list l
    | .lam  l => .val $ .lam  l
    | .var  n => match ctx[n] with
      | none   => .err .name $ notFound n
      | some v => .val $ v
    | .app e es => match reduce ctx e with
      | .val $ .lam $ .mk ns h p => match h' : consume p ns es with
        | some (some l, p) => .val $ .lam $ .mk l (noDupOfConsumeNoDup h h') p
        | some (none, p) => (p.run! ctx).2
        | none => .err .runTime $ wrongNParameters e ns.length es.length
      | .val v                   => .err .type $ notAFunction e v
      | er@(.err ..)             => er
    | .unOp o e => match reduce ctx e with
      | .val v      => match v.unOp o with
        | .ok    v => .val v
        | .error m => .err .type m
      | er@(.err ..) => er
    | .binOp o eₗ eᵣ => match (reduce ctx eₗ, reduce ctx eᵣ) with
      | (.val vₗ, .val vᵣ) => match vₗ.binOp vᵣ o with
        | .ok    v => .val v
        | .error m => .err .type m
      | (er@(.err ..), _)        => er
      | (_, er@(.err ..))        => er

  partial def Program.run! (ctx : Context := default) :
      Program → Context × Result
    | skip      => (ctx, .val .nil)
    | eval e => (ctx, (reduce ctx e))
    | seq p₁ p₂ =>
      let res := p₁.run! ctx
      match res.2 with
      | .err .. => res
      | _       => p₂.run! res.1
    | decl n p => match (p.run! ctx).2 with
      | er@(.err ..) => (ctx, er)
      | .val v => (ctx.insert n v, .val .nil)
    | fork e pT pF => match reduce ctx e with
      | .val $ .lit $ .bool b => if b then pT.run! ctx else pF.run! ctx
      | .val v                => (ctx, .err .type $ cantEvalAsBool e v)
      | er@(.err ..)          => (ctx, er)
    | loop e p  => match reduce ctx e with
      | .val $ .lit $ .bool b =>
        if !b then (ctx, .val .nil) else
          match p.run! ctx with
          | er@(_, .err ..) => er
          | (ctx, _)        => (loop e p).run! ctx
      | .val v       => (ctx, .err .type $ cantEvalAsBool e v)
      | er@(.err ..) => (ctx, er)
    | print e   => match reduce ctx e with
      | .val v       => dbg_trace v; (ctx, .val .nil)
      | er@(.err ..) => (ctx, er)

end

inductive Continuation
  | exit   : Continuation
  | seq    : Program → Continuation → Continuation
  | decl   : String → Continuation → Continuation
  | fork   : Expression → Program → Program → Continuation → Continuation
  | loop   : Expression → Program → Continuation → Continuation
  | unOp   : UnOp → Expression → Continuation → Continuation
  | binOp₁ : BinOp → Expression → Continuation → Continuation
  | binOp₂ : BinOp → Value → Continuation → Continuation
  | app    : Expression → NEList Expression → Continuation → Continuation
  | block  : Context → Continuation → Continuation
  | print  : Continuation → Continuation
  deriving Inhabited

inductive State
  | ret   : Value      → Context → Continuation → State
  | prog  : Program    → Context → Continuation → State
  | expr  : Expression → Context → Continuation → State
  | error : ErrorType  → Context → String → State
  | done  : Value      → Context → State

def State.step : State → State
  | prog .skip ctx k => ret .nil ctx k
  | prog (.eval e) ctx k => expr e ctx k
  | prog (.seq p₁ p₂) ctx k => prog p₁ ctx (.seq p₂ k)
  | prog (.decl n p) ctx k => prog p ctx $ .block ctx (.decl n k)
  | prog (.fork e pT pF) ctx k => expr e ctx (.fork e pT pF k)
  | prog (.loop e p) ctx k => expr e ctx (.loop e p k)
  | prog (.print e) ctx k => expr e ctx (.print k)

  | expr (.lit l) ctx k => ret (.lit l) ctx k
  | expr (.list l) ctx k => ret (.list l) ctx k
  | expr (.var n) ctx k => match ctx[n] with
    | none   => error .name ctx $ notFound n
    | some v => ret v ctx k
  | expr (.lam l) ctx k => ret (.lam l) ctx k
  | expr (.app e es) ctx k => expr e ctx (.app e es k)
  | expr (.unOp o e) ctx k => expr e ctx (.unOp o e k)
  | expr (.binOp o e₁ e₂) ctx k => expr e₁ ctx (.binOp₁ o e₂ k)
 
  | ret v ctx .exit => done v ctx
  | ret v ctx (.print k) => dbg_trace v; ret .nil ctx k
  | ret _ ctx (.seq p k) => prog p ctx k

  | ret v _ (.block ctx k) => ret v ctx k

  | ret v ctx (.app e es k) => match v with
    | .lam $ .mk ns h p => match h' : consume p ns es with
      | some (some l, p) =>
        ret (.lam $ .mk l (noDupOfConsumeNoDup h h') p) ctx k
      | some (none, p) => prog p ctx (.block ctx k)
      | none => error .runTime ctx $ wrongNParameters e ns.length es.length
    | v                 => error .type ctx $ notAFunction e v
 
  | ret (.lit $ .bool true)  ctx (.fork _ pT _ k) => prog pT ctx k
  | ret (.lit $ .bool false) ctx (.fork _ _ pF k) => prog pF ctx k
  | ret v ctx (.fork e ..) => error .type ctx $ cantEvalAsBool e v

  | ret (.lit $ .bool true) ctx (.loop e p k) => prog (.seq p (.loop e p)) ctx k
  | ret (.lit $ .bool false) ctx (.loop _ _ k) => ret .nil ctx k
  | ret v ctx (.loop e ..) => error .type ctx $ cantEvalAsBool e v

  | ret v ctx (.decl n k) => ret .nil (ctx.insert n v) k

  | ret v ctx (.unOp o e k) => match v.unOp o with
    | .error m => error .type ctx m
    | .ok    v => ret v ctx k
  | ret v1 ctx (.binOp₁ o e2 k) => expr e2 ctx (.binOp₂ o v1 k)
  | ret v2 ctx (.binOp₂ o v1 k) => match v1.binOp v2 o with
    | .error m => error .type ctx m
    | .ok    v => ret v ctx k

  | s@(error ..) => s
  | s@(done ..)  => s

partial def Program.run (p : Program) : Context × Result :=
  let rec run' (s : State) : Context × Result :=
    match s.step with
    | .error t ctx m => (ctx, .err t m)
    | .done  v ctx   => (ctx, .val v)
    | s              => run' s
  run' $ State.prog p default .exit
