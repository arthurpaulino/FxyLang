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

  partial def reduce (c : Context) : Expression → Result
    | .lit  l => .val $ .lit  l
    | .list l => .val $ .list l
    | .lam  l => .val $ .lam  l
    | .var  n => match c[n] with
      | none   => .err .name $ notFound n
      | some v => .val $ v
    | .app e es => match reduce c e with
      | .val $ .lam $ .mk ns h p => match h' : consume p ns es with
        | some (some l, p) => .val $ .lam $ .mk l (noDupOfConsumeNoDup h h') p
        | some (none, p) => (p.run! c).2
        | none => .err .runTime $ wrongNParameters e ns.length es.length
      | .val v                   => .err .type $ notAFunction e v
      | er@(.err ..)             => er
    | .unOp o e => match reduce c e with
      | .val v      => match v.unOp o with
        | .ok    v => .val v
        | .error m => .err .type m
      | er@(.err ..) => er
    | .binOp o eₗ eᵣ => match (reduce c eₗ, reduce c eᵣ) with
      | (.val vₗ, .val vᵣ) => match vₗ.binOp vᵣ o with
        | .ok    v => .val v
        | .error m => .err .type m
      | (er@(.err ..), _)        => er
      | (_, er@(.err ..))        => er

  partial def Program.run! (c : Context := default) :
      Program → Context × Result
    | skip      => (c, .val .nil)
    | eval e => (c, (reduce c e))
    | seq p₁ p₂ =>
      let res := p₁.run! c
      match res.2 with
      | .err .. => res
      | _       => p₂.run! res.1
    | decl n p => match (p.run! c).2 with
      | er@(.err ..) => (c, er)
      | .val v => (c.insert n v, .val .nil)
    | fork e pT pF => match reduce c e with
      | .val $ .lit $ .bool b => if b then pT.run! c else pF.run! c
      | .val v                => (c, .err .type $ cantEvalAsBool e v)
      | er@(.err ..)          => (c, er)
    | loop e p  => match reduce c e with
      | .val $ .lit $ .bool b =>
        if !b then (c, .val .nil) else
          match p.run! c with
          | er@(_, .err ..) => er
          | (c, _)        => (loop e p).run! c
      | .val v       => (c, .err .type $ cantEvalAsBool e v)
      | er@(.err ..) => (c, er)
    | print e   => match reduce c e with
      | .val v       => dbg_trace v; (c, .val .nil)
      | er@(.err ..) => (c, er)

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
  | prog .skip c k => ret .nil c k
  | prog (.eval e) c k => expr e c k
  | prog (.seq p₁ p₂) c k => prog p₁ c (.seq p₂ k)
  | prog (.decl n p) c k => prog p c $ .block c (.decl n k)
  | prog (.fork e pT pF) c k => expr e c (.fork e pT pF k)
  | prog (.loop e p) c k => expr e c (.loop e p k)
  | prog (.print e) c k => expr e c (.print k)

  | expr (.lit l) c k => ret (.lit l) c k
  | expr (.list l) c k => ret (.list l) c k
  | expr (.var nm) c k => match c[nm] with
    | none   => error .name c $ notFound nm
    | some v => ret v c k
  | expr (.lam l) c k => ret (.lam l) c k
  | expr (.app e es) c k => expr e c (.app e es k)
  | expr (.unOp o e) c k => expr e c (.unOp o e k)
  | expr (.binOp o e₁ e₂) c k => expr e₁ c (.binOp₁ o e₂ k)
 
  | ret v c .exit => done v c
  | ret v c (.print k) => dbg_trace v; ret .nil c k
  | ret _ c (.seq p k) => prog p c k

  | ret v _ (.block c k) => ret v c k

  | ret v c (.app e es k) => match v with
    | .lam $ .mk ns h p => match h' : consume p ns es with
      | some (some l, p) =>
        ret (.lam $ .mk l (noDupOfConsumeNoDup h h') p) c k
      | some (none, p) => prog p c (.block c k)
      | none => error .runTime c $ wrongNParameters e ns.length es.length
    | v                 => error .type c $ notAFunction e v
 
  | ret (.lit $ .bool true)  c (.fork _ pT _ k) => prog pT c k
  | ret (.lit $ .bool false) c (.fork _ _ pF k) => prog pF c k
  | ret v c (.fork e ..) => error .type c $ cantEvalAsBool e v

  | ret (.lit $ .bool true) c (.loop e p k) => prog (.seq p (.loop e p)) c k
  | ret (.lit $ .bool false) c (.loop _ _ k) => ret .nil c k
  | ret v c (.loop e ..) => error .type c $ cantEvalAsBool e v

  | ret v c (.decl n k) => ret .nil (c.insert n v) k

  | ret v c (.unOp o e k) => match v.unOp o with
    | .error m => error .type c m
    | .ok    v => ret v c k
  | ret v₁ c (.binOp₁ o e₂ k) => expr e₂ c (.binOp₂ o v₁ k)
  | ret v₂ c (.binOp₂ o v₁ k) => match v₁.binOp v₂ o with
    | .error m => error .type c m
    | .ok    v => ret v c k

  | s@(error ..) => s
  | s@(done ..)  => s

partial def Program.run (p : Program) : Context × Result :=
  let rec run' (s : State) : Context × Result :=
    match s.step with
    | .error t c m => (c, .err t m)
    | .done  v c   => (c, .val v)
    | s            => run' s
  run' $ State.prog p default .exit
