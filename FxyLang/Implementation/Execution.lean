/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import FxyLang.Implementation.ASTUtilities

/- 
This file implements the actual execution of a Fxy program.

There are two ways to run a Fxy program:
* `Program.run!` is fast but uses code that can't be reasoned on
* `Program.run` is ~50% slower, but uses a function that implements small step
semantics and thus can be reasoned on
-/

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

/-- Takes a list of expressions and matches each element with an element from a
list of strings. For each match, it adds a declaration in the beginning of a
given program, returning such modified program -/
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

def State.step : State → State
  | prog c k .skip => ret c k .nil
  | prog c k (.eval e) => expr c k e
  | prog c k (.seq p₁ p₂) => prog c (.seq p₂ k) p₁
  | prog c k (.decl n p) => prog c (.block c (.decl n k)) p
  | prog c k (.fork e pT pF) => expr c (.fork e pT pF k) e
  | prog c k (.loop e p) => expr c (.loop e p k) e
  | prog c k (.print e) => expr c (.print k) e

  | expr c k (.lit l) => ret c k (.lit l)
  | expr c k (.list l) => ret c k (.list l)
  | expr c k (.var nm) => match c[nm] with
    | none   => error c k .name $ notFound nm
    | some v => ret c k v
  | expr c k (.lam l) => ret c k (.lam l)
  | expr c k (.app e es) => expr c (.app e es k) e
  | expr c k (.unOp o e) => expr c (.unOp o e k) e
  | expr c k (.binOp o e₁ e₂) => expr c (.binOp₁ o e₂ k) e₁
 
  | ret c .nil v => done c .nil v

  | ret c (.exit k) v => done c k v
  | ret c (.print k) v => dbg_trace v; ret c k .nil 
  | ret c (.seq p k) _ => prog c k p

  | ret _ (.block c k) v => ret c k v

  | ret c (.app e es k) v => match v with
    | .lam $ .mk ns h p => match h' : consume p ns es with
      | some (some l, p) =>
        ret c k (.lam $ .mk l (noDupOfConsumeNoDup h h') p)
      | some (none, p) => prog c (.block c k) p
      | none => error c k .runTime $ wrongNParameters e ns.length es.length
    | v                 => error c k .type $ notAFunction e v
 
  | ret c (.fork _ pT _ k) (.lit $ .bool true)  => prog c k pT
  | ret c (.fork _ _ pF k) (.lit $ .bool false) => prog c k pF
  | ret c (.fork e _ _ k) v  => error c k .type $ cantEvalAsBool e v

  | ret c (.loop e p k) (.lit $ .bool true) => prog c k (.seq p (.loop e p))
  | ret c (.loop _ _ k) (.lit $ .bool false) => ret c k .nil
  | ret c (.loop e _ k) v => error c k .type $ cantEvalAsBool e v

  | ret c (.decl n k) v => ret (c.insert n v) k .nil

  | ret c (.unOp o e k) v => match v.unOp o with
    | .error m => error c k .type m
    | .ok    v => ret c k v
  | ret c (.binOp₁ o e₂ k) v₁ => expr c (.binOp₂ o v₁ k) e₂
  | ret c (.binOp₂ o v₁ k) v₂ => match v₁.binOp v₂ o with
    | .error m => error c k .type m
    | .ok    v => ret c k v

  | s@(error ..) => s
  | s@(done ..)  => s

partial def Program.run (p : Program) : Context × Result :=
  let rec run' (s : State) : Context × Result :=
    match s.step with
    | .error c _ t m => (c, .err t m)
    | .done  c _ v   => (c, .val v)
    | s              => run' s
  run' $ State.prog default default p
