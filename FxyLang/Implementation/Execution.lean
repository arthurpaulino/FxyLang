/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import FxyLang.Implementation.ASTUtilities

/- Before we proceed, it's important to notice that a function that executes a
program *has* to be `partial` because programs themselves may loop forever.

This file contains two partial functions capable of running Fxy programs:
* `Program.run!` is fast but uses code that can't be reasoned on
* `Program.run` is ~50% slower, but uses a function that implements small step
semantics and thus can be reasoned on

Another important detail is that the computation of a `Program` yields an
intrinsic `Value`:
* `skip` yields `nil`
* `eval` yields the `Value` of the expression being evaluated
* `seq` yields the `Value` of the second `Program`, unless the first one causes
an error
* `fork` yields the `Value` of the child `Program` executed
* `loop` yields `nil` or an error
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

/-- Consuming elements from a non-duplicated NEList results in a non-duplicated
NEList -/
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

/- Next we're going to define a pair of mutual functions:
* `reduce` computes over an expression with the goal of extracting a term of
`Result` from it, which signals either a `Value` or an error.
* `Program.run!` is similar to `reduce`, but it processes a `Program` instead

They are mutual because *i*) a program may rely on the resolution of expressions
to move forward (for instance, knowing whether to loop again or not) and *ii*)
an expression can be the application of a function, which may need to trigger
the execution of another term of `Program` (see the `app` case)
-/

mutual

  /-- Since we're already in the `partial` realm, let's allow ourselves to be
  carelessly recursive, always believing that `reduce` will compute *any*
  expression for us! -/
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

  /-- And here we can allow ourselves to be careless too, trusting on `reduce`
  as well as on `run!`! -/
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

/-- This is the function that will allow us to prove results about the semantics
of Fxy. Let's dive into its details. -/
def State.step : State → State
  /- `skip` just goes straight into returning `nil` -/
  | prog c k .skip => ret c k .nil

  /- `eval` enters the `expr` state for expression evaluation -/
  | prog c k (.eval e) => expr c k e

  /- `seq` runs the first program and stacks the second -/
  | prog c k (.seq p₁ p₂) => prog c (.seq p₂ k) p₁

  /- `decl` calls for the execution of the innermost program and then stores the
  current context with the `block` continuation, which is recovered later on.
  This allows us to have functions running with their own contexts, being able
  to write on them as they need as they will be discarded anyway -/
  | prog c k (.decl n p) => prog c (.block c (.decl n k)) p

  /- `fork`, `loop` and `print` go to the expression evaluation step, keeping
  track of what needs to be done with the returned value later on -/
  | prog c k (.fork e pT pF) => expr c (.fork e pT pF k) e
  | prog c k (.loop e p) => expr c (.loop e p k) e
  | prog c k (.print e) => expr c (.print k) e

  /- If the expression resulted in a literal, a list or a function, just return
  them -/
  | expr c k (.lit l) => ret c k (.lit l)
  | expr c k (.list l) => ret c k (.list l)
  | expr c k (.lam l) => ret c k (.lam l)

  /- If we're supposed to extract the value of a variable, we need to check
  whether it's available in the context or not -/
  | expr c k (.var nm) => match c[nm] with
    | none   => error c k .name $ notFound nm
    | some v => ret c k v
  
  /- For an application we need to evaluate what we're using to apply. We expect
  it to be a function! -/
  | expr c k (.app e es) => expr c (.app e es k) e

  /- For the unary operator we have to evaluate the (only) expression first -/
  | expr c k (.unOp o e) => expr c (.unOp o k) e

  /- For the binary operator, we need to evaluate the first expression first and
  stack up the evaluation of the second one -/
  | expr c k (.binOp o e₁ e₂) => expr c (.binOp₁ o e₂ k) e₁

  /- The `Continuation.exit` signals that there's nothing else to do -/
  | ret c .exit v => done c .exit v

  /- Here we print the returned value and then return `nil` -/
  | ret c (.print k) v => dbg_trace v; ret c k .nil

  /- When returning from the execution of the first program in a `seq`, we
  ignore the value and go straight to the execution of the second program -/
  | ret c (.seq p k) _ => prog c k p

  /- Here we do what we promised and recover the original context stacked with
  the `Continuation.block` constructor -/
  | ret _ (.block c k) v => ret c k v

  /- When returning from an `app` continuation, we need to inspect the value
  that was returned from the evaluation of the first expression -/
  | ret c (.app e es k) v => match v with

    /- The desired case: it's a function! Let's consume it's parameters -/
    | .lam $ .mk ns h p => match h' : consume p ns es with

      /- When `consume` didn't eat up all the arguments we return an
      yet-to-be-uncurried function -/
      | some (some l, p) =>
        ret c k (.lam $ .mk l (noDupOfConsumeNoDup h h') p)
      
      /- All arguments were consumed: let's run the lambda program and use
      `block` to save up the context -/
      | some (none, p) => prog c (.block c k) p
      
      /- This signals that too many arguments were provided -/
      | none => error c k .runTime $ wrongNParameters e ns.length es.length
    
    /- Anything but a function. Error! -/
    | v                 => error c k .type $ notAFunction e v

  /- Now we need to resolve a `fork` given the value returned from the
  expression. We expext it to be a boolean -/
  | ret c (.fork _ pT _ k) (.lit $ .bool true)  => prog c k pT
  | ret c (.fork _ _ pF k) (.lit $ .bool false) => prog c k pF

  /- Not a boolean. Error! -/
  | ret c (.fork e _ _ k) v  => error c k .type $ cantEvalAsBool e v

  /- Resolving a `loop` is similar to a `fork`. We should expect a boolean, at
  least. The difference is that in case of `true`, we run the program and stack
  up the same loop expression and program. In case of `false`, just break the
  loop and return `nil` -/
  | ret c (.loop e p k) (.lit $ .bool true) => prog c k (.seq p (.loop e p))
  | ret c (.loop _ _ k) (.lit $ .bool false) => ret c k .nil
  | ret c (.loop e _ k) v => error c k .type $ cantEvalAsBool e v

  /- The execution of the `decl` program is returning a value. We can finally
  add it to the context under the name recovered from the `Continuation.decl` -/
  | ret c (.decl nm k) v => ret (c.insert nm v) k .nil

  /- In the unary operator, let's compute it right away -/
  | ret c (.unOp o k) v => match v.unOp o with
    | .error m => error c k .type m
    | .ok    v => ret c k v

  /- The binary operator is a bit more laborious. When returning from the
  evaluation of the first expression, we stack the result and call the
  evaluation of the second expression -/
  | ret c (.binOp₁ o e₂ k) v₁ => expr c (.binOp₂ o v₁ k) e₂
  
  /- Once the second evaluation is complete, we're good to go -/
  | ret c (.binOp₂ o v₁ k) v₂ => match v₁.binOp v₂ o with
    | .error m => error c k .type m
    | .ok    v => ret c k v

  /- `error` and `done` states just loop into themselves! -/
  | s@(error ..) => s
  | s@(done ..)  => s

/-- And now we can finally define our partial function to run a program using
`step`. It's really simple: call `step` until it yields a value or an error! -/
partial def Program.run (p : Program) : Context × Result :=
  let rec run' (s : State) : Context × Result :=
    match s.step with
    | .error c _ t m => (c, .err t m)
    | .done  c _ v   => (c, .val v)
    | s              => run' s
  run' $ State.prog default default p
