/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import Std

/-- Non-empty list -/
inductive NEList (α : Type)
  | uno  : α → NEList α
  | cons : α → NEList α → NEList α
  deriving Repr

def List.toNEList [DecidableEq α] : (l : List α) → l ≠ [] → NEList α
  | [], h => by simp at h
  | a :: b, _ =>
    if h : b ≠ []
      then NEList.cons a $ b.toNEList h
      else NEList.uno a

mutual

  inductive Value
    | nil   : Value
    | bool  : Bool          → Value
    | int   : Int           → Value
    | float : Float         → Value
    | list  : Array  Value  → Value
    | str   : String        → Value
    | curry : NEList String → Program → Value
    deriving Repr, Inhabited

  inductive Expression
    | atom : Value      → Expression
    | var  : String     → Expression
    | not  : Expression → Expression
    | add  : Expression → Expression        → Expression
    | mul  : Expression → Expression        → Expression
    | app  : String     → NEList Expression → Expression

  inductive Program
    | skip        : Program
    | sequence    : Program    → Program → Program
    | attribution : String     → Program → Program
    | ifElse      : Expression → Program → Program → Program
    | whileLoop   : Expression → Program → Program
    | evaluation  : Expression → Program
    deriving Inhabited

end

abbrev Context := Std.HashMap String Value

def Value.add : Value → Value → Value
  | bool  bL, bool  bR => bool  $ bL || bR
  | str   sL, str   sR => str   $ sL ++ sR
  | int   iL, int   iR => int   $ iL +  iR
  | float fL, float fR => float $ fL +  fR
  | list  lL, list  lR => list  $ lL ++ lR
  | _,        _        => panic! "invalid application of '+'"

def Value.mul : Value → Value → Value
  | bool  bL, bool  bR => bool  $ bL && bR
  | int   iL, int   iR => int   $ iL *  iR
  | float fL, float fR => float $ fL *  fR
  | _,        _        => panic! "invalid application of '*'"

def cantEvalAsBool := "can't evaluate as boolean"

open Value Program

def consume (p : Program) :
    NEList String → NEList Expression → (Option (NEList String)) × Program
  | NEList.cons n ns, NEList.cons e es =>
    consume (sequence (attribution n (evaluation e)) p) ns es
  | NEList.cons n ns, NEList.uno e     =>
    (some ns, sequence (attribution n (evaluation e)) p)
  | NEList.uno n,     NEList.uno e     =>
    (none, sequence (attribution n (evaluation e)) p)
  | NEList.uno _,     NEList.cons _ _  =>
    panic! "incompatible number of parameters"

mutual

  partial def evaluate (ctx : Context) : Expression → Value
    | Expression.atom v    => v
    | Expression.var n     => match ctx[n] with
      | none   => panic! s!"'{n}' not found"
      | some v => v
    | Expression.not e => match evaluate ctx e with
      | Value.bool b => bool !b
      | _            => panic! cantEvalAsBool
    | Expression.add eL eR => (evaluate ctx eL).add $ evaluate ctx eR
    | Expression.mul eL eR => (evaluate ctx eL).mul $ evaluate ctx eR
    | Expression.app n es  => match ctx[n] with
      | none   => panic! s!"'{n}' not found"
      | some v => match v with
        | curry ns p =>
          let (ns?, p') := consume p ns es
          match ns? with
          | none => (p'.run ctx).2 -- actually executing the function program
          | some ns => curry ns p' -- there are still arguments to be fulfille
        | _ => panic! s!"'{n}' is not a function"

  partial def Program.run (ctx : Context) : Program → Context × Value
    | skip           => (ctx, nil)
    | sequence p₁ p₂ => p₂.run (p₁.run ctx).1
    | attribution name p => (ctx.insert name (p.run ctx).2, nil)
    | ifElse e pT pF => match evaluate ctx e with
      | Value.bool b => if b then pT.run ctx else pF.run ctx
      | _            => panic! cantEvalAsBool
    | whileLoop e p  => match evaluate ctx e with
      | Value.bool b => if !b then (ctx, nil) else
        (Program.whileLoop e p).run (p.run ctx).1
      | _            => panic! cantEvalAsBool
    | evaluation e   => (ctx, (evaluate ctx e))

end
