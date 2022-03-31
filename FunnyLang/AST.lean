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

def List.toNEList : (l : List α) → ¬ l.isEmpty → NEList α
  | [], h => by simp [isEmpty] at h
  | a :: b, _ =>
    if h : ¬ b.isEmpty
      then NEList.cons a $ b.toNEList h
      else NEList.uno a

def NEList.toList : NEList α → List α
  | uno a    => [a]
  | cons a b => a :: b.toList

protected def NEList.toString [ToString α] (l : NEList α) : String :=
  l.toList.foldl (init := "") $ fun acc a => acc ++ s!" {a}" |>.trimLeft

instance [ToString α] : ToString (NEList α) := ⟨NEList.toString⟩

mutual

  inductive Value
    | nil   : Value
    | bool  : Bool          → Value
    | int   : Int           → Value
    | float : Float         → Value
    | list  : Array  Value  → Value
    | str   : String        → Value
    | curry : NEList String → Program → Value
    deriving Inhabited, Repr

  inductive Expression
    | atom : Value      → Expression
    | var  : String     → Expression
    | not  : Expression → Expression
    | add  : Expression → Expression        → Expression
    | mul  : Expression → Expression        → Expression
    | app  : String     → NEList Expression → Expression
    | eq   : Expression → Expression        → Expression
    | ne   : Expression → Expression        → Expression
    | lt   : Expression → Expression        → Expression
    | le   : Expression → Expression        → Expression
    | gt   : Expression → Expression        → Expression
    | ge   : Expression → Expression        → Expression
    deriving Inhabited, Repr

  inductive Program
    | skip        : Program
    | sequence    : Program    → Program → Program
    | attribution : String     → Program → Program
    | ifElse      : Expression → Program → Program → Program
    | whileLoop   : Expression → Program → Program
    | evaluation  : Expression → Program
    deriving Inhabited, Repr

end

protected partial def Value.toString : Value → String
  | nil => "nil"
  | bool b => toString b
  | int i => toString i
  | float f => toString f
  | list l => toString $ l.map fun v => Value.toString v
  | str s => s
  | curry _ _ => "uncuried function"

instance : ToString Value := ⟨Value.toString⟩

partial def Expression.toString : Expression → String
  | atom v => v.toString
  | var n  => n
  | not e => s!"(! {e.toString})"
  | add l r => s!"({l.toString} + {r.toString})"
  | mul l r => s!"({l.toString} * {r.toString})"
  | app n es =>
    let q := es.toList.map fun e => e.toString
    let q := q.foldl (init := "") $ fun acc a => acc ++ s!" {a}" |>.trimLeft
    s!"{n} {q}"
  | eq l r => s!"({l.toString} = {r.toString})"
  | ne l r => s!"({l.toString} != {r.toString})"
  | lt l r => s!"({l.toString} < {r.toString})"
  | le l r => s!"({l.toString} <= {r.toString})"
  | gt l r => s!"({l.toString} > {r.toString})"
  | ge l r => s!"({l.toString} >= {r.toString})"

instance : ToString Expression := ⟨Expression.toString⟩

def nSpaces (n : Nat) : String := Id.run do
  let mut s := ""
  for i in [0:n] do
    s := s ++ " "
  s

partial def Program.lengthAux (n : Nat) : Program → Nat
  | Program.sequence _ q => q.lengthAux (n + 1)
  | _ => n + 1

partial def Program.length (p : Program) : Nat :=
  p.lengthAux 0

partial def Program.toStringAux (l : Nat) : Program → String
  | skip => s!"{nSpaces l}skip"
  | sequence p q => s!"{nSpaces l}{p.toStringAux l};\n{q.toStringAux l}"
  | attribution n p => s!"{nSpaces l}{n} :=\n{p.toStringAux (l+2)}"
  | evaluation e => s!"{nSpaces l}{e}"
  | whileLoop e p => s!"{nSpaces l}while {e} do\n{p.toStringAux (l+2)}"
  | ifElse e p q =>
    s!"{nSpaces l}if {e} then\n{p.toStringAux (l+2)}\nelse\n{q.toStringAux (l+2)}"

partial def Program.toString (p : Program) : String :=
  p.toStringAux 0

instance : ToString Program := ⟨Program.toString⟩

abbrev Context := Std.HashMap String Value

protected def Context.toString (c : Context) : String :=
  (c.toList.foldl (init := "")
    fun acc (var, val) => acc ++ s!"{var}:\t{val}\n").trimRight

instance : ToString Context := ⟨Context.toString⟩

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

partial def Value.eq : Value → Value → Value
  | bool  bL, bool  bR => bool $ bL = bR
  | str   sL, str   sR => bool $ sL = sR
  | int   iL, int   iR => bool $ iL = iR
  | float fL, float fR => bool $ fL == fR
  | list  lL, list  lR => bool $
    if lL.size = lR.size then
      lL.zip lR |>.foldl (init := true) $ fun acc (l, r) =>
        acc && match l.eq r with | bool true => true | _ => false
    else false
  | _,        _        => panic! "invalid application of '=' or '!='"

def Value.lt : Value → Value → Value
  | str   sL, str   sR => bool $ sL < sR
  | int   iL, int   iR => bool $ iL < iR
  | float fL, float fR => bool $ fL < fR
  | list  lL, list  lR => bool $ lL.size < lR.size
  | _,        _        => panic! "invalid application of '<'"

def Value.le : Value → Value → Value
  | str   sL, str   sR => bool $ sL < sR || sL == sR
  | int   iL, int   iR => bool $ iL ≤ iR
  | float fL, float fR => bool $ fL ≤ fR
  | list  lL, list  lR => bool $ lL.size ≤ lR.size
  | _,        _        => panic! "invalid application of '<='"

def Value.gt : Value → Value → Value
  | str   sL, str   sR => bool $ sL > sR
  | int   iL, int   iR => bool $ iL > iR
  | float fL, float fR => bool $ fL > fR
  | list  lL, list  lR => bool $ lL.size > lR.size
  | _,        _        => panic! "invalid application of '>'"

def Value.ge : Value → Value → Value
  | str   sL, str   sR => bool $ sL > sR || sL == sR
  | int   iL, int   iR => bool $ iL ≥ iR
  | float fL, float fR => bool $ fL ≥ fR
  | list  lL, list  lR => bool $ lL.size ≥ lR.size
  | _,        _        => panic! "invalid application of '>='"

def cantEvalAsBool (v : Value) := s!"can't evaluate {v} as boolean"

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
      | v            => panic! cantEvalAsBool v
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
    | Expression.eq eL eR => (evaluate ctx eL).eq $ evaluate ctx eR
    | Expression.ne eL eR => match (evaluate ctx eL).eq $ evaluate ctx eR with
      | Value.bool b => bool !b
      | v            => panic! cantEvalAsBool v
    | Expression.lt eL eR => (evaluate ctx eL).lt $ evaluate ctx eR
    | Expression.le eL eR => (evaluate ctx eL).le $ evaluate ctx eR
    | Expression.gt eL eR => (evaluate ctx eL).gt $ evaluate ctx eR
    | Expression.ge eL eR => (evaluate ctx eL).ge $ evaluate ctx eR

  partial def Program.run (ctx : Context) : Program → Context × Value
    | skip           => (ctx, nil)
    | sequence p₁ p₂ => p₂.run (p₁.run ctx).1
    | attribution name p => (ctx.insert name (p.run ctx).2, nil)
    | ifElse e pT pF => match evaluate ctx e with
      | Value.bool b => if b then pT.run ctx else pF.run ctx
      | v            => panic! cantEvalAsBool v
    | whileLoop e p  => match evaluate ctx e with
      | Value.bool b => if !b then (ctx, nil) else
        (Program.whileLoop e p).run (p.run ctx).1
      | v            => panic! cantEvalAsBool v
    | evaluation e   => (ctx, (evaluate ctx e))

end
