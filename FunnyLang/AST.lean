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

def List.unfoldStrings (l : List String) : String :=
  l.foldl (init := "") $ fun acc a => acc ++ s!" {a}" |>.trimLeft

mutual

  inductive Value
    | nil   : Value
    | bool  : Bool          → Value
    | int   : Int           → Value
    | float : Float         → Value
    | list  : Array  Value  → Value
    | str   : String        → Value
    | curry : NEList String → Program → Value
    | error : String        → Value
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
    | err         : String     → Program
    deriving Inhabited, Repr

end

open Value Expression Program

def Program.getCurryNames? : Program → Option (NEList String)
  | evaluation (atom (curry ns _))                              => some ns
  | sequence (attribution _ (evaluation (atom (curry ns _)))) _ => some ns
  | _                                                           => none

def nSpaces (n : Nat) : String := Id.run do
  let mut s := ""
  for i in [0:n] do
    s := s ++ " "
  s

def Program.lengthAux (n : Nat) : Program → Nat
  | Program.sequence _ q => q.lengthAux (n + 1)
  | _ => n + 1

def Program.length (p : Program) : Nat :=
  p.lengthAux 0

mutual

  partial def valToString : Value → String
    | nil => "nil"
    | Value.bool b => toString b
    | int i => toString i
    | float f => toString f
    | list l => toString $ l.map fun v => valToString v
    | str s => s
    | curry _ p => progToString p
    | error s => s

  partial def unfoldExpressions (es : NEList Expression) : String :=
    (es.toList.map fun e => expToString e).unfoldStrings

  partial def expToString : Expression → String
    | atom v => valToString v
    | var n  => n
    | Expression.not e => s!"(! {expToString e})"
    | add l r => s!"({expToString l} + {expToString r})"
    | mul l r => s!"({expToString l} * {expToString r})"
    | app n es => s!"{n} {unfoldExpressions es}"
    | eq l r => s!"({expToString l} = {expToString r})"
    | ne l r => s!"({expToString l} != {expToString r})"
    | lt l r => s!"({expToString l} < {expToString r})"
    | le l r => s!"({expToString l} <= {expToString r})"
    | gt l r => s!"({expToString l} > {expToString r})"
    | ge l r => s!"({expToString l} >= {expToString r})"

  partial def progToStringAux (l : Nat) : Program → String
    | skip => s!"{nSpaces l}skip"
    | sequence p q => s!"{nSpaces (l-2)}{progToStringAux l p}\n{progToStringAux l q}"
    | attribution n p =>
      let pString := if p.length > 1 then s!"\n{progToStringAux (l+2) p}" else s!" {progToStringAux (l-2) p}"
      match p.getCurryNames? with
      | none    => s!"{nSpaces l}{n} :=" ++ pString
      | some ns => s!"{nSpaces l}{n} {ns.toList.unfoldStrings} :=" ++ pString
    | evaluation e => s!"{nSpaces l}{expToString e}"
    | whileLoop e p => s!"{nSpaces l}while {expToString e} do\n{progToStringAux (l+2) p}"
    | ifElse e p q =>
      s!"{nSpaces l}if {expToString e} then\n{progToStringAux (l+2) p}\nelse\n{progToStringAux (l+2) q}"
    | err s => s

  partial def progToString (p : Program) : String :=
    progToStringAux 0 p

end

instance : ToString Value      := ⟨valToString⟩
instance : ToString Expression := ⟨expToString⟩
instance : ToString Program    := ⟨progToString⟩

abbrev Context := Std.HashMap String Value

protected def Context.toString (c : Context) : String :=
  (c.toList.foldl (init := "")
    fun acc (n, val) => acc ++ s!"{n}:\t{val}\n").trimRight

instance : ToString Context := ⟨Context.toString⟩

def Value.add : Value → Value → Value
  | bool  bL, bool  bR => bool  $ bL || bR
  | str   sL, str   sR => str   $ sL ++ sR
  | int   iL, int   iR => int   $ iL +  iR
  | float fL, float fR => float $ fL +  fR
  | list  lL, list  lR => list  $ lL ++ lR
  | _,        _        => error "invalid application of '+'"

def Value.mul : Value → Value → Value
  | bool  bL, bool  bR => bool  $ bL && bR
  | int   iL, int   iR => int   $ iL *  iR
  | float fL, float fR => float $ fL *  fR
  | _,        _        => error "invalid application of '*'"

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
  | _,        _        => error "invalid application of '=' or '!='"

def Value.lt : Value → Value → Value
  | str   sL, str   sR => bool $ sL < sR
  | int   iL, int   iR => bool $ iL < iR
  | float fL, float fR => bool $ fL < fR
  | list  lL, list  lR => bool $ lL.size < lR.size
  | _,        _        => error "invalid application of '<'"

def Value.le : Value → Value → Value
  | str   sL, str   sR => bool $ sL < sR || sL == sR
  | int   iL, int   iR => bool $ iL ≤ iR
  | float fL, float fR => bool $ fL ≤ fR
  | list  lL, list  lR => bool $ lL.size ≤ lR.size
  | _,        _        => error "invalid application of '<='"

def Value.gt : Value → Value → Value
  | str   sL, str   sR => bool $ sL > sR
  | int   iL, int   iR => bool $ iL > iR
  | float fL, float fR => bool $ fL > fR
  | list  lL, list  lR => bool $ lL.size > lR.size
  | _,        _        => error "invalid application of '>'"

def Value.ge : Value → Value → Value
  | str   sL, str   sR => bool $ sL > sR || sL == sR
  | int   iL, int   iR => bool $ iL ≥ iR
  | float fL, float fR => bool $ fL ≥ fR
  | list  lL, list  lR => bool $ lL.size ≥ lR.size
  | _,        _        => error "invalid application of '>='"

def cantEvalAsBool (v : Value) := s!"can't evaluate {v} as boolean"

def consume (p : Program) :
    NEList String → NEList Expression → (Option (NEList String)) × Program
  | NEList.cons n ns, NEList.cons e es =>
    consume (sequence (attribution n (evaluation e)) p) ns es
  | NEList.cons n ns, NEList.uno e     =>
    (some ns, sequence (attribution n (evaluation e)) p)
  | NEList.uno n,     NEList.uno e     =>
    (none, sequence (attribution n (evaluation e)) p)
  | NEList.uno _,     NEList.cons _ _  =>
    (none, err "incompatible number of parameters")

mutual

  partial def evaluate (ctx : Context) : Expression → Value
    | Expression.atom v    => v
    | Expression.var n     => match ctx[n] with
      | none   => error s!"'{n}' not found"
      | some v => v
    | Expression.not e => match evaluate ctx e with
      | Value.bool b => bool !b
      | v            => error $ cantEvalAsBool v
    | Expression.add eL eR => (evaluate ctx eL).add $ evaluate ctx eR
    | Expression.mul eL eR => (evaluate ctx eL).mul $ evaluate ctx eR
    | Expression.app n es  => match ctx[n] with
      | none   => error s!"'{n}' not found"
      | some v => match v with
        | curry ns p =>
          let (ns?, p') := consume p ns es
          match ns? with
          | none => (p'.run ctx).2 -- actually executing the function program
          | some ns => curry ns p' -- there are still arguments to be fulfille
        | _ => error s!"'{n}' is not a function"
    | Expression.eq eL eR => (evaluate ctx eL).eq $ evaluate ctx eR
    | Expression.ne eL eR => match (evaluate ctx eL).eq $ evaluate ctx eR with
      | Value.bool b => bool !b
      | v            => error $ cantEvalAsBool v
    | Expression.lt eL eR => (evaluate ctx eL).lt $ evaluate ctx eR
    | Expression.le eL eR => (evaluate ctx eL).le $ evaluate ctx eR
    | Expression.gt eL eR => (evaluate ctx eL).gt $ evaluate ctx eR
    | Expression.ge eL eR => (evaluate ctx eL).ge $ evaluate ctx eR

  partial def Program.run (ctx : Context) : Program → Context × Value
    | skip           => (ctx, nil)
    | sequence p₁ p₂ =>
      let res := p₁.run ctx
      match res.2 with
      | error _ => res
      | _       => p₂.run res.1
    | attribution name p =>
      let res := p.run ctx
      match res.2 with
      | error _ => res
      | _       => (ctx.insert name res.2, nil)
    | ifElse e pT pF => match evaluate ctx e with
      | Value.bool b => if b then pT.run ctx else pF.run ctx
      | v            => (ctx, error $ cantEvalAsBool v)
    | whileLoop e p  => match evaluate ctx e with
      | Value.bool b => if !b then (ctx, nil) else
        (Program.whileLoop e p).run (p.run ctx).1
      | v            => (ctx, error $ cantEvalAsBool v)
    | evaluation e   => (ctx, (evaluate ctx e))
    | err s          => (ctx, error s)

end
