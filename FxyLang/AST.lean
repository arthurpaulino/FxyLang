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

def List.toNEList (a : α) : List α → NEList α
  | []      => .uno a
  | b :: bs => .cons a (toNEList b bs)

def NEList.toList : NEList α → List α
  | uno  a   => [a]
  | cons a b => a :: b.toList

def isEq : NEList α → List α → Prop
  | .cons a as, b :: bs => a = b ∧ isEq as bs
  | .uno  a   , [b]     => a = b
  | _,          _       => False

theorem ListToNEListIsEqList {a : α} {as : List α} :
    isEq (as.toNEList a) (a :: as) := by
  induction as with
  | nil            => rw [List.toNEList, isEq]
  | cons a' as' hi =>
    cases as' with
    | nil      => simp only [List.toNEList, isEq]
    | cons _ _ =>
      simp [List.toNEList, isEq] at hi ⊢
      exact hi

theorem NEListToListEqList {a : α} {as : List α} :
    (as.toNEList a).toList = a :: as := by
  induction as with
  | nil           => rw [List.toNEList, NEList.toList]
  | cons _ as' hi =>
    cases as' with
    | nil      => simp only [List.toNEList, NEList.toList]
    | cons _ _ =>
      simp [List.toNEList, NEList.toList] at hi ⊢
      exact hi

def List.unfoldStrings (l : List String) : String :=
  l.foldl (init := "") $ fun acc a => acc ++ s!" {a}" |>.trimLeft

mutual

  inductive Halting
    | err : String  → Halting
    | brk : Halting

  inductive Value
    | nil   : Value
    | bool  : Bool          → Value
    | int   : Int           → Value
    | float : Float         → Value
    | list  : Array Value   → Value
    | str   : String        → Value
    | curry : NEList String → Program → Value
    | haltV : Halting       → Value
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
    deriving Repr

  inductive Program
    | skip        : Program
    | sequence    : Program    → Program → Program
    | attribution : String     → Program → Program
    | ifElse      : Expression → Program → Program → Program
    | whileLoop   : Expression → Program → Program
    | evaluation  : Expression → Program
    | halt        : Halting    → Program
    deriving Inhabited, Repr

end

open Halting Value Expression Program

def Program.getCurryNames? : Program → Option (NEList String)
  | evaluation (atom (curry ns _))                              => some ns
  | sequence (attribution _ (evaluation (atom (curry ns _)))) _ => some ns
  | _                                                           => none

def Program.isSequence : Program → Bool
  | sequence .. => true
  | _           => false

def blankAux (cs : List Char) : Nat → List Char
  | 0     => cs
  | n + 1 => ' ' :: ' ' :: (blankAux cs n)

def blank (n : Nat) : String :=
  ⟨blankAux [] n⟩

mutual

  partial def haltToString : Halting → String
    | err s => s!"error: {s}"
    | brk   => unreachable!

  partial def valToString : Value → String
    | nil       => "nil"
    | .bool b   => toString b
    | int   i   => toString i
    | float f   => toString f
    | list  l   => toString $ l.map fun v => valToString v
    | str   s   => s
    | curry _ p => progToString p
    | haltV h   => haltToString h

  partial def unfoldExpressions (es : NEList Expression) : String :=
    (es.toList.map fun e => expToString e).unfoldStrings

  partial def expToString : Expression → String
    | atom v    => valToString v
    | var  n    => n
    | .not e    => s!"(! {expToString e})"
    | app  n es => s!"({n} {unfoldExpressions es})"
    | add  l r  => s!"({expToString l} + {expToString r})"
    | mul  l r  => s!"({expToString l} * {expToString r})"
    | eq   l r  => s!"({expToString l} = {expToString r})"
    | ne   l r  => s!"({expToString l} != {expToString r})"
    | lt   l r  => s!"({expToString l} < {expToString r})"
    | le   l r  => s!"({expToString l} <= {expToString r})"
    | gt   l r  => s!"({expToString l} > {expToString r})"
    | ge   l r  => s!"({expToString l} >= {expToString r})"

  partial def progToStringAux (l : Nat) : Program → String
    | skip              => s!"{blank l}skip"
    | sequence    p q   =>
      s!"{blank (l-2)}{progToStringAux l p}\n{progToStringAux l q}"
    | attribution n p   =>
      let pString := if p.isSequence
        then s!"\n{progToStringAux (l+2) p}"
        else s!" {progToStringAux (l-2) p}"
      match p.getCurryNames? with
      | none    => s!"{blank l}{n} :=" ++ pString
      | some ns => s!"{blank l}{n} {ns.toList.unfoldStrings} :=" ++ pString
    | evaluation  e     => s!"{blank l}{expToString e}"
    | whileLoop   e p   =>
      s!"{blank l}while {expToString e} do\n{progToStringAux (l+2) p}"
    | ifElse      e p q =>
      s!"{blank l}if {expToString e} then\n{progToStringAux (l+2) p}\n" ++
        s!"else\n{progToStringAux (l+2) q}"
    | .halt       h     => haltToString h

  partial def progToString (p : Program) : String :=
    progToStringAux 0 p

end

def Value.toString      (v : Value)      : String := valToString  v
def Expression.toString (e : Expression) : String := expToString  e
def Program.toString    (p : Program)    : String := progToString p

instance : ToString Value      := ⟨toString⟩
instance : ToString Expression := ⟨toString⟩
instance : ToString Program    := ⟨toString⟩

def Program.lengthAux (n : Nat) : Program → Nat
  | sequence _ p => p.lengthAux (n + 1)
  | _            => n + 1

def Program.length (p : Program) : Nat :=
  p.lengthAux 0

def Value.add : Value → Value → Value
  | haltV h,  _        => haltV h
  | _,        haltV h  => haltV h
  | bool  bL, bool  bR => bool  $ bL || bR
  | str   sL, str   sR => str   $ sL ++ sR
  | int   iL, int   iR => int   $ iL +  iR
  | float fL, float fR => float $ fL +  fR
  | list  lL, list  lR => list  $ lL ++ lR
  | list  lL, vR       => list  $ lL.push vR
  | curry .., curry .. => haltV $ .err "can't sum functions"
  | l,        r        =>
    haltV $ .err s!"invalid application of '+' between\n{l}\nand\n{r}"

def Value.mul : Value → Value → Value
  | haltV h,  _        => haltV h
  | _,        haltV h  => haltV h
  | bool  bL, bool  bR => bool  $ bL && bR
  | int   iL, int   iR => int   $ iL *  iR
  | float fL, float fR => float $ fL *  fR
  | curry .., curry .. => haltV $ .err "can't multiply functions"
  | l,        r        =>
    haltV $ .err s!"invalid application of '*' between\n{l}\nand\n{r}"

def Value.lt : Value → Value → Value
  | haltV h,   _         => haltV h
  | _,         haltV h   => haltV h
  | str   sL,  str   sR  => bool $ sL < sR
  | int   iL,  int   iR  => bool $ iL < iR
  | float fL,  float fR  => bool $ fL < fR
  | list  lL,  list  lR  => bool $ lL.size < lR.size
  | curry _ p, curry _ q => bool $ p.length < q.length
  | l,         r         =>
    haltV $ .err s!"invalid application of '<' between\n{l}\nand\n{r}"

def Value.le : Value → Value → Value
  | haltV h,   _         => haltV h
  | _,         haltV h   => haltV h
  | str   sL,  str   sR  => bool $ sL < sR || sL == sR
  | int   iL,  int   iR  => bool $ iL ≤ iR
  | float fL,  float fR  => bool $ fL ≤ fR
  | list  lL,  list  lR  => bool $ lL.size ≤ lR.size
  | curry _ p, curry _ q => bool $ p.length ≤ q.length
  | l,         r         =>
    haltV $ .err s!"invalid application of '<=' between\n{l}\nand\n{r}"

def Value.gt : Value → Value → Value
  | haltV h,   _         => haltV h
  | _,         haltV h   => haltV h
  | str   sL,  str   sR  => bool $ sL > sR
  | int   iL,  int   iR  => bool $ iL > iR
  | float fL,  float fR  => bool $ fL > fR
  | list  lL,  list  lR  => bool $ lL.size > lR.size
  | curry _ p, curry _ q => bool $ p.length > q.length
  | l,         r         =>
    haltV $ .err s!"invalid application of '>' between\n{l}\nand\n{r}"

def Value.ge : Value → Value → Value
  | haltV h,   _         => haltV h
  | _,         haltV h   => haltV h
  | str   sL,  str   sR  => bool $ sL > sR || sL == sR
  | int   iL,  int   iR  => bool $ iL ≥ iR
  | float fL,  float fR  => bool $ fL ≥ fR
  | list  lL,  list  lR  => bool $ lL.size ≥ lR.size
  | curry _ p, curry _ q => bool $ p.length ≥ q.length
  | l,         r         =>
    haltV $ .err s!"invalid application of '<=' between\n{l}\nand\n{r}"

partial def Value.eq : Value → Value → Value
  | haltV h,  _        => haltV h
  | _,        haltV h  => haltV h
  | nil,      nil      => bool true
  | bool  bL, bool  bR => bool $ bL =  bR
  | str   sL, str   sR => bool $ sL =  sR
  | int   iL, int   iR => bool $ iL =  iR
  | float fL, float fR => bool $ fL == fR
  | list  lL, list  lR => bool $
    if lL.size = lR.size then
      lL.zip lR |>.foldl (init := true) $ fun acc (l, r) =>
        acc && match l.eq r with | bool true => true | _ => false
    else false
  | curry .., curry .. => haltV $ .err "can't compare functions"
  | _,        _        => bool false

partial def Value.ne : Value → Value → Value
  | haltV h,  _        => haltV h
  | _,        haltV h  => haltV h
  | nil,      nil      => bool false
  | bool  bL, bool  bR => bool $ bL ≠ bR
  | str   sL, str   sR => bool $ sL ≠ sR
  | int   iL, int   iR => bool $ iL ≠ iR
  | float fL, float fR => bool $ !(fL == fR)
  | list  lL, list  lR => bool $
    if lL.size = lR.size then
      lL.zip lR |>.foldl (init := false) $ fun acc (l, r) =>
        acc || match l.ne r with | bool true => true | _ => false
    else true
  | curry .., curry .. => haltV $ .err "can't compare functions"
  | _,        _        => bool true

open NEList in
def consume (p : Program) :
    NEList String → NEList Expression → (Option (NEList String)) × Program
  | cons n ns, cons e es =>
    consume (sequence (attribution n (evaluation e)) p) ns es
  | cons n ns, uno  e    => (some ns, sequence (attribution n (evaluation e)) p)
  | uno  n,    uno  e    => (none, sequence (attribution n (evaluation e)) p)
  | uno  _,    cons _ _  =>
    (none, halt $ .err "incompatible number of parameters")

abbrev Context := Std.HashMap String Value

protected def Context.toString (c : Context) : String :=
  (c.toList.foldl (init := "")
    fun acc (n, val) => acc ++ s!"{n}:\t{val}\n").trimRight

instance : ToString Context := ⟨Context.toString⟩

structure State where
  ctx     : Context
  inWhile : Bool
  deriving Inhabited

def State.new : State :=
  ⟨default, false⟩

def State.getOp (self : State) (idx : String) : Option Value :=
  self.ctx[idx]

def State.with (self : State) (idx : String) (value : Value) : State :=
  ⟨self.ctx.insert idx value, self.inWhile⟩

def State.toWhile (self : State) (isWhile : Bool := true) : State :=
  { self with inWhile := isWhile }

def cantEvalAsBool (v : Value) : String :=
  s!"can't evaluate as bool:\n{v}"

def cantUseBreak : String := "can't use break outside of a `while` loop"

mutual

  partial def evaluate (stt : State) : Expression → Value
    | atom v     => v
    | var  n     => match stt[n] with
      | none   => haltV $ .err s!"'{n}' not found"
      | some v => v
    | .not e     => match evaluate stt e with
      | .bool b => bool !b
      | v       => haltV $ .err $ cantEvalAsBool v
    | app  n es  => match stt[n] with
      | none              => haltV $ .err s!"'{n}' not found"
      | some (curry ns p) => match consume p ns es with
        | (none,    p) => (p.run stt).2
        | (some ns, p) => curry ns p
      | _        => haltV $ .err s!"'{n}' is not a function"
    | .add eL eR => (evaluate stt eL).add $ evaluate stt eR
    | .mul eL eR => (evaluate stt eL).mul $ evaluate stt eR
    | .eq  eL eR => (evaluate stt eL).eq  $ evaluate stt eR
    | .ne  eL eR => (evaluate stt eL).ne  $ evaluate stt eR
    | .lt  eL eR => (evaluate stt eL).lt  $ evaluate stt eR
    | .le  eL eR => (evaluate stt eL).le  $ evaluate stt eR
    | .gt  eL eR => (evaluate stt eL).gt  $ evaluate stt eR
    | .ge  eL eR => (evaluate stt eL).ge  $ evaluate stt eR

  partial def Program.run (stt : State) : Program → State × Value
    | skip           => (stt, nil)
    | sequence p₁ p₂ =>
      let res := p₁.run stt
      match res.2 with
      | haltV _ => res
      | _       => p₂.run res.1
    | attribution n p =>
      let v := (p.run stt).2
      match v with
      | haltV _ => (stt, v)
      | v       => (stt.with n v, nil)
    | ifElse e pT pF => match evaluate stt e with
      | .bool b => if b then pT.run stt else pF.run stt
      | v            => (stt, haltV $ .err $ cantEvalAsBool v)
    | whileLoop e p  => match evaluate stt e with
      | .bool b =>
        if !b then (stt, nil) else
          match p.run stt.toWhile with
          | (stt', haltV brk) => (stt'.toWhile stt.inWhile, nil)
          | (stt', haltV h)   => (stt'.toWhile stt.inWhile, haltV h)
          | (stt', _)         => (whileLoop e p).run $ stt'.toWhile stt.inWhile
      | v       => (stt, haltV $ .err $ cantEvalAsBool v)
    | evaluation e   => (stt, (evaluate stt e))
    | halt brk       =>
      if stt.inWhile
        then (stt, haltV brk)
        else (stt, haltV $ err cantUseBreak)
    | halt h => (stt, haltV h)

end

mutual

  partial def evaluateIO (stt : State) : Expression → IO Value
    | atom v     => return v
    | var  n     => return match stt[n] with
      | none   => haltV $ .err s!"'{n}' not found"
      | some v => v
    | .not e     => return match ← evaluateIO stt e with
      | .bool b => bool !b
      | v       => haltV $ .err $ cantEvalAsBool v
    | app  n es  => match stt[n] with
      | none              => return haltV $ .err s!"'{n}' not found"
      | some (curry ns p) => match consume p ns es with
        | (none   , p) => return (← p.runIO stt).2
        | (some ns, p) => return curry ns p
      | _        => return haltV $ .err s!"'{n}' is not a function"
    | .add eL eR => return (← evaluateIO stt eL).add $ ← evaluateIO stt eR
    | .mul eL eR => return (← evaluateIO stt eL).mul $ ← evaluateIO stt eR
    | .eq  eL eR => return (← evaluateIO stt eL).eq  $ ← evaluateIO stt eR
    | .ne  eL eR => return (← evaluateIO stt eL).ne  $ ← evaluateIO stt eR
    | .lt  eL eR => return (← evaluateIO stt eL).lt  $ ← evaluateIO stt eR
    | .le  eL eR => return (← evaluateIO stt eL).le  $ ← evaluateIO stt eR
    | .gt  eL eR => return (← evaluateIO stt eL).gt  $ ← evaluateIO stt eR
    | .ge  eL eR => return (← evaluateIO stt eL).ge  $ ← evaluateIO stt eR

  partial def Program.runIO (stt : State) :
      Program → IO (State × Value)
    | skip           => return (stt, nil)
    | sequence p₁ p₂ => do
      let res ← p₁.runIO stt
      match res.2 with
      | haltV _ => return res
      | _       => p₂.runIO res.1
    | attribution n p => do
      let v := (← p.runIO stt).2
      match v with
      | haltV _ => return (stt, v)
      | v       => return (stt.with n v, nil)
    | ifElse e pT pF => do match ← evaluateIO stt e with
      | .bool b => if b then pT.runIO stt else pF.runIO stt
      | v       => return (stt, haltV $ .err $ cantEvalAsBool v)
    | whileLoop e p  => do match ← evaluateIO stt e with
      | .bool b => do
        if !b then return (stt, nil) else
          return match ← p.runIO stt.toWhile with
          | (stt', haltV brk) => (stt'.toWhile stt.inWhile, nil)
          | (stt', haltV h)   => (stt'.toWhile stt.inWhile, haltV h)
          | (stt', _)         => (whileLoop e p).run $ stt'.toWhile stt.inWhile
      | v            => return (stt, haltV $ .err $ cantEvalAsBool v)
    | evaluation e   => return (stt, (← evaluateIO stt e))
    | halt brk       =>
      if stt.inWhile
        then return (stt, haltV brk)
        else return (stt, haltV $ err cantUseBreak)
    | halt h => return (stt, haltV h)

end

def Program.run! (p : Program) : Context × Value :=
  let r := p.run State.new
  (r.1.ctx, r.2)

def Program.runIO! (p : Program) : IO (Context × Value) := do
  let r ← p.runIO State.new
  return (r.1.ctx, r.2)
