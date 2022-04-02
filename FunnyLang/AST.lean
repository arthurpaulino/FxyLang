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

  inductive Value
    | nil   : Value
    | bool  : Bool          → Value
    | int   : Int           → Value
    | float : Float         → Value
    | list  : Array Value   → Value
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
    | fail        : String     → Program
    deriving Inhabited, Repr

end

open Value Expression Program

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

  partial def valToString : Value → String
    | nil       => "nil"
    | .bool b   => toString b
    | int   i   => toString i
    | float f   => toString f
    | list  l   => toString $ l.map fun v => valToString v
    | str   s   => s
    | curry _ p => progToString p
    | error s   => s!"error: {s}"

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
    | fail        s     => s

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
  | Program.sequence _ p => p.lengthAux (n + 1)
  | _                    => n + 1

def Program.length (p : Program) : Nat :=
  p.lengthAux 0

def Value.add : Value → Value → Value
  | error s,  _        => error s
  | _,        error s  => error s
  | bool  bL, bool  bR => bool  $ bL || bR
  | str   sL, str   sR => str   $ sL ++ sR
  | int   iL, int   iR => int   $ iL +  iR
  | float fL, float fR => float $ fL +  fR
  | list  lL, list  lR => list  $ lL ++ lR
  | list  lL, vR       => list  $ lL.push vR
  | curry .., curry .. => error "can't sum functions"
  | l,        r        =>
    error s!"invalid application of '+' between\n{l}\nand\n{r}"

def Value.mul : Value → Value → Value
  | error s,  _        => error s
  | _,        error s  => error s
  | bool  bL, bool  bR => bool  $ bL && bR
  | int   iL, int   iR => int   $ iL *  iR
  | float fL, float fR => float $ fL *  fR
  | curry .., curry .. => error "can't multiply functions"
  | l,        r        =>
    error s!"invalid application of '*' between\n{l}\nand\n{r}"

def Value.lt : Value → Value → Value
  | error s,   _         => error s
  | _,         error s   => error s
  | str   sL,  str   sR  => bool $ sL < sR
  | int   iL,  int   iR  => bool $ iL < iR
  | float fL,  float fR  => bool $ fL < fR
  | list  lL,  list  lR  => bool $ lL.size < lR.size
  | curry _ p, curry _ q => bool $ p.length < q.length
  | l,         r         =>
    error s!"invalid application of '<' between\n{l}\nand\n{r}"

def Value.le : Value → Value → Value
  | error s,   _         => error s
  | _,         error s   => error s
  | str   sL,  str   sR  => bool $ sL < sR || sL == sR
  | int   iL,  int   iR  => bool $ iL ≤ iR
  | float fL,  float fR  => bool $ fL ≤ fR
  | list  lL,  list  lR  => bool $ lL.size ≤ lR.size
  | curry _ p, curry _ q => bool $ p.length ≤ q.length
  | l,         r         =>
    error s!"invalid application of '<=' between\n{l}\nand\n{r}"

def Value.gt : Value → Value → Value
  | error s,   _         => error s
  | _,         error s   => error s
  | str   sL,  str   sR  => bool $ sL > sR
  | int   iL,  int   iR  => bool $ iL > iR
  | float fL,  float fR  => bool $ fL > fR
  | list  lL,  list  lR  => bool $ lL.size > lR.size
  | curry _ p, curry _ q => bool $ p.length > q.length
  | l,         r         =>
    error s!"invalid application of '>' between\n{l}\nand\n{r}"

def Value.ge : Value → Value → Value
  | error s,   _         => error s
  | _,         error s   => error s
  | str   sL,  str   sR  => bool $ sL > sR || sL == sR
  | int   iL,  int   iR  => bool $ iL ≥ iR
  | float fL,  float fR  => bool $ fL ≥ fR
  | list  lL,  list  lR  => bool $ lL.size ≥ lR.size
  | curry _ p, curry _ q => bool $ p.length ≥ q.length
  | l,         r         =>
    error s!"invalid application of '<=' between\n{l}\nand\n{r}"

partial def Value.eq : Value → Value → Value
  | error s,   _       => error s
  | _,         error s => error s
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
  | curry .., curry .. => error "can't compare functions"
  | _,        _        => bool false

partial def Value.ne : Value → Value → Value
  | error s,   _       => error s
  | _,         error s => error s
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
  | curry .., curry .. => error "can't compare functions"
  | _,        _        => bool true

def cantEvalAsBool (v : Value) : String :=
  s!"can't evaluate as bool:\n{v}"

open NEList in
def consume (p : Program) :
    NEList String → NEList Expression → (Option (NEList String)) × Program
  | cons n ns, cons e es =>
    consume (sequence (attribution n (evaluation e)) p) ns es
  | cons n ns, uno  e    => (some ns, sequence (attribution n (evaluation e)) p)
  | uno  n,    uno  e    => (none, sequence (attribution n (evaluation e)) p)
  | uno  _,    cons _ _  => (none, fail "incompatible number of parameters")

abbrev Context := Std.HashMap String Value

protected def Context.toString (c : Context) : String :=
  (c.toList.foldl (init := "")
    fun acc (n, val) => acc ++ s!"{n}:\t{val}\n").trimRight

instance : ToString Context := ⟨Context.toString⟩

mutual

  partial def evaluate (ctx : Context) : Expression → Value
    | atom v     => v
    | var  n     => match ctx[n] with
      | none   => error s!"'{n}' not found"
      | some v => v
    | .not e => match evaluate ctx e with
      | .bool b => bool !b
      | v       => error $ cantEvalAsBool v
    | .add eL eR => (evaluate ctx eL).add $ evaluate ctx eR
    | .mul eL eR => (evaluate ctx eL).mul $ evaluate ctx eR
    | app  n  es => match ctx[n] with
      | none              => error s!"'{n}' not found"
      | some (curry ns p) =>
        let (ns?, p') := consume p ns es
        match ns? with
        | none    => (p'.run ctx).2 -- actually executing the function program
        | some ns => curry ns p' -- there are still arguments to be fulfille
      | _                 => error s!"'{n}' is not a function"
    | .eq eL eR  => (evaluate ctx eL).eq $ evaluate ctx eR
    | .ne eL eR  => (evaluate ctx eL).ne $ evaluate ctx eR
    | .lt eL eR  => (evaluate ctx eL).lt $ evaluate ctx eR
    | .le eL eR  => (evaluate ctx eL).le $ evaluate ctx eR
    | .gt eL eR  => (evaluate ctx eL).gt $ evaluate ctx eR
    | .ge eL eR  => (evaluate ctx eL).ge $ evaluate ctx eR

  partial def Program.run (ctx : Context := default) : Program → Context × Value
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
    | fail s         => (ctx, error s)

end
