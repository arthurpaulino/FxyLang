/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import Std

def List.unfoldStrings (l : List String) : String :=
  l.foldl (init := "") $ fun acc a => acc ++ s!" {a}" |>.trimLeft

def List.noDup [BEq α] : List α → Bool
  | []      => true
  | a :: as => ¬as.contains a && as.noDup

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

def NEList.contains [BEq α] : NEList α → α → Bool
  | uno a,     x => a == x
  | cons a as, x => a == x || as.contains x

def NEList.noDup [BEq α] : NEList α → Bool
  | uno a => true
  | cons a as => ¬as.contains a && as.noDup

theorem ListToNEListIsEqList {a : α} {as : List α} :
    isEq (as.toNEList a) (a :: as) := by
  induction as with
  | nil            => simp only [isEq]
  | cons a' as' hi =>
    cases as' with
    | nil      => simp only [isEq]
    | cons _ _ => simp [isEq] at hi ⊢; exact hi

theorem NEListToListEqList {a : α} {as : List α} :
    (as.toNEList a).toList = a :: as := by
  induction as with
  | nil           => simp only [NEList.toList]
  | cons _ as' hi =>
    cases as' with
    | nil      => simp only [NEList.toList]
    | cons _ _ => simp [NEList.toList] at hi ⊢; exact hi

theorem eqIffBEq [BEq α] [LawfulBEq α] {a b : α} : a == b ↔ a = b := by
  constructor
  · intro h; exact eq_of_beq h
  · intro h; simp [h]

theorem eqRfl [BEq α] {a x : α} : a = x ↔ x = a := by
  constructor
  all_goals
  · intro h; simp [h]

theorem notEqRfl [BEq α] {a x : α} : ¬ a = x ↔ ¬ x = a := by
  constructor
  · intro h
    by_cases h' : x = a
    · simp [eqRfl, h] at h'
    · exact h'
  · intro h
    by_cases h' : a = x
    · simp [h'] at h
    · exact h'

theorem notBEqOfNotEq [BEq α] [LawfulBEq α] {a x : α} (h : ¬a = x) :
    ¬ x == a := by
  by_cases h' : x == a
  · simp [eq_of_beq h'] at h
  · exact h'

theorem eqOfSingletonListContains [BEq α] [LawfulBEq α] {a x : α} :
    List.contains [a] x ↔ a == x := by
  constructor
  · intro h
    simp [List.contains, List.elem] at h
    by_cases h' : a = x
    · simp [h']
    · simp [notBEqOfNotEq h'] at h
  · intro h
    rw [List.contains, List.elem]
    have : x == a := by
      rw [eqIffBEq] at h ⊢
      exact eqRfl.mpr h
    simp only [this]

theorem NEListContainsOfListContains [BEq α] [LawfulBEq α] {l : NEList α}
    (h : l.toList.contains x) : l.contains x := by
  induction l with
  | uno  _      => exact eqOfSingletonListContains.mp h
  | cons a _ hi =>
    rw [NEList.toList] at h
    simp [NEList.contains]
    by_cases h' : a == x
    · exact Or.inl h'
    · rw [List.contains] at h
      have : ¬ x == a := by
        rw [eqIffBEq] at h' ⊢
        exact notEqRfl.mp h'
      simp only [this, List.elem] at h
      exact Or.inr $ hi h

theorem ListContainsOfNEListContains [BEq α] [LawfulBEq α] {l : NEList α}
    (h : l.contains x) : l.toList.contains x := by
  induction l with
  | uno  _      => exact eqOfSingletonListContains.mpr h
  | cons a _ hi =>
    rw [NEList.toList]
    simp [NEList.contains] at h
    cases h with | _ h => ?_
    · simp [eqIffBEq.mp h, List.contains, List.elem]
    · rw [List.contains, List.elem]
      by_cases h' : x == a
      · rw [h']
      · simp only [h', hi h]

theorem NEListContainsIffListContains [BEq α] [LawfulBEq α] {l : NEList α} :
    l.contains x ↔ l.toList.contains x :=
  ⟨ListContainsOfNEListContains, NEListContainsOfListContains⟩

mutual

  inductive Value
    | nil   : Value
    | bool  : Bool        → Value
    | int   : Int         → Value
    | float : Float       → Value
    | list  : Array Value → Value
    | str   : String      → Value
    | error : String      → Value
    | curry : (l : NEList String) → l.noDup → Program → Value
    deriving Inhabited

  inductive Expression
    | atom : Value      → Expression
    | var  : String     → Expression
    | not  : Expression → Expression
    | app  : String     → NEList Expression → Expression
    | add  : Expression → Expression → Expression
    | mul  : Expression → Expression → Expression
    | eq   : Expression → Expression → Expression
    | ne   : Expression → Expression → Expression
    | lt   : Expression → Expression → Expression
    | le   : Expression → Expression → Expression
    | gt   : Expression → Expression → Expression
    | ge   : Expression → Expression → Expression

  inductive Program
    | skip        : Program
    | sequence    : Program    → Program → Program
    | attribution : String     → Program → Program
    | ifElse      : Expression → Program → Program → Program
    | whileLoop   : Expression → Program → Program
    | evaluation  : Expression → Program
    | fail        : String     → Program
    deriving Inhabited

end

open Value Expression Program

def Program.getCurryNames? : Program → Option (NEList String)
  | evaluation (atom (curry ns ..))                              => some ns
  | sequence (attribution _ (evaluation (atom (curry ns ..)))) _ => some ns
  | _                                                            => none

def Program.isSequence : Program → Bool
  | sequence .. => true
  | _           => false

def blank (n : Nat) : String :=
  let rec blankAux (cs : List Char) : Nat → List Char
    | 0     => cs
    | n + 1 => ' ' :: ' ' :: (blankAux cs n)
  ⟨blankAux [] n⟩

mutual

  partial def valToString : Value → String
    | nil       => "nil"
    | .bool b   => toString b
    | int   i   => toString i
    | float f   => toString f
    | list  l   => toString $ l.map fun v => valToString v
    | str   s   => s
    | curry _ _ p => progToString p
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

  partial def progToString (p : Program) : String :=
    let rec progToStringAux (l : Nat) : Program → String
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
      | fail s            => s!"raise {s}"
    progToStringAux 0 p

end

def Value.toString      (v : Value)      : String := valToString  v
def Expression.toString (e : Expression) : String := expToString  e
def Program.toString    (p : Program)    : String := progToString p

instance : ToString Value      := ⟨toString⟩
instance : ToString Expression := ⟨toString⟩
instance : ToString Program    := ⟨toString⟩

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
  | error s,  _        => error s
  | _,        error s  => error s
  | str   sL, str   sR => bool $ sL < sR
  | int   iL, int   iR => bool $ iL < iR
  | float fL, float fR => bool $ fL < fR
  | list  lL, list  lR => bool $ lL.size < lR.size
  | curry .., curry .. => error "can't multiply functions"
  | l,         r         =>
    error s!"invalid application of '<' between\n{l}\nand\n{r}"

def Value.le : Value → Value → Value
  | error s,  _        => error s
  | _,        error s  => error s
  | str   sL, str   sR => bool $ sL < sR || sL == sR
  | int   iL, int   iR => bool $ iL ≤ iR
  | float fL, float fR => bool $ fL ≤ fR
  | list  lL, list  lR => bool $ lL.size ≤ lR.size
  | curry .., curry .. => error "can't multiply functions"
  | l,         r         =>
    error s!"invalid application of '<=' between\n{l}\nand\n{r}"

def Value.gt : Value → Value → Value
  | error s,  _        => error s
  | _,        error s  => error s
  | str   sL, str   sR => bool $ sL > sR
  | int   iL, int   iR => bool $ iL > iR
  | float fL, float fR => bool $ fL > fR
  | list  lL, list  lR => bool $ lL.size > lR.size
  | curry .., curry .. => error "can't multiply functions"
  | l,         r         =>
    error s!"invalid application of '>' between\n{l}\nand\n{r}"

def Value.ge : Value → Value → Value
  | error s,  _        => error s
  | _,        error s  => error s
  | str   sL, str   sR => bool $ sL > sR || sL == sR
  | int   iL, int   iR => bool $ iL ≥ iR
  | float fL, float fR => bool $ fL ≥ fR
  | list  lL, list  lR => bool $ lL.size ≥ lR.size
  | curry .., curry .. => error "can't multiply functions"
  | l,         r         =>
    error s!"invalid application of '<=' between\n{l}\nand\n{r}"

partial def Value.eq : Value → Value → Value
  | error s,  _        => error s
  | _,        error s  => error s
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
  | error s,  _        => error s
  | _,        error s  => error s
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

open NEList in
def consume (p : Program) :
    NEList String → NEList Expression → (Option (NEList String)) × Program
  | cons n ns, cons e es =>
    consume (sequence (attribution n (evaluation e)) p) ns es
  | cons n ns, uno  e    => (some ns, sequence (attribution n (evaluation e)) p)
  | uno  n,    uno  e    => (none, sequence (attribution n (evaluation e)) p)
  | uno  _,    cons ..   => (none, fail "incompatible number of parameters")

theorem noDupOfConsumeNoDup
  (h : ns.noDup) (h' : consume p' ns es = (some l, p)) :
    NEList.noDup l = true := by
    induction ns generalizing p' es with
    | uno  _      => cases es <;> cases h'
    | cons _ _ hi =>
      simp [NEList.noDup] at h
      cases es with
      | uno  _   => simp [consume] at h'; simp only [h.2, ← h'.1]
      | cons _ _ => exact hi h.2 h'

abbrev Context := Std.HashMap String Value

protected def Context.toString (c : Context) : String :=
  (c.toList.foldl (init := "")
    fun acc (n, val) => acc ++ s!"{n}:\t{val}\n").trimRight

instance : ToString Context := ⟨Context.toString⟩

def cantEvalAsBool (v : Value) : String :=
  s!"can't evaluate as bool:\n{v}"

mutual

  partial def evaluate (ctx : Context) : Expression → Value
    | atom v     => v
    | var  n     => match ctx[n] with
      | none   => error s!"'{n}' not found"
      | some v => v
    | .not e     => match evaluate ctx e with
      | .bool b => bool !b
      | v       => error $ cantEvalAsBool v
    | app  n es  => match ctx[n] with
      | none                => error s!"'{n}' not found"
      | some (curry ns h p) =>
        match h' : consume p ns es with
        | (some l, p) => curry l (noDupOfConsumeNoDup h h') p
        | (none,   p) => (p.run ctx).2
      | _        => error s!"'{n}' is not an uncurried function"
    | .add eL eR => (evaluate ctx eL).add $ evaluate ctx eR
    | .mul eL eR => (evaluate ctx eL).mul $ evaluate ctx eR
    | .eq  eL eR => (evaluate ctx eL).eq  $ evaluate ctx eR
    | .ne  eL eR => (evaluate ctx eL).ne  $ evaluate ctx eR
    | .lt  eL eR => (evaluate ctx eL).lt  $ evaluate ctx eR
    | .le  eL eR => (evaluate ctx eL).le  $ evaluate ctx eR
    | .gt  eL eR => (evaluate ctx eL).gt  $ evaluate ctx eR
    | .ge  eL eR => (evaluate ctx eL).ge  $ evaluate ctx eR

  partial def Program.run (ctx : Context := default) : Program → Context × Value
    | skip           => (ctx, nil)
    | sequence p₁ p₂ =>
      let res := p₁.run ctx
      match res.2 with
      | error _ => res
      | _       => p₂.run res.1
    | attribution n p => match (p.run ctx).2 with
      | error s => (ctx, error s)
      | v       => (ctx.insert n v, nil)
    | ifElse e pT pF => match evaluate ctx e with
      | .bool b => if b then pT.run ctx else pF.run ctx
      | v       => (ctx, error $ cantEvalAsBool v)
    | whileLoop e p  => match evaluate ctx e with
      | .bool b =>
        if !b then (ctx, nil) else
          match p.run ctx with
          | (ctx, error s)   => (ctx, error s)
          | (ctx, _)         => (whileLoop e p).run ctx
      | v       => (ctx, error $ cantEvalAsBool v)
    | evaluation e   => (ctx, (evaluate ctx e))
    | fail s         => (ctx, error s)

end

mutual

  partial def evaluateIO (ctx : Context) : Expression → IO Value
    | atom v     => return v
    | var  n     => return match ctx[n] with
      | none   => error s!"'{n}' not found"
      | some v => v
    | .not e     => return match ← evaluateIO ctx e with
      | .bool b => bool !b
      | v       => error $ cantEvalAsBool v
    | app  n es  => match ctx[n] with
      | none                => return error s!"'{n}' not found"
      | some (curry ns h p) =>
        match h' : consume p ns es with
        | (some l, p) => return curry l (noDupOfConsumeNoDup h h') p
        | (none,   p) => return (← p.runIO ctx).2
      | _        => return error s!"'{n}' is not an uncurried function"
    | .add eL eR => return (← evaluateIO ctx eL).add $ ← evaluateIO ctx eR
    | .mul eL eR => return (← evaluateIO ctx eL).mul $ ← evaluateIO ctx eR
    | .eq  eL eR => return (← evaluateIO ctx eL).eq  $ ← evaluateIO ctx eR
    | .ne  eL eR => return (← evaluateIO ctx eL).ne  $ ← evaluateIO ctx eR
    | .lt  eL eR => return (← evaluateIO ctx eL).lt  $ ← evaluateIO ctx eR
    | .le  eL eR => return (← evaluateIO ctx eL).le  $ ← evaluateIO ctx eR
    | .gt  eL eR => return (← evaluateIO ctx eL).gt  $ ← evaluateIO ctx eR
    | .ge  eL eR => return (← evaluateIO ctx eL).ge  $ ← evaluateIO ctx eR

  partial def Program.runIO (ctx : Context := default) :
      Program → IO (Context × Value)
    | skip           => return (ctx, nil)
    | sequence p₁ p₂ => do
      let res ← p₁.runIO ctx
      match res.2 with
      | error _ => return res
      | _       => p₂.runIO res.1
    | attribution n p => return match (← p.runIO ctx).2 with
      | error s => (ctx, error s)
      | v       => (ctx.insert n v, nil)
    | ifElse e pT pF => do match ← evaluateIO ctx e with
      | .bool b => if b then pT.runIO ctx else pF.runIO ctx
      | v       => return (ctx, error $ cantEvalAsBool v)
    | whileLoop e p  => do match ← evaluateIO ctx e with
      | .bool b =>
        if !b then return (ctx, nil) else
          match ← p.runIO ctx with
          | (ctx, error s)   => return (ctx, error s)
          | (ctx, _)         => (whileLoop e p).runIO ctx
      | v       => return (ctx, error $ cantEvalAsBool v)
    | evaluation e   => return (ctx, (← evaluateIO ctx e))
    | fail s         => return (ctx, error s)

end
