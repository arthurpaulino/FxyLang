/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import Std

-- def List.noDup [BEq α] : List α → Bool
--   | []      => true
--   | a :: as => ¬as.contains a && as.noDup

/-- Non-empty list -/
inductive NEList (α : Type)
  | uno  : α → NEList α
  | cons : α → NEList α → NEList α

@[specialize]
def NEList.foldl (f : α → β → α) : (init : α) → NEList β → α
  | a, uno  b   => f a b
  | a, cons b l => foldl f (f a b) l

@[specialize]
def NEList.map (f : α → β) : NEList α → NEList β
  | uno  a     => uno  (f a)
  | cons a  as => cons (f a) (map f as)

def NEList.unfoldStrings (l : NEList String) : String :=
  l.foldl (init := "") $ fun acc a => acc ++ s!" {a}" |>.trimLeft

def NEList.contains [BEq α] : NEList α → α → Bool
  | uno  a,    x => a == x
  | cons a as, x => a == x || as.contains x

def NEList.noDup [BEq α] : NEList α → Bool
  | uno  a    => true
  | cons a as => ¬as.contains a && as.noDup

inductive Expression
  | bool  : Bool   → Expression
  | int   : Int    → Expression
  | float : Float  → Expression
  | str   : String → Expression
  | var   : String → Expression
  | list  : List Expression → Expression
  | not   : Expression → Expression
  | add   : Expression → Expression → Expression
  | mul   : Expression → Expression → Expression
  | eq    : Expression → Expression → Expression
  | ne    : Expression → Expression → Expression
  | lt    : Expression → Expression → Expression
  | le    : Expression → Expression → Expression
  | gt    : Expression → Expression → Expression
  | ge    : Expression → Expression → Expression
  | app   : String → NEList Expression → Expression

inductive Program
  | skip : Program
  | fail : String  → Program
  | eval : Expression → Program
  | decl : String  → Program → Program
  | seq  : Program → Program → Program
  | loop : Expression → Program → Program
  | fork : Expression → Program → Program → Program

inductive Value
  | nil   : Value
  | bool  : Bool   → Value
  | int   : Int    → Value
  | float : Float  → Value
  | str   : String → Value
  | error : String → Value
  | list  : Array Value → Value
  | lam   : (l : NEList String) → l.noDup → Program → Value
  | prog  : Program → Value
  deriving Inhabited

protected partial def Value.toString : Value → String
  | .nil    => "nil"
  | .bool b => toString b
  | int   i => toString i
  | float f => toString f
  | list  l => toString $ l.data.map fun v => Value.toString v
  | str   s => s
  | lam ..  => "«function»"
  | prog _  => "«program»"
  | error s => s!"error: {s}"

mutual

  partial def unfoldExpressions (es : NEList Expression) : String :=
    (es.map fun e => Expression.toString e).unfoldStrings

  protected partial def Expression.toString : Expression → String
    | var   n    => n
    | .bool b    => toString b
    | int   i    => toString i
    | float f    => toString f
    | list  l    => toString $ l.map fun v => Expression.toString v
    | str   s    => s
    | .not  e    => s!"(! {Expression.toString e})"
    | app   n es => s!"({n} {unfoldExpressions es})"
    | add   l r  => s!"({Expression.toString l} + {Expression.toString r})"
    | mul   l r  => s!"({Expression.toString l} * {Expression.toString r})"
    | eq    l r  => s!"({Expression.toString l} = {Expression.toString r})"
    | ne    l r  => s!"({Expression.toString l} != {Expression.toString r})"
    | lt    l r  => s!"({Expression.toString l} < {Expression.toString r})"
    | le    l r  => s!"({Expression.toString l} <= {Expression.toString r})"
    | gt    l r  => s!"({Expression.toString l} > {Expression.toString r})"
    | ge    l r  => s!"({Expression.toString l} >= {Expression.toString r})"

end

instance : ToString Expression := ⟨Expression.toString⟩
instance : ToString Value      := ⟨Value.toString⟩

def Value.typeStr : Value → String
  | nil      => "nil"
  | bool  _  => "bool"
  | int   _  => "int"
  | float _  => "float"
  | str   _  => "str"
  | error _  => "error"
  | list  _  => "list"
  | lam l .. => (l.foldl (init := "") fun acc _ => acc ++ "_ → ") ++ "program"
  | prog _   => "program"

def Value.add : Value → Value → Value
  | error s,  _        => error s
  | _,        error s  => error s
  | bool  bL, bool  bR => bool  $ bL || bR
  | str   sL, str   sR => str   $ sL ++ sR
  | int   iL, int   iR => int   $ iL +  iR
  | float fL, float fR => float $ fL +  fR
  | list  lL, list  lR => list  $ lL ++ lR
  | list  lL, vR       => list  $ lL.push vR
  | lam ..,   lam ..   => error "can't sum functions"
  | l,        r        =>
    error s!"invalid application of '+' between\n{l}\nand\n{r}"

def Value.mul : Value → Value → Value
  | error s,  _        => error s
  | _,        error s  => error s
  | bool  bL, bool  bR => bool  $ bL && bR
  | int   iL, int   iR => int   $ iL *  iR
  | float fL, float fR => float $ fL *  fR
  | lam ..,   lam ..   => error "can't multiply functions"
  | l,        r        =>
    error s!"invalid application of '*' between\n{l}\nand\n{r}"

def Value.lt : Value → Value → Value
  | error s,  _        => error s
  | _,        error s  => error s
  | str   sL, str   sR => bool $ sL < sR
  | int   iL, int   iR => bool $ iL < iR
  | float fL, float fR => bool $ fL < fR
  | list  lL, list  lR => bool $ lL.size < lR.size
  | lam ..,   lam ..   => error "can't multiply functions"
  | l,         r         =>
    error s!"invalid application of '<' between\n{l}\nand\n{r}"

def Value.le : Value → Value → Value
  | error s,  _        => error s
  | _,        error s  => error s
  | str   sL, str   sR => bool $ sL < sR || sL == sR
  | int   iL, int   iR => bool $ iL ≤ iR
  | float fL, float fR => bool $ fL ≤ fR
  | list  lL, list  lR => bool $ lL.size ≤ lR.size
  | lam ..,   lam ..   => error "can't multiply functions"
  | l,         r         =>
    error s!"invalid application of '<=' between\n{l}\nand\n{r}"

def Value.gt : Value → Value → Value
  | error s,  _        => error s
  | _,        error s  => error s
  | str   sL, str   sR => bool $ sL > sR
  | int   iL, int   iR => bool $ iL > iR
  | float fL, float fR => bool $ fL > fR
  | list  lL, list  lR => bool $ lL.size > lR.size
  | lam ..,   lam ..   => error "can't multiply functions"
  | l,         r         =>
    error s!"invalid application of '>' between\n{l}\nand\n{r}"

def Value.ge : Value → Value → Value
  | error s,  _        => error s
  | _,        error s  => error s
  | str   sL, str   sR => bool $ sL > sR || sL == sR
  | int   iL, int   iR => bool $ iL ≥ iR
  | float fL, float fR => bool $ fL ≥ fR
  | list  lL, list  lR => bool $ lL.size ≥ lR.size
  | lam ..,   lam ..   => error "can't multiply functions"
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
  | lam ..,   lam ..   => error "can't compare functions"
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
  | lam ..,   lam ..   => error "can't compare functions"
  | _,        _        => bool true

def cantEvalAsBool (e : Expression) (v : Value) : String :=
  s!"can't evaluate {e} as bool. expression results in {v}, of type {v.typeStr}"

def notFound (n : String) : String :=
  s!"'{n}' not found"

def consume (p : Program) :
    NEList String → NEList Expression → (Option (NEList String)) × Program
  | .cons n ns, .cons e es => consume (.seq (.decl n (.eval e)) p) ns es
  | .cons n ns, .uno  e    => (some ns, .seq (.decl n (.eval e)) p)
  | .uno  n,    .uno  e    => (none, .seq (.decl n (.eval e)) p)
  | .uno  _,    .cons ..   => (none, .fail "incompatible number of parameters")

theorem noDupOfConsumeNoDup
  (h : ns.noDup) (h' : consume p' ns es = (some l, p)) : l.noDup = true := by
    induction ns generalizing p' es with
    | uno  _      => cases es <;> cases h'
    | cons _ _ hi =>
      simp [NEList.noDup] at h
      cases es with
      | uno  _   => simp [consume] at h'; simp only [h.2, ← h'.1]
      | cons _ _ => exact hi h.2 h'

abbrev Context := Std.HashMap String Value

partial def Context.evaluate (ctx : Context) : Expression → Value
  | .bool  b => .bool b
  | .int   i => .int i
  | .float f => .float f
  | .str s   => .str s
  | .var n   => match ctx[n] with
    | none   => .error $ notFound n
    | some v => v
  | .list  l => .list ⟨l.map (evaluate ctx)⟩
  | .not   e => match evaluate ctx e with
    | .bool b     => .bool !b
    | .prog p => .prog p
    | v           => .error $ cantEvalAsBool e v
  | .app n es => match ctx[n] with
    | none               => .error $ notFound n
    | some (.lam ns h p) =>
      match h' : consume p ns es with
      | (some l, p) => .lam l (noDupOfConsumeNoDup h h') p
      | (none,   p) => .prog p
    | _        => .error s!"'{n}' is not an uncurried function"
  | .add eL eR => (evaluate ctx eL).add $ evaluate ctx eR
  | .mul eL eR => (evaluate ctx eL).mul $ evaluate ctx eR
  | .eq  eL eR => (evaluate ctx eL).eq  $ evaluate ctx eR
  | .ne  eL eR => (evaluate ctx eL).ne  $ evaluate ctx eR
  | .lt  eL eR => (evaluate ctx eL).lt  $ evaluate ctx eR
  | .le  eL eR => (evaluate ctx eL).le  $ evaluate ctx eR
  | .gt  eL eR => (evaluate ctx eL).gt  $ evaluate ctx eR
  | .ge  eL eR => (evaluate ctx eL).ge  $ evaluate ctx eR

inductive ProgramResult
  | prog : Program → ProgramResult
  | val  : Value   → ProgramResult

def Program.step (ctx : Context) : Program → Context × ProgramResult
  | skip         => (ctx, .val .nil)
  | fail m       => (ctx, .val $ .error m)
  | eval e       => (ctx, .val $ ctx.evaluate e)
  | seq p₁ p₂    => match p₁.step ctx with
    | (ctx, .val (.error s)) => (ctx, .val (.error s))
    | (ctx, .val _)          => (ctx, .prog p₂) -- discarding value of p₁
    | (ctx, .prog p)         => (ctx, .prog (seq p p₂))
  | decl n p    => match p.step ctx with
    | (ctx, .val v) => (ctx.insert n v, .val .nil)
    | res           => res
  | loop e p     => match ctx.evaluate e with
    | .error s => (ctx, .val (.error s))
    | .bool b  => if b then (ctx, .prog (loop e p)) else (ctx, .val .nil)
    | .prog p? => sorry
    | v        => (ctx, .val (.error (cantEvalAsBool e v)))
  | fork e pT pF => match ctx.evaluate e with
    | .error s => (ctx, .val (.error s))
    | .bool b  => if b then pT.step ctx else pF.step ctx
    | .prog p? => sorry
    | v        => (ctx, .val (.error (cantEvalAsBool e v)))
  -- | loop (eval e) p   => match ctx.evaluate e with
  --   | .error s => (ctx, .val (.error s))
  --   | .bool b  => if b then (ctx, .prog (loop (eval e) p)) else (ctx, .val .nil)
  --   | .prog p? => (ctx, .prog $ fork p? (loop (eval e) p) skip)
  --   | v        => (ctx, .val (.error (cantEvalAsBool e v)))
  -- | loop p? p         => (ctx, .prog $ loop p? p)
  -- | fork (eval e) p q => match ctx.evaluate e with
  --   | .error s => (ctx, .val (.error s))
  --   | .bool b  => if b then p.step ctx else q.step ctx
  --   | .prog p?        => (ctx, .prog $ fork p? p q)
  --   | v          => (ctx, .val (.error (cantEvalAsBool e v)))
  -- | fork p? p q       =>
    -- match p?.step ctx with
    -- | (ctx, .val $ .error s) => 
    -- (ctx, .prog $ fork p? p q)
