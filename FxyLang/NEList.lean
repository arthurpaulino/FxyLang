/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

/-- Non-empty list -/
inductive NEList (α : Type)
  | uno  : α → NEList α
  | cons : α → NEList α → NEList α

def List.toNEList (a : α) : List α → NEList α
  | []      => .uno a
  | b :: bs => .cons a (toNEList b bs)

def List.noDup [BEq α] : List α → Bool
  | []      => true
  | a :: as => ¬as.contains a && as.noDup

def NEList.length : NEList α → Nat
  | uno  _   => 1
  | cons _ l => 1 + l.length

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

def NEList.toList : NEList α → List α
  | uno  a   => [a]
  | cons a b => a :: b.toList

def NEList.isEqToList : NEList α → List α → Prop
  | .cons a as, b :: bs => a = b ∧ isEqToList as bs
  | .uno  a   , [b]     => a = b
  | _,          _       => False

theorem NEList.ListToNEListIsEqList {a : α} {as : List α} :
    (as.toNEList a).isEqToList (a :: as) := by
  induction as with
  | nil            => simp only [isEqToList]
  | cons a' as' hi =>
    cases as' with
    | nil      => simp only [isEqToList]
    | cons _ _ => simp [isEqToList] at hi ⊢; exact hi

theorem NEList.toListEqList {a : α} {as : List α} :
    (as.toNEList a).toList = a :: as := by
  induction as with
  | nil           => simp only [toList]
  | cons _ as' hi =>
    cases as' with
    | nil      => simp only [toList]
    | cons _ _ => simp [toList] at hi ⊢; exact hi

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

theorem List.eqOfSingletonListContains [BEq α] [LawfulBEq α] {a x : α} :
    [a].contains x ↔ a == x := by
  constructor
  · intro h
    simp [contains, elem] at h
    by_cases h' : a = x
    · simp [h']
    · simp [notBEqOfNotEq h'] at h
  · intro h
    rw [contains, elem]
    have : x == a := by
      rw [eqIffBEq] at h ⊢
      exact eqRfl.mpr h
    simp only [this]

theorem NEList.containsOfListContains [BEq α] [LawfulBEq α] {l : NEList α}
    (h : l.toList.contains x) : l.contains x := by
  induction l with
  | uno  _      => exact List.eqOfSingletonListContains.mp h
  | cons a _ hi =>
    rw [toList] at h
    simp [contains]
    by_cases h' : a == x
    · exact Or.inl h'
    · rw [List.contains] at h
      have : ¬ x == a := by
        rw [eqIffBEq] at h' ⊢
        exact notEqRfl.mp h'
      simp only [this, List.elem] at h
      exact Or.inr $ hi h

theorem NEList.listContainsOfNEListContains [BEq α] [LawfulBEq α] {l : NEList α}
    (h : l.contains x) : l.toList.contains x := by
  induction l with
  | uno  _      => exact List.eqOfSingletonListContains.mpr h
  | cons a _ hi =>
    rw [toList]
    simp [contains] at h
    cases h with | _ h => ?_
    · simp [eqIffBEq.mp h, List.contains, List.elem]
    · rw [List.contains, List.elem]
      by_cases h' : x == a
      · rw [h']
      · simp only [h', hi h]

theorem NEList.containsIffListContains [BEq α] [LawfulBEq α] {l : NEList α} :
    l.contains x ↔ l.toList.contains x :=
  ⟨listContainsOfNEListContains, containsOfListContains⟩

theorem NEList.notContainsIffListNotContains [BEq α] [LawfulBEq α]
    {l : NEList α} : l.contains x = false ↔ l.toList.contains x = false := by
  constructor
  · intro h
    by_cases h' : List.contains (toList l) x
    · simp only [containsIffListContains.mpr h'] at h
    · simp only [h']
  · intro h
    by_cases h' : l.contains x
    · simp only [containsIffListContains.mp h'] at h
    · simp only [h']

theorem NEList.noDupIffToListNoDup [BEq α] [LawfulBEq α] {l : NEList α} :
    l.noDup ↔ l.toList.noDup := by
  constructor
  · intro h
    induction l with
    | uno _ => simp [noDup, List.noDup, List.contains, List.elem]
    | cons _ _ hi =>
      simp [noDup] at h
      simp [toList, List.noDup]
      exact ⟨(notContainsIffListNotContains.mp h.1), (hi h.2)⟩
  · intro h
    induction l with
    | uno _ => rw [noDup]
    | cons _ _ hi =>
      simp [List.noDup] at h
      simp [noDup]
      exact ⟨(notContainsIffListNotContains.mpr h.1), (hi h.2)⟩

theorem NEList.lengthEqToListLength [BEq α] {l : NEList α} :
    l.length = l.toList.length := by
  induction l with
  | uno _ => simp [length, toList]
  | cons a as hi =>
    simp [length, toList, hi, Nat.add_comm]
