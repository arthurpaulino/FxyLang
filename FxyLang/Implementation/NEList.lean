/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

/-
This file contains definitions for `NEList`, an inductive type meant to
represent non-empty lists.

They are used to encode the arguments of a function or the parameters used to
make functions applications.

For example, in `f x y := ⋯ `, `x` and `y` will become members of a
`NEList String`. And in `f (a + 2) 5`, `(a + 2)` and `5` will become members of
a `NEList Expression`. We'll see more about those soon.
-/

inductive NEList (α : Type)
  | uno  : α → NEList α
  | cons : α → NEList α → NEList α

/-- Builds an `NEList α` from a term of `α` and a term of `List α` -/
def List.toNEList (a : α) : List α → NEList α
  | []      => .uno a
  | b :: bs => .cons a (toNEList b bs)

/-- Returns `true` iff a list doesn't have duplicated elements -/
def List.noDup [BEq α] : List α → Bool
  | []      => true
  | a :: as => ¬as.contains a && as.noDup

/-- The length of a `NEList` -/
def NEList.length : NEList α → Nat
  | uno  _   => 1
  | cons _ l => l.length + 1

/-- Performs a fold-left on a `NEList`

The `specialize` tag forces the compiler to create a version of the function
for each `f` used for optimization purposes -/
@[specialize]
def NEList.foldl (f : α → β → α) : (init : α) → NEList β → α
  | a, uno  b   => f a b
  | a, cons b l => foldl f (f a b) l

/-- Performs a map on a `NEList` -/
@[specialize]
def NEList.map (f : α → β) : NEList α → NEList β
  | uno  a    => uno  (f a)
  | cons a as => cons (f a) (map f as)

/-- Builds a string with each element of a `NEList` separated by a whitespace -/
def NEList.unfoldStrings (l : NEList String) : String :=
  l.foldl (init := "") $ fun acc a => acc ++ s!" {a}" |>.trimLeft

/-- Whether an `NEList α` contains a certain term of `α` -/
def NEList.contains [BEq α] : NEList α → α → Bool
  | uno  a,    x => a == x
  | cons a as, x => a == x || as.contains x

/-- Returns `true` iff the non-empty list doesn't have duplicated elements -/
def NEList.noDup [BEq α] : NEList α → Bool
  | uno  a    => true
  | cons a as => ¬as.contains a && as.noDup

/-- Creates a term of `List α` from the elements of a term of `NEList α` -/
def NEList.toList : NEList α → List α
  | uno  a   => [a]
  | cons a b => a :: b.toList
