/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import FunnyLang.FunnyDSL

/-! example
a := 4         # int

f x y := x + y # function _ → _ → _

fa := f a      # function int → int

fa3 := fa 3    # 7 : int

g n :=
  s := 0
  while > 0
    s := s + n
    n := n - 1
  s

print g 5      # 15
-/

def symbols : List String := [":=", "+", "*", "-", "/", "(", ")"]

def joinedOn (on : String) : List String → String
  | []            => ""
  | [s]           => s
  | s :: s' :: ss => s ++ on ++ joinedOn on (s' :: ss)

def removeDoubleSpaces (l : String) : String :=
  joinedOn " " $ l.splitOn " " |>.filter fun s => ¬ s.isEmpty

def removeComments (l : String) : String :=
  l.splitOn "#" |>.headD ""

def replaceTabs (s : String) : String :=
  s.replace "\t" " "

def spaceSymbols (s : String) : String :=
  symbols.foldl (fun acc sym => acc.replace sym s!" {sym} ") s

def cleanse (s : String) : String :=
  spaceSymbols $ replaceTabs $ removeComments s

def parseLineLevelAux (n : Nat := 0) : List Char → Nat × Option (List Char)
  | []      => (n, none)
  | c :: cs => if c = ' ' then parseLineLevelAux (n + 1) cs else (n, c :: cs)

def parseLineAndLevel (l : String) : Nat × Option String :=
  let (n, cs?) := parseLineLevelAux 0 (cleanse l).data
  (n, cs?.map fun cs => removeDoubleSpaces ⟨cs⟩)

  def parseLines (s : String) : List (Nat × Option String) :=
  s.splitOn "\n" |>.map parseLineAndLevel

def partitionOnFirstAux [DecidableEq α] (l : List α) (a : α) :
    List α → List α × List α
  | h :: t => if h = a then (l.reverse, t) else partitionOnFirstAux (h :: l) a t
  | _      => (l.reverse, [])

def partitionOnFirst [DecidableEq α] (l : List α) (a : α) : List α × List α :=
  partitionOnFirstAux [] a l

-- todo
def parseExpression (ss : List String) : Expression :=
  Expression.var "my_var"

def build : List (Nat × Option String) → Program
  | []            => Program.skip
  | (n, s?) :: ls => match s? with
    | none   => build ls
    | some s =>
      let words := s.splitOn " "
      let (wordsL, wordsR) := partitionOnFirst words ":="
      if wordsL.length < words.length then -- attribution
        match wordsL with
        | []             => unreachable!
        | name :: params =>
          let curryProg := Program.skip -- todo
          let uncurriedProg : Program :=
            if h : params ≠ []
              then Program.evaluation $ Expression.atom $
                Value.curry (params.toNEList h) curryProg
              else curryProg
          let prog := Program.attribution name uncurriedProg
          -- fix: `ls` might have been consumed by `curryProg`
          Program.sequence prog (build ls)
      else let (wordsL, wordsR) := partitionOnFirst words "if"
        if wordsL.length < words.length then -- ifElse
          Program.skip -- todo
        else let (wordsL, wordsR) := partitionOnFirst words "while"
          if wordsL.length < words.length then -- whileLoop
            Program.skip -- todo
          else -- evaluation
            Program.sequence
              (Program.evaluation $ parseExpression words) (build ls)
termination_by _ f => SizeOf.sizeOf f

def parse (s : String) : Program :=
  build $ parseLines s

def p := parse "a := 1"

#eval (p.run default).1.toList
