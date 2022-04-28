/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

declare_syntax_cat              literal
syntax ("-" noWs)? num        : literal
syntax str                    : literal
syntax "true"                 : literal
syntax "false"                : literal
syntax ("-" noWs)? scientific : literal

declare_syntax_cat binop
syntax " + "     : binop
syntax " * "     : binop
syntax " = "     : binop
syntax " != "    : binop
syntax " < "     : binop
syntax " <= "    : binop
syntax " > "     : binop
syntax " >= "    : binop

declare_syntax_cat                            expression
syntax literal                              : expression
syntax withPosition(
  "[ " colGt literal,* " ]")                : expression
syntax:51 ident                             : expression
syntax:49 expression (colGt expression:50)+ : expression
syntax:48 " ! " expression                  : expression
syntax:48 expression binop expression       : expression
syntax " ( " expression " ) "               : expression

declare_syntax_cat                      program
declare_syntax_cat                      programSeq
syntax withPosition((colGe program)+) : programSeq

syntax "skip"                                       : program
syntax withPosition(ident+ colGt " := " programSeq) : program
syntax expression                                   : program
syntax withPosition(
  "if " programSeq colGe " then "
    colGt programSeq
  (colGe " else "
    colGt programSeq)?)                             : program
syntax withPosition("while " programSeq " do "
  colGt programSeq)                                 : program
syntax withPosition("!print " colGt expression)     : program
