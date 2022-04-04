/-
  Copyright (c) 2022 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

declare_syntax_cat                            value
syntax ("-" noWs)? num                      : value
syntax str                                  : value
syntax "true"                               : value
syntax "false"                              : value
syntax ("-" noWs)? num noWs "." (noWs num)? : value
syntax withPosition("[ " colGt value* " ]") : value
syntax "nil"                                : value

declare_syntax_cat                       expression
syntax value                           : expression
syntax " ! " expression                : expression
syntax expression " + "  expression    : expression
syntax expression " * "  expression    : expression
syntax expression " = "  expression    : expression
syntax expression " != " expression    : expression
syntax expression " < "  expression    : expression
syntax expression " <= " expression    : expression
syntax expression " > "  expression    : expression
syntax expression " >= " expression    : expression
syntax:51 ident                        : expression
syntax:49 ident (colGt expression:50)+ : expression
syntax " ( " expression " ) "          : expression

declare_syntax_cat                      program
declare_syntax_cat                      programSeq
syntax withPosition((colGe program)+) : programSeq

syntax "skip"                                                 : program
syntax withPosition(ident+ " := " colGt programSeq)           : program
syntax expression                                             : program
syntax "if" expression "then" colGt programSeq
  ("else" colGt programSeq)?                                  : program
syntax withPosition("while" expression "do" colGt programSeq) : program
syntax " ( " programSeq " ) "                                 : program
