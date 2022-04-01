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
syntax " [ " value* " ] "                   : value
syntax "nil"                                : value

declare_syntax_cat                    expression
syntax value                        : expression
syntax expression " + " expression  : expression
syntax expression " * " expression  : expression
syntax " ! " expression             : expression
syntax expression " = " expression  : expression
syntax expression " != " expression : expression
syntax expression " < " expression  : expression
syntax expression " <= " expression : expression
syntax expression " > " expression  : expression
syntax expression " >= " expression : expression
syntax ident expression*            : expression
syntax " ( " expression " ) "       : expression

declare_syntax_cat                                     program
syntax "skip"                                        : program
syntax:25 program " ; " program                      : program
syntax ident+ " := " program:75                      : program
syntax expression                                    : program
syntax "if" expression "then" program "else" program : program
syntax "while" expression "do" program               : program
syntax " ( " program " ) "                           : program
