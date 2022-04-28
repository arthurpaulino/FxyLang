# Fxy implementation

Let's divide the implementation of Fxy in

## Backend

Contains the definitions of the main inductive types to represent a Fxy program,
its execution states as well as the functions to run a Fxy program.

1. [NEList](NEList.lean)
2. [AST](AST.lean)
3. [ASTUtilities](ASTUtilities.lean)
4. [Execution](Execution.lean)

## Frontend

Contains the definition of the Fxy syntax as well as the functions to parse
source code as an abstract syntax tree.

1. [Syntax](Syntax.lean)
2. [Parser](Parser.lean)
