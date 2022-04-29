# FxyLang

This repository contains the implementation of *Fxy*, a toy language created for
learning purposes.

The name *Fxy* comes from its way of defining functions: `f x y := x + y`. It is
implemented in [Lean 4](https://leanprover.github.io/), which allows us not only
to build software, but also to reason about it.

Big thanks to the [Lean community](https://leanprover.zulipchat.com/),
especially Mario Carneiro, Simon Hudon and the Lean developers!

This repository also serves the purpose of being a somewhat brief demonstration
of the capabilities of Lean 4 as a hybrid of programming language and an
interactive theorem prover assistant. Feel free to continue reading through
[FxyLang](FxyLang) if you're interested in knowing more about it!

## Collaborators

* [Arthur Paulino](https://github.com/arthurpaulino)
* [Joseph O](https://github.com/crabbo-rave)

## Usage

After cloning the repository, build the binary with `lake build`.

If you have a source file, say `test.fxy`, you can run it with
`./build/bin/fxy run test.fxy`. Or, instead, use `run!` to execute `test.fxy`
with the unverified (but faster) executor.

## Fxy specification

### Basic types

* `int` is the type of integer numbers (e.g. `1`, `0`, `-3`)
* `bool` is the type of booleans (`true` and `false`)
* `str` is the type of strings (e.g. `"hi"`, `""`, `"world"`)
* `float` is the type of floating pointer numbers (e.g. `1.0`, `-10.4`)
* `list` is the type of lists of elements of the types above (e.g. `[1, "hi"]`)
* `_ → ... → _` is the type of functions

Integers, booleans, strings and floating pointer numbers are also called
"literals".

### Declarations

To assign a value to a variable, use the walrus operator `:=`. Example:
`a := 1`, `s := "Fxy is cool"`.

To declare a function, use the same walrus operator, but also naming the
arguments on its left. Example: `f x y := x + y`.

### Functions

As mentioned above, functions are defined with the syntax:

```
<function name> <names of input variables> := <function body>
```

The "names" are identifiers that start with letters. The scope of the function
body is defined with indentation (as do the scopes of other structures in Fxy).

The return of the function is defined by its last line. Example:

```
prod a b c :=
  ab := a * b
  ab * c

!print prod 2 3 7
```

The function `prod` computes the product of three variables. The code above
should print out `42` upon execution.

#### Currying

Fxy has a common feature of functional languages: currying. That is, one can
store functions with partially applied arguments for later computations.
Example:

```
prod23 := prod 2 3

!print prod23 7
```

The code above should print out `42` upon execution.

### Forks and loops

Fxy supports logic bifurcation and looping via the respective syntaxes:

```
if <expression> then <body> else <body>
```

```
while <expression> do <body>
```

Example:

```
countTo n :=
  i := 0
  while i < n do
    i := i + 1
  i

if countTo 42 = 42 then
  !print "42"
else
  !print "not 42 :("
```

The code above should print out `42` upon execution.

### Basic operators

Since Fxy is a toy language, it only has the following operators:

* `+` is the regular addition for numbers. For booleans, it represents an "or".
For lists, it does concatenations and can also push a literal to its end. For
strings, `+` does concatenation;

* `*` is the regular multiplication for numbers. For booleans, it represents an
"and".

* `!` represents a "not" for booleans

* `=`, `!=`, `<`, `<=`, `>` and `>=` are the symbols to encode "equals", "not
equals", "less than", "less than or equals to", "greater than" and "greater than
or equals to" respectively.

### Commentaries

Similarly to Python, Fxy uses `#` to represent the beginning of a commentary. So
everything to the right of a `#` (including the `#` itself) will be filtered out
before the parsing phase.
