# FxyLang

This repository contains the implementation of *Fxy*, a toy language created for
learning purposes.

The name *Fxy* comes from its way of defining functions: `f x y := x + y`. It is
implemented in [Lean 4](https://leanprover.github.io/), which also allows us to
reason about the correctness of its semantics.

Big thanks to the [Lean community](https://leanprover.zulipchat.com/),
especially Mario Carneiro, Simon Hudon and the Lean developers!

## Usage

After cloning the repository, build the binary with `lake build`.

If you have a source file, say `test.fxy`, you can run it with
`./build/bin/fxy run test.fxy`. Or, instead, use `run!` to execute `test.fxy`
with the unverified (but faster) runner.

## Fxy API

### Basic types

* `int` is the type of integer numbers (e.g. `1`, `0`, `-3`)
* `bool` is the type of booleans (`true` and `false`)
* `str` is the type of strings (e.g. `"hi"`, `""`, `"world"`)
* `float` is the type of floating pointer numbers (e.g. `1.0`, `-10.4`)
* `list` is the type of lists of elements of the types above (e.g. `[1, "hi"]`)
* `_ → ... → _` is the type of functions

### Declarations

To assign a value to a variable, use the walrus operator `:=`. Example:
`a := 1`, `s := "Fxy is cool"`.

To declare a function, use the same walrus operator, but naming the arguments on
its left. Example: `f x y := x + y`.
