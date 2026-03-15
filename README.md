# Mica

A verified verifier for a fragment of OCaml, built in Lean 4 with Z3.

## Example

Mica verifies OCaml functions against specifications written as annotations.
Here is a recursive function that computes triangle numbers, verified against
the exact closed-form spec `r = n*(n+1)/2`:

```ocaml
let rec triangle (n: int) : int =
  if n <= 0 then 0
  else triangle (n - 1) + n
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  assert (n >= 0);
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r = n * (n + 1) / 2);
    ret ())]
```

Build it and run it with:
```
$ lake build
$ .lake/build/bin/mica examples/recursive.ml
Status: all declarations verified
```

More examples are in the [`examples/`](examples/) directory.

## How it works

Unlike approaches that generate a single verification condition and hand it
off to an SMT solver, Mica maintains an interactive session with Z3. The
verifier incrementally declares constants, asserts facts, and issues
check-sat queries as it walks the program. It can also branch on the solver's
responses — for example, testing whether a property is provable before
deciding how to proceed.

The verifier is written in Lean 4 and comes with a mechanized correctness
proof: if the verifier accepts a program, the program satisfies its
specification with respect to a weakest-precondition semantics. Since the
SMT solver exists outside of Lean, correctness is proved against an abstract
characterization of the interactive session (push/pop, assert, check-sat)
that captures what it means for the solver's responses to be sound.

The weakest-precondition rules are currently axiomatized and will be derived
from the operational semantics in a future version.

## Building

Requires [Lean 4](https://lean-lang.org/) and [Z3](https://github.com/Z3Prover/z3)
(on PATH for running the verifier).

```
lake build              # build the verifier
lake build Exploration  # build experimental scratch files (optional)
```

## Project structure

| Directory | Description |
|-----------|-------------|
| `TinyML/` | Lexer, parser, type system, and operational semantics for the surface language |
| `FOL/` | First-order logic with Tarski semantics, designed for SMT integration |
| `Engine/` | Generic infrastructure for interactive SMT sessions |
| `Verifier/` | The verifier and its correctness proof |
| `Base/` | Shared utilities (fresh name generation) |
| `Exploration/` | Experimental scratch work (not built by default) |
| `examples/` | OCaml programs with spec annotations |
