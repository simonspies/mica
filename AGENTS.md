# CLAUDE.md

## Project Overview

Mica is a program verifier for a fragment of OCaml, implemented in Lean 4. It uses the separation logic framework Iris (via iris-lean) for heap reasoning, Mathlib for mathematical infrastructure, and the SMT solver Z3 as a backend to discharge proof obligations. The core verifier components have mechanized correctness proofs.

**Main.lean** is the CLI entry point. The implementation lives under `Mica/`, roughly in dependency order:

1. **Base/** — Shared utilities.
2. **TinyML/** — Core IR in three stages: `Untyped` (surface), `Typed` (elaborated), `Runtime` (operational semantics).
3. **FOL/** — First-order logic with Tarski semantics, targeting SMT encoding.
4. **Engine/** — Defines the interaction protocol with the SMT solver and implements it via Z3. The protocol is what correctness proofs are stated against.
5. **SeparationLogic/** — Iris-based separation logic reasoning principles for TinyML.
6. **Verifier/** — The verifier itself, stratified into monadic layers with correctness proofs.
7. **Frontend/** — Lexer, parser, elaborator, and spec parser for the OCaml surface syntax.

**Exploration/** contains experimental scratch work where sorries are acceptable.

**Examples/** contains the test suite of OCaml programs.

---

## Style Guide

**Naming:**
- Prefer elegant single-word names for definitions (e.g., `eval`, `translate`, `correct`), not multi-word camelCase.
- Theorems: namespaced under the definition with dots. Suffixes: `_refl`, `_symm`, `_trans`, `_mono`, `_injective`, `_iff`, `_of_X` (from X), `X_of_` (to X).
- One word per concept everywhere: `eval` (semantics), `translate` (IR compilation), `correct` (soundness linking translate to eval).
- Prefer composing `eval_bind`, `eval_decl` over fused names like `eval_bind_decl_assume`.

**File organization:**
- One definition + its API per section. Importing a definition should give you its basic API.

---

## Development Guidelines

### Building and running

```bash
lake build                        # build the project
lake env lean <file>              # build a single file
lake exe mica <file.ml>           # run the verifier on an OCaml source file
lake run testsuite Examples/      # run the test suite
```

**MCP Tools**
- `lean_diagnostic_messages` after proof work, check for errors (filter to the declaration)

### Proof discipline

- Never sorry out an existing proof — locally sorry a case or assumption instead. Deleting a working proof means re-proving from scratch.
- If a proof attempt is abandoned, delete the sorried helpers. No dead code.
- If a top-down attempt needs more than 4 helper lemmas, stop and consult the user.
- Before induction, generalize any argument that changes in recursive calls.

### Iris proof mode

- Tactic reference: `docs/iris-tactics.md`. Worked examples: `Mica/SeparationLogic/ProofModePatterns.lean`.
- Spatial hypotheses must be distributed when splitting `∗` — use `isplitl`/`isplitr`.
- For simple entailment chains, prefer term mode (`sep_mono`, `sep_comm`, `.trans`).

### Search tools (when available)

- `lean_local_search` — use freely.
- `lean_loogle` — use rarely.
- `lean_leansearch` — do not use.
- `lean_leanfinder`, `lean_state_search`, `lean_hammer_premise` — do not use.
