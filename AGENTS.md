# Agent Instructions

## Project Overview

Mica is a program verifier for a fragment of OCaml, implemented in Lean 4. It uses the separation logic framework Iris (via iris-lean) for heap reasoning, Mathlib for mathematical infrastructure, and the SMT solver Z3 as a backend to discharge proof obligations. The core verifier components have mechanized correctness proofs.

**Main.lean** is the CLI entry point. The implementation lives under `Mica/`.

@Mica/OUTLINE.md

**Exploration/** contains experimental scratch work.

**Examples/** contains the test suite of OCaml programs.

### Navigating the codebase

Two layers of generated documentation help you find your way around:

- **`OUTLINE.md`** (one per directory under `Mica/`) — a list of files with a one-line summary each. These are auto-included in the context, so you already have the overview.
- **`<file>.lean.md`** — per-file outline of declarations (names, signatures, docstrings), derived from the Lean LSP. Use these to see concisely what a file provides.

Two lake scripts govern regeneration:

- `lake run generate-file-summaries` — regenerates `<file>.lean.md`. Incremental and does not affect agent caching. Slow to build. These files are not checked in. 
- `lake run generate-overviews` — regenerates `OUTLINE.md`. These *are* checked in and CI-enforced. Ask for user confirmation before regenerating, as they invalidate the cache.


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
- Address Lean's linter warnings.
- If a proof attempt is abandoned, delete the sorried helpers. No dead code.
- If a top-down attempt needs more than 4 helper lemmas, stop and consult the user.
- Before induction, generalize any argument that changes in recursive calls.

### Writing for discoverability

When adding or renaming declarations, keep the outlines meaningful:

- Add a docstring (`/-- ... -/`) to public definition, theorem, and structure unless self-explanatory. These flow into `<file>.lean.md` and are an agent's first read on what a thing does.
- Add or update the `-- SUMMARY: <one line>` comment at the top of the file if the file's purpose has shifted. Keep it concise (one line); it lands verbatim in the directory `OUTLINE.md`.

### Iris proof mode

- Tactic reference: `docs/iris-tactics.md`. Worked examples: `Mica/SeparationLogic/ProofModePatterns.lean`.
- There is a persistent and a spatial context. Persistent assertions can be duplicated. Spatial assertions behave linearly (_affine_ to be precise).
- Spatial hypotheses must be distributed when splitting `∗` — use `isplitl [H1 ... Hn]`/`isplitr [H1 ... Hn]`. Always specify via the brackets which assumptions you want to take on the left/right side.
- Persistent hypotheses (when in the persistent context) remain accessible in both branches. Introduce them with `□` to add to the persistent context. (Works only for persistent assertions.) 
- In `... $$ h` the assumption `h` must match the goal exactly, and `... $$ [h]` spawns a new subgoal where `h` is accessible to prove the goal.
- For simple entailment chains, prefer term mode (`sep_mono`, `sep_comm`, `.trans`).

### Search tools (when available)

- `lean_local_search` — use freely.
- `lean_loogle` — use rarely.
- `lean_leansearch` — do not use.
- `lean_leanfinder`, `lean_state_search`, `lean_hammer_premise` — do not use.

---

## Style Guide

**Naming:**
- Prefer elegant single-word names for definitions (e.g., `eval`, `translate`, `correct`), not multi-word camelCase.
- Theorems: namespaced under the definition with dots. Suffixes: `_refl`, `_symm`, `_trans`, `_mono`, `_injective`, `_iff`, `_of_X` (from X), `X_of_` (to X).
- One word per concept everywhere: `eval` (semantics), `translate` (IR compilation), `correct` (soundness linking translate to eval).
- Prefer composing `eval_bind`, `eval_decl` over fused names like `eval_bind_decl_assume`.

**File organization:**
- One definition + its API per section. Importing a definition should give you its basic API.
