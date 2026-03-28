# Uninterpreted Constants in FOL — Overview

## Goal

Enrich the FOL layer and verifier with uninterpreted constants (arity 0), unary functions, and binary functions. This enables spec-level functions like `fibonacci` or predicates like `sorted` in the verifier.

## Design

Extend the existing `Const`, `UnOp`, `BinOp` types with `.uninterpreted` constructors rather than adding new `Term` constructors. This reuses the existing term structure cleanly.

`Env` becomes a structure with four fields: `.vars` (existing variable lookup), `.consts` (nullary uninterpreted), `.unary` (unary uninterpreted), `.binary` (binary uninterpreted). All evaluation functions (`Const.denote`, `UnOp.eval`, `BinOp.eval`) receive the full `Env` to look up interpretations for uninterpreted symbols.

`Env.agreeOn` is defined over all four `Signature` components from the start, so theorem statements like `eval_env_agree` never need to change — only proofs gain cases as new constructors are added.

`VarCtx` stays as `List Var` for genuine variable lists (bindings in `Verifier/Utils.lean`). A new `Signature` structure with fields for each symbol kind replaces `VarCtx` in FOL well-formedness, `SmtFrame`, and `FlatCtx`. Signature components use named structures (`FOL.Const`, `FOL.Unary`, `FOL.Binary`) rather than tuples.

## Phases

1. **Generalize `Env` and `Signature`** — Add new fields, replace `VarCtx` with `Signature` in FOL/SMT definitions. `Env.agreeOn` covers all components. Nothing uses the new fields yet.
2. **Make `wfIn` inductive** — Change `Term.wfIn`/`Formula.wfIn` from membership-based to recursive. Update `checkWf`. No bridge lemmas to the old definition — proofs are updated directly.
3. **Thread `Env` through operator evaluation** — `Const.denote`/`UnOp.eval`/`BinOp.eval` gain an `Env` parameter without using it. Forces statement updates across eval lemmas.
4. **Add `.uninterpreted` constructors** — The actual new constructors, with separate `Const.wfIn`, `UnOp.wfIn`, `BinOp.wfIn` definitions. Evaluation uses `Env` for these cases. Printing emits function names.
5. **Expose at verifier layer** — `Command.declareFun`, `ScopedM.declareUnary`/`.declareBinary`/`.declareUninterpretedConst`, `VerifM` ops. Fresh name generation checks all `Signature` components.
6. **Replace FOL variables with FOL constants** — The verifier currently uses `declareConst` (SMT variables) for values that are semantically uninterpreted constants. Migrate these to use `Const.uninterpreted` and the new declaration ops. Update `declareConst` to use `.consts` instead of `.vars` where appropriate. Delete `declareUninterpretedConst` if it becomes redundant with the updated `declareConst`. This phase requires more exploration of the verifier's usage patterns before committing to a detailed plan.

## Key Invariant

Each phase must leave the project building. Changes are additive: new fields/constructors are introduced before they are used. Existing proofs are updated minimally at each step.

## File Impact Map

| File | Ph1 | Ph2 | Ph3 | Ph4 | Ph5 | Ph6 |
|------|-----|-----|-----|-----|-----|-----|
| FOL/Variables.lean | X | | | X | | |
| FOL/Terms.lean | X | X | X | X | | |
| FOL/Formulas.lean | X | X | X | X | | |
| FOL/Subst.lean | X | X | X | X | | |
| FOL/Printing.lean | | | | X | | |
| Engine/Command.lean | X | | | | X | X |
| Verifier/Scoped.lean | X | | | | X | X |
| Verifier/Monad.lean | | | | | X | X |
| Verifier/Atoms.lean | | X | X | X | | |
| Verifier/Assertions.lean | | X | X | | | |
| Verifier/Expressions.lean | | X | X | X | | X |
| Verifier/Utils.lean | | | | | | |
| Verifier/Specifications.lean | | X | X | | | X |
| Verifier/PredicateTransformers.lean | | X | X | | | |
| Verifier/Functions.lean | | | | | | X |
| Verifier/Programs.lean | | | | | | X |
