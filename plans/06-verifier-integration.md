# Phase 6: Replace FOL Variables with FOL Constants

## Objective

The verifier currently uses `declareConst` (which creates SMT variables / FOL variables) for values that are semantically uninterpreted constants — they have a fixed interpretation within a verification condition, not a universally-quantified one. Migrate these to use `Const.uninterpreted` and the new constant declaration infrastructure. Rationalize the declaration commands so that `declareConst` operates on the `.consts` component of the signature rather than `.vars`.

## Context

This phase requires more exploration before committing to a detailed plan. The key questions to investigate:

1. **Which uses of `VerifM.decl` are truly variables vs constants?**
   - Function return values, let-bound variables, and fresh witnesses are existentially quantified — but in the SMT encoding they become `declare-const`, which is a nullary uninterpreted function. The distinction is in `VerifM.eval`, where `decl` universally quantifies over all values.
   - Spec-level function symbols (fibonacci, sorted) are universally quantified over all *interpretations* — a different kind of universal quantification.
   - Need to audit `compile` in Expressions.lean and `checkSpec` in Functions.lean to classify each `decl` call.

2. **Can `declareConst` and `declareUninterpretedConst` be unified?**
   - Both emit `(declare-const ...)` to SMT-LIB. The difference is semantic: where the declaration lands in the `Signature` and how `eval` quantifies over it.
   - Investigate whether `declareConst` should move from `.vars` to `.consts` and whether this simplifies or complicates the existing proofs.

3. **What changes in the correctness proofs?**
   - `compile_correct` (Expressions.lean) and `checkSpec_correct` (Functions.lean) are large proofs that depend on `eval_decl`. Changing the semantics of declarations affects the quantifier structure of the verification condition.
   - Need to understand the proof structure before deciding how to refactor.

## Likely Steps (Tentative)

- Audit all `VerifM.decl` call sites and classify as variable vs constant
- For constant uses: switch to `VerifM.declConst`
- Update `Command.declareConst` to add to `Signature.consts` instead of `.vars`
- Delete `Command.declareUninterpretedConst` if now redundant with `declareConst`
- Update `ScopedM.declareConst` and `FlatCtx.addDecl` accordingly
- Update correctness proofs

## Files Likely Touched

- Engine/Command.lean
- Verifier/Scoped.lean
- Verifier/Monad.lean
- Verifier/Expressions.lean
- Verifier/Functions.lean
- Verifier/Programs.lean
- Verifier/Specifications.lean
