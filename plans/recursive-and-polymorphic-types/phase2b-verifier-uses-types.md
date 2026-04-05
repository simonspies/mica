# Phase 2b: Verifier Uses Expr.ty

## Goal

Refactor the verifier so that `compile` no longer returns a type. Instead, it uses `Expr.ty` from the typed IR. This changes the signature of `compile` and the statement of `compile_correct`.

## Background

After Phase 2a, `Typed.Expr` carries type annotations and defines `Expr.ty`. But the verifier still ignores those annotations — `compile` returns `(TinyML.Typ × Term .value)` and computes types internally.

This phase removes that redundancy: `compile` returns only `Term .value` and reads types from `Expr.ty`.

## Deliverables

### 1. Change `compile` signature

Currently (in `Mica/Verifier/Expressions.lean`):

```lean
def compile (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx) : Typed.Expr → VerifM (TinyML.Typ × Term .value)
```

Change to:

```lean
def compile (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx) : Typed.Expr → VerifM (Term .value)
```

Key changes:
- The return type drops `TinyML.Typ` — the type is now `e.ty`
- `Γ` is kept because the verifier must *check* the types that elaboration claims — it does not blindly trust `Expr.ty` but verifies consistency with the context

In each case of `compile`, where it previously returned `(ty, term)`, it now returns just `term`. The type computations (e.g., `TinyML.BinOp.typeOf op tl tr`) are still needed — the verifier checks that `e.ty` is consistent with what the operators and context demand, and the existing lemmas apply to those computed types.

### 2. Update `compile_correct`

Currently:

```lean
theorem compile_correct (e : TinyML.Expr) ... 
    (Ψ : TinyML.Typ × Term .value → TransState → Env → Prop) (Φ : Runtime.Val → Prop) :
    VerifM.eval (compile S B Γ e) st ρ Ψ →
    ...
    (∀ v ρ' st' ty se, Ψ (ty, se) st' ρ' → se.wfIn st'.decls → Term.eval ρ' se = v →
      TinyML.ValHasType v ty → Φ v) →
    wp (e.runtime.subst γ) Φ
```

The continuation `Ψ` currently receives `(ty, se)`. After the change:
- `Ψ` receives just `se : Term .value` (plus `TransState` and `Env`)
- The `ValHasType v ty` in the continuation premise uses `e.ty` instead of the returned `ty`

The new shape should be approximately:

```lean
theorem compile_correct (e : Typed.Expr) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx)
    (st : TransState) (ρ : Env) (γ : Runtime.Subst)
    (Ψ : Term .value → TransState → Env → Prop) (Φ : Runtime.Val → Prop) :
    VerifM.eval (compile S B Γ e) st ρ Ψ →
    ...
    (∀ v ρ' st' se, Ψ se st' ρ' → se.wfIn st'.decls → Term.eval ρ' se = v →
      TinyML.ValHasType v e.ty → Φ v) →
    wp (e.runtime.subst γ) Φ
```

**This is the most significant proof change.** The inductive cases in `compile_correct` currently thread the returned type through. After the change, each case must show that `e.ty` is the right type. Since `Expr.ty` is defined to match what `compile` previously computed, the proof structure should be similar but the details will shift.

**Critical:** Do not sorry out the entire `compile_correct` proof. Work case by case — every case must be completed. The overall proof structure (mutual recursion over `compile`/`compileArgs`/`compileBranches`) should be preserved.

### 3. Update `checkSpec` and callers

`checkSpec` in `Mica/Verifier/Functions.lean` calls `compile` and uses the returned type. Update it to use `Expr.ty` instead. Similarly update `checkSpec_correct` and any other theorems in that file.

### 4. Update `Program.check` and `Program.verify`

These are in `Mica/Verifier/Programs.lean`. They call `checkSpec` which calls `compile`. The changes should propagate naturally.

## What NOT to do

- Do not change `Typed.Expr` — its structure was finalized in Phase 2a.
- Do not introduce new types (`Ty`, named types, etc.).
- Do not change `ValHasType`, `wp`, or the operational semantics.
- Do not change the frontend or `elaborate`.

## Verification

`lake build` must succeed and `lake run testsuite Examples/` must pass.
