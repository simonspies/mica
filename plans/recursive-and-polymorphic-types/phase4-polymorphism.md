# Phase 4: Polymorphism

## Goal

Add function-level polymorphism. Functions can have polymorphic type schemes. Elaboration instantiates them using unification. The verifier handles polymorphic types via a semantic interpretation where type variables map to predicates on values.

## Background

After Phase 3, `Typ` includes `named` and `tvar` constructors, subtyping unfolds named types, and `match` is the left-unfolding site. All type parameters are concrete at every use site — there is no polymorphism.

This phase adds:
- `Scheme` for polymorphic function signatures
- Subtyping with unification during elaboration
- `Typed.Expr.global` for explicitly instantiated function references
- Explicit type variable declarations on functions in the typed IR
- A semantic interpretation of type variables in `ValHasType`

This is the most speculative phase. The overall shape is clear, but implementation details (especially around unification) should be determined during implementation rather than prescribed here.

## Design Constraints (from the overview)

- Constructors always synthesize their principal narrow structural sum — named type recovery happens at use sites via subtype checking with unification
- Unification is confined to elaboration — the verifier never solves type variables
- `Typed.Expr` is meta-free — all metavariables are resolved before emission
- If a metavariable remains unconstrained, elaboration rejects the term

## Deliverables

### 1. Define `Scheme`

```lean
structure Scheme where
  tparams : List TyVar
  body    : Typ
```

Add a scheme environment to track polymorphic function signatures:

```lean
abbrev SchemeEnv := String → Option Scheme
```

### 2. Add `Typed.Expr.global`

Add a constructor for explicitly instantiated function references:

```lean
| global (name : String) (tyArgs : List Typ) (ty : Typ)
```

- `tyArgs` is the concrete instantiation of the scheme's type parameters
- `ty` is the fully instantiated type (i.e., `scheme.body` with `tparams` substituted by `tyArgs`)
- `Expr.ty (.global _ _ ty) = ty`

Use `global` for **all** function references, not just polymorphic ones. Monomorphic functions simply have empty `tyArgs`. This avoids special-casing in the verifier.

At runtime, `global` erases the same way as `var`:

```lean
| .global name _ _ => .var name
```

### 3. Explicit type variable declarations on functions

In the typed IR, functions must declare which type variables they are polymorphic over:

```lean
| fix (tparams : List TyVar) (self : Binder) (args : List Binder) (retTy : Typ) (body : Expr)
```

Only the declared `tparams` are available as `tvar` inside the function body. This is the typed-IR equivalent of `let f (type a) (type b) ...`.

Generalization — determining which type variables to bind — happens in the untyped-to-typed translation, not in the frontend. The translation infers types for the function, discovers which type variables are free, and generalizes them into `tparams`.

### 4. Subtyping with unification during elaboration

At application sites, elaboration must solve type variable instantiations. The key operation is a subtyping check that can assign metavariables:

- Instantiate the function's `tparams` with fresh metavariables
- Subtype-check the argument types against the parameter types, assigning metavariables as needed
- Zonk (substitute all solved metavariables) and emit a meta-free `Typed.Expr`
- If any metavariable remains unassigned, reject the term

The exact representation of metavariables and the unification algorithm are implementation choices. Since elaboration only needs to produce a well-typed term — the verifier checks correctness independently — the unification implementation can use mutable state freely. It only needs to terminate.

**Key constraint:** after zonking, every `cast` node that elaboration inserts must pass the verifier's subtyping check (`Typ.sub`). Elaboration's unification may be more powerful than the verifier's subtyping (e.g., it can assign metavariables), but the *concrete results* it produces — the fully instantiated casts — must be verifiable by the simpler check.

### 5. Constructor elaboration

Constructors do NOT change — they still synthesize their principal narrow structural sum via `inj`. The named type is recovered at use sites.

For example, given `size : ∀ a, tree a → int` and `size (Node (1, Empty, Empty))`:
- `Node (1, Empty, Empty)` synthesizes `sum [empty, tuple [int, sum [unit, empty], sum [unit, empty]]]`
- Elaboration instantiates `size` to `tree ?a → int`
- Subtype-checking the argument against `named "tree" [?a]` unfolds `tree` and solves `?a := int`
- The emitted typed expression uses `global "size" [int] (arrow (named "tree" [int]) int)`
- A `cast` is inserted on the argument: `cast (inj ...) (named "tree" [int])`

### 6. Semantic interpretation for `ValHasType`

After Phase 3, `ValHasType` takes a `TypeEnv` and handles `named` types. For polymorphism, the verifier needs to state correctness for polymorphic functions without fixing the type parameter.

The approach: parameterize `ValHasType` by an interpretation of type variables:

```lean
abbrev TyInterp := TyVar → (Runtime.Val → Prop)

mutual
  inductive ValHasType (Θ : TypeEnv) (ι : TyInterp) : Runtime.Val → Typ → Prop where
    | int  : ValHasType Θ ι (.int n)  .int
    | bool : ValHasType Θ ι (.bool b) .bool
    | unit : ValHasType Θ ι .unit     .unit
    | tvar : ι α v → ValHasType Θ ι v (.tvar α)
    | inj  : ...  -- same structure as before
    | tuple : ...
    | any  : ValHasType Θ ι v .value
    | named : TypeName.unfold Θ T args = some ty →
              ValHasType Θ ι v ty →
              ValHasType Θ ι v (.named T args)

  inductive ValsHaveTypes (Θ : TypeEnv) (ι : TyInterp) : List Runtime.Val → List Typ → Prop where
    | nil  : ValsHaveTypes Θ ι [] []
    | cons : ValHasType Θ ι v t → ValsHaveTypes Θ ι vs ts → ValsHaveTypes Θ ι (v :: vs) (t :: ts)
end
```

The critical point for specifications: in `Spec.isPrecondFor`, `ι` is **universally quantified**. The caller may choose any interpretation of the type variables. The same `ι` is used for both the arguments and the return value. This means the specification of a polymorphic function is parametric — it holds for all type interpretations.

At a concrete call site, the caller instantiates `ι` to match the chosen type arguments. For example, calling `size` at type `tree int → int`, the caller sets `ι "a" = fun v => ValHasType Θ ι v .int`.

### 7. Update `compile_correct`

`compile_correct` must now work with `ValHasType Θ ι` instead of `ValHasType Θ`. The `TypeEnv` parameter (from Phase 3) is already present. The new `ι` parameter is threaded through.

For monomorphic code, `ι` is unused (no `tvar` in types). The existing proof structure should largely carry over.

### 8. Update `Program.check`

`Program.check` must now:
- Track `SchemeEnv` alongside `SpecMap` and `TypeEnv`
- When processing a function declaration, use its `tparams` to form a `Scheme`
- When verifying a call to a function, use the instantiation from `Typed.Expr.global`

## What NOT to do

- Do not change the runtime language or operational semantics.
- Do not add recursive non-variant types.
- Do not add higher-rank polymorphism — only top-level `∀` on function declarations.

## Verification

`lake build` must succeed and `lake run testsuite Examples/` must pass. New test files with polymorphic functions over recursive types should be added and verifiable.
