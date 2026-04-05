# Phase 3: Nominal Recursive Types

## Goal

Add support for recursive variant type declarations. These are nominal types that unfold on the right in subtyping and on the left in `match`. No polymorphism yet — all type parameters are concrete at every use site.

## Background

After Phase 2, the typed IR (`Typed.Expr`) carries type annotations and the verifier uses `Expr.ty`. The type language is `TinyML.Typ`, which has structural sums, tuples, arrows, etc. but no named/nominal types.

This phase extends `Typ` with `tvar` and `named` constructors and introduces:
- `DataDecl` for recursive variant declarations
- A type declaration environment (`Θ`) threaded through elaboration and verification
- Subtyping with right-unfolding of named types
- `match` as the left-unfolding site

## Design Constraints (from the overview)

- Recursive type declarations are supported **only for variants**
- Non-recursive type declarations are elaborated away (as they are today)
- Constructors synthesize their **principal narrow structural sum** — they do NOT synthesize a named type
- Named types unfold **only on the right** in subtyping
- `match` is the **only** construct that unfolds named types on the left
- `cast` nodes are inserted by elaboration at use sites where a structural sum needs to be checked against a named type

## Deliverables

### 1. Extend `Typ` with `tvar` and `named`

Add two constructors to the existing `TinyML.Typ` in `Common.lean`:

```lean
inductive Typ where
  | unit | bool | int
  | sum (ts : List Typ)
  | arrow (t1 t2 : Typ)
  | ref (t : Typ)
  | empty | value
  | tuple (ts : List Typ)
  | tvar  (v : TyVar)                  -- NEW
  | named (T : TypeName) (args : List Typ)  -- NEW
```

where:

```lean
abbrev TyVar := String
abbrev TypeName := String
```

This is a change to the shared type, so it affects the entire codebase. All existing pattern matches on `Typ` must handle the new constructors (typically as impossible/error cases in contexts where `tvar`/`named` cannot appear). Update `DecidableEq`, `BEq`, etc. This is the heaviest mechanical part of the phase — do it first, since everything else depends on it building.

### 2. Define `DataDecl`, `TypeEnv`, and unfolding

```lean
structure DataDecl where
  tparams  : List TyVar
  payloads : List Typ        -- each payload may reference tparams and the type itself via `named`

abbrev TypeEnv := TypeName → Option DataDecl
```

Define substitution on `Typ`:

```lean
def Typ.subst (σ : TyVar → Typ) : Typ → Typ
```

Define instantiation on `DataDecl`:

```lean
def DataDecl.instantiate (d : DataDecl) (args : List Typ) : Typ :=
  Typ.sum (d.payloads.map (Typ.subst (fun v => (d.tparams.zip args).lookup v |>.getD (.tvar v))))
```

Define unfolding:

```lean
def TypeName.unfold (Θ : TypeEnv) (T : TypeName) (args : List Typ) : Option Typ :=
  (Θ T).map (·.instantiate args)
```

### 3. Define subtyping

Define a subtyping check:

```lean
inductive FoldStatus where
  | canFold    -- right-unfolding is allowed
  | exhausted  -- right-unfolding has been used at this level

def Typ.sub (Θ : TypeEnv) : FoldStatus → Typ → Typ → Bool
```

Rules:
- Structural rules for `int`, `bool`, `unit`, `empty`, `value`, `arrow`, `tuple`, `sum`, `ref` — same as the existing subtyping
- `sub Θ .canFold s (.named T args)` — unfold the right-hand side via `TypeName.unfold Θ T args` and recurse with `.exhausted`
- `sub Θ .exhausted s (.named T args)` — fail (no double-unfolding at the same level)
- `sub Θ _ s .value` — always true
- `sub Θ _ .empty t` — always true
- No left-unfolding of `named` in subtyping

Termination: lexicographic on `(size of left type, FoldStatus)`. Right-unfolding decreases `FoldStatus` (from `.canFold` to `.exhausted`). Structural recursion into subterms decreases the first component and resets the status to `.canFold`.

### 4. Update `infer` and `check` for named types

`infer` does not change fundamentally — constructors still synthesize structural sums. The key changes:

- `check` now uses `Typ.sub Θ .canFold` — this *replaces* the previous `Typ.sub` from Phase 2a entirely
- `infer` for `match_` must unfold the scrutinee type if it is `named`:

```lean
-- In infer, match_ case:
let scrutTy := scrutExpr.ty
let payloadTys ← match scrutTy with
  | .sum ts => pure ts
  | .named T args =>
      match TypeName.unfold Θ T args with
      | some (.sum ts) => pure ts
      | _ => .error (...)
  | _ => .error (...)
```

`infer` and `check` must now take `Θ : TypeEnv` as a parameter.

### 5. Add type declarations to `Untyped`

Type declarations must be representable in the untyped IR so that TinyML is a self-contained language. Add a type declaration form to `Untyped`:

```lean
inductive Untyped.TypeDecl where
  | variant (name : TypeName) (params : List TyVar) (ctors : List Typ)
```

Each constructor always has a payload type — the frontend inserts `unit` for nullary constructors.

And extend `Untyped.Program` to include type declarations (either as a separate list or interleaved with value declarations).

The frontend elaborates OCaml type declarations into `Untyped.TypeDecl`. The untyped-to-typed elaboration converts these into `DataDecl` entries and builds the `TypeEnv`. Type declarations are erased at runtime — they have no runtime representation.

### 6. Update `ValHasType`

`ValHasType` must be extended to handle `named` types. It takes a `TypeEnv` and unfolds `named` types:

```lean
mutual
  inductive ValHasType (Θ : TypeEnv) : Runtime.Val → Typ → Prop where
    | int  (n : Int)  : ValHasType Θ (.int n)  .int
    | bool (b : Bool) : ValHasType Θ (.bool b) .bool
    | unit            : ValHasType Θ .unit     .unit
    | inj  : ...  -- same structure as before
    | tuple : ...
    | any  : ValHasType Θ v .value
    | named : TypeName.unfold Θ T args = some ty →
              ValHasType Θ v ty →
              ValHasType Θ v (.named T args)

  inductive ValsHaveTypes (Θ : TypeEnv) : List Runtime.Val → List Typ → Prop where
    | nil  : ValsHaveTypes Θ [] []
    | cons : ValHasType Θ v t → ValsHaveTypes Θ vs ts → ValsHaveTypes Θ (v :: vs) (t :: ts)
end
```

This replaces the existing `ValHasType`. The signature changes from `Runtime.Val → Typ → Prop` to `TypeEnv → Runtime.Val → Typ → Prop`. All consumers must be updated to thread `Θ`.

### 7. Update the verifier

`compile` and `compile_correct` must now carry `Θ : TypeEnv`. The key changes:

- `compile` for `match_` unfolds named scrutinee types (same logic as `infer`)
- `compile_correct` uses the updated `ValHasType Θ`
- `checkSpec`, `Program.check`, `Program.verify` thread `Θ`

## What NOT to do

- Do not add polymorphism, `Scheme`, or unification with metavariables. All type parameters at use sites are concrete.
- Do not change `Runtime.Expr` or the operational semantics.
- Do not change `wp`.

## Verification

`lake build` must succeed and `lake run testsuite Examples/` must pass. New test files with recursive types (e.g., `list`, `tree`) should be added and verifiable.
