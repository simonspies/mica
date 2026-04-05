# Phase 2a: Add Type Annotations to Typed IR

## Goal

Enrich `Typed.Expr` so that every node carries enough type information to compute `Expr.ty` — a syntax-directed type for every expression. Replace the trivial `elaborate` with type elaboration (`infer` and `check`). The verifier continues to work as before (ignoring the new annotations).

## Background

After Phase 1, `Typed.Expr` is structurally identical to `Untyped.Expr`. The verifier consumes `Typed.Expr` and internally computes types via `compile`, which returns `(TinyML.Typ × Term .value)`.

This phase adds type annotations to `Typed.Expr` and defines `Expr.ty`. The verifier is NOT changed in this phase — it still returns a type from `compile` and ignores the annotations on the typed IR. Phase 2b will refactor the verifier to use `Expr.ty`.

## Deliverables

### 1. Extend `Typed.Expr` with type annotations

Modify `Typed.Expr` to carry types on the constructors that need them. The target shape (from the design overview) is:

```lean
inductive Expr where
  | const  (c : Const)
  | var    (name : Var) (ty : Typ)          -- NEW: carries its type
  | unop   (op : UnOp) (e : Expr) (ty : Typ) -- NEW: result type
  | binop  (op : BinOp) (lhs rhs : Expr) (ty : Typ) -- NEW: result type
  | fix    (self : Binder) (args : List Binder) (retTy : Typ) (body : Expr) -- retTy is now non-optional
  | app    (fn : Expr) (args : List Expr) (ty : Typ) -- NEW: result type
  | ifThenElse (cond thn els : Expr) (ty : Typ) -- NEW: result type
  | letIn  (name : Binder) (bound body : Expr)
  | ref    (e : Expr)
  | deref  (e : Expr) (ty : Typ)            -- NEW: result type
  | store  (loc val : Expr)
  | assert (e : Expr)
  | tuple  (es : List Expr)
  | inj    (tag : Nat) (arity : Nat) (payload : Expr)
  | match_ (scrutinee : Expr) (branches : List (Binder × Expr)) (ty : Typ) -- NEW: result type
  | cast   (e : Expr) (ty : Typ)            -- NEW: subsumption cast
```

Also update `Typed.Binder` to a structure where the type is non-optional and ignored variables still carry a type:

```lean
structure Binder where
  name : Option Var
  ty   : Typ
```

This replaces the `Untyped.Binder` inductive (which has `.none` without a type and `.named` with `Option Typ`).

Define `Const.ty`:

```lean
def Const.ty : Const → Typ
  | .int _  => .int
  | .bool _ => .bool
  | .unit   => .unit
```

Key decisions:
- `var` carries the type from the context lookup
- `Typed.Binder.named` carries a non-optional `Typ` (elaboration must resolve all binder types)
- `fix` has a non-optional `retTy : Typ` (the return type of the function)
- `app`, `match_`, `ifThenElse`, `unop`, `binop`, `deref` carry their result types
- `letIn` does NOT need an extra annotation — its type is `body.ty`
- `const`, `tuple`, `inj`, `ref`, `store`, `assert` do NOT need extra annotations — their types are determined by their subexpressions (`const` via `Const.ty`)
- `cast e ty` means "check `e.ty <: ty`"; it erases to just `e` at runtime

### 2. Define `Expr.ty`

```lean
def Expr.ty : Expr → Typ
  | .const c           => c.ty
  | .var _ ty          => ty
  | .unop _ _ ty       => ty
  | .binop _ _ _ ty    => ty
  | .fix self args retTy body => .arrow (arrowOfArgs args retTy)  -- or however the current type synthesis works
  | .app _ _ ty        => ty
  | .ifThenElse _ _ _ ty => ty
  | .letIn _ _ body    => body.ty
  | .ref e             => .ref e.ty
  | .deref _ ty        => ty
  | .store _ _         => .unit
  | .assert _          => .unit
  | .tuple es          => .tuple (es.map Expr.ty)
  | .inj tag arity e   => .sum ((List.replicate arity .empty).set tag e.ty)
  | .match_ _ _ ty     => ty
  | .cast _ ty         => ty
```

The exact shape of `fix` typing needs to match the current system. Currently, `Untyped.Expr.fix` has `retTy : Option Typ`. In the typed IR, this becomes non-optional. The function type is determined by the binder types and the return type.

### 3. Define `Typed.TypeError`

Define a structured error type in `Mica/TinyML/Typed.lean` for typing errors:

```lean
inductive TypeError where
  | undefinedVar (name : Var)
  | operatorMismatch (op : BinOp) (lhs rhs : Typ)
  | unaryMismatch (op : UnOp) (arg : Typ)
  | notAFunction (ty : Typ)
  | arityMismatch (expected actual : Nat)
  | typeMismatch (expected actual : Typ)
  | notASum (ty : Typ)
  | notARef (ty : Typ)
  | missingReturnType
  | subsumptionFailure (sub super : Typ)
```

The exact set of constructors should be determined by what `infer`/`check` actually need. The above is a starting point — add or remove variants as needed. Provide a `ToString` or `Repr` instance so errors can be displayed.

### 4. Type elaboration

Replace the trivial `elaborate` from Phase 1 with type elaboration. The core function is `infer`, which synthesizes a type and produces a typed expression:

```lean
def infer (Γ : TyCtx) : Untyped.Expr → Except TypeError (Typ × Typed.Expr)
```

Every expression form is handled by `infer`:
- `const` — synthesizes via `Const.ty`
- `var` — looks up the type in `Γ`
- `unop`, `binop` — infers operand types, computes result type
- `app` — infers function type, infers arguments, returns result type
- `ifThenElse` — infers condition, infers both branches, joins their types via `Typ.join` (defined in `Mica/TinyML/Typing.lean`)
- `match_` — infers scrutinee, infers all branches, joins their types via `Typ.join`
- `letIn` — infers bound expression, extends `Γ`, infers body
- `tuple` — infers each component
- `inj` — infers the payload, synthesizes the principal narrow sum
- `fix` — infers from binder annotations and body
- `ref`, `deref`, `store`, `assert` — standard

`check` is a thin wrapper — it infers, then tests subtyping:

```lean
def check (Γ : TyCtx) (e : Untyped.Expr) (expected : Typ) : Except TypeError Typed.Expr :=
  let (ty, e') ← infer Γ e
  if ty == expected then return e'
  else if Typ.sub ty expected then return .cast e' expected
  else .error (.subsumptionFailure ty expected)
```

This suffices for the current fragment. Later phases (with named types and polymorphism) may push more logic into `check`, but for now everything synthesizes.

The type elaboration at this stage does NOT need to handle polymorphism, named types, or unification. It only needs to propagate the types that are already present in the `Untyped.Expr` binders and compute result types for operators. Use `Typ.value` as a fallback when no type information is available.

### 5. Update `Typed.Expr.runtime`

The new `cast` constructor erases to just the inner expression:

```lean
| .cast e _ => e.runtime
```

All other constructors that gained type annotations just ignore them during erasure — the runtime translation drops types.

### 6. Prove `infer_runtime` and `check_runtime`

Replace the Phase 1 `elaborate_runtime` theorem with two mutual theorems stating that type elaboration preserves runtime behavior:

```lean
mutual
  theorem infer_runtime (Γ : TyCtx) (e : Untyped.Expr) (ty : Typ) (e' : Typed.Expr) :
      infer Γ e = .ok (ty, e') → e'.runtime = e.runtime

  theorem check_runtime (Γ : TyCtx) (e : Untyped.Expr) (expected : Typ) (e' : Typed.Expr) :
      check Γ e expected = .ok e' → e'.runtime = e.runtime
end
```

These are mutual because `infer` calls `check` and vice versa. `check_runtime` follows from `infer_runtime` plus the fact that `cast` erases to the identity. The proofs should be by induction on the elaboration, mirroring the structure of `infer`/`check`.

### 7. Verifier: mechanical update only

The verifier's `compile` function pattern-matches on `Typed.Expr`. Since constructors gained extra fields (the type annotations), the pattern matches need updating to bind (and ignore) the new fields. For example:

```lean
-- Before:
| .var x => ...
-- After:
| .var x _ty => ...
```

The new `cast` constructor should be handled as a no-op in the verifier — just compile the inner expression:

```lean
| .cast e _ty => compile S B Γ e
```

No verifier logic changes. No proof changes beyond accommodating the new constructor shapes.

## What NOT to do

- Do not change `compile` to use `Expr.ty` instead of computing types. That is Phase 2b.
- Do not change `compile_correct` or the verification theorems beyond mechanical pattern-match updates.
- Do not add named types, polymorphism, or subtyping with unfolding. That is Phase 3+.
- Do not change `ValHasType`, `wp`, or the operational semantics.
- Do not change `Untyped.Expr`.

## Verification

`lake build` must succeed and `lake run testsuite Examples/` must pass.
