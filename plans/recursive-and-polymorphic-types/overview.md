# Recursive Types Design

## Summary

We keep the existing runtime language and the existing structural typing story for tuples, sums, and `empty`, but insert a typed source IR between frontend elaboration and verification.

The design goals are:

- preserve the current verifier style, where compilation carries enough type information to prove well-typedness of produced values
- avoid pushing more inference into the verifier
- keep recursive types simple enough that their representation is exposed in one place only

The resulting design is:

- recursive type declarations are supported only for variants
- non-recursive type declarations are elaborated away
- recursive variants remain nominal in typed source
- subtyping unfolds recursive named types only on the right
- `match` is the only construct that unfolds recursive types on the left
- constructors still synthesize narrow structural sums with `empty`
- the verifier consumes typed source, while top-level semantics remain stated over untyped source

This stays close to the original type-system, but improves the architecture by separating:

- syntactic elaboration (frontend)
- type-directed elaboration (untyped → typed)
- verification / SMT compilation

## 1. IRs

We use three expression languages inside `TinyML`:

- `Untyped.Expr`
  - output of frontend elaboration
  - constructors resolved to tags and arities
  - no resolved polymorphic instantiations
  - no inserted casts
  - includes type declarations for recursive variants

- `Typed.Expr`
  - output of type-directed elaboration
  - binders carry non-optional types
  - all function references use `global` with explicit type instantiation
  - functions declare their polymorphic type variables via `tparams`
  - verifier input

- `Runtime.Expr`
  - executable language

Why this split:

- `compile_correct` currently relies on recursive compilation producing a type witness for each subexpression
- therefore the verifier cannot simply consume an untyped IR after the frontend has "already checked types"
- instead, the frontend must elaborate to a locally typed IR, and the verifier must check that IR locally while compiling it

Both source IRs erase to `Runtime.Expr`.

## 2. Types

There is a single type language `Typ` shared across all IRs, extended with `tvar` and `named` constructors for recursive and polymorphic types:

```lean
abbrev TyVar := String
abbrev TypeName := String

inductive Typ where
  | tvar  : TyVar → Typ
  | int   : Typ
  | bool  : Typ
  | unit  : Typ
  | empty : Typ
  | value : Typ
  | arrow : Typ → Typ → Typ
  | tuple : List Typ → Typ
  | sum   : List Typ → Typ
  | ref   : Typ → Typ
  | named : TypeName → List Typ → Typ

structure Scheme where
  tparams : List TyVar
  body    : Typ

structure DataDecl where
  tparams  : List TyVar
  payloads : List Typ
```

Recursive variant declarations are stored in a type environment `Θ : TypeName → Option DataDecl`. Each `DataDecl` lists the payload types of the variants (constructors always carry a payload; the frontend inserts `unit` for nullary ones). `DataDecl.instantiate` substitutes type arguments for `tparams` and returns the corresponding `Typ.sum`.

Why only recursive variants:

- they give one distinguished structural eliminator, `match`
- that yields a single clear left-unfolding site
- recursive non-variant declarations would either require a general recursive structural type representation or many more unfolding sites

Non-recursive aliases and records are elaborated away because users expect them to behave transparently anyway.

## 3. Typed Source Sketch

The typed IR should be locally typed enough that every node has a syntax-directed type.

Lean-style sketch:

```lean
abbrev Var := String

structure Binder where
  name : Option Var
  ty   : Typ

inductive Expr where
  | const  : Const → Expr
  | var    : Var → Typ → Expr
  | global : Var → List Typ → Typ → Expr
  | unop   : UnOp → Expr → Typ → Expr
  | binop  : BinOp → Expr → Expr → Typ → Expr
  | fix    : List TyVar → Binder → List Binder → Typ → Expr → Expr
  | app    : Expr → List Expr → Typ → Expr
  | ifThenElse : Expr → Expr → Expr → Typ → Expr
  | letIn  : Binder → Expr → Expr → Expr
  | ref    : Expr → Expr
  | deref  : Expr → Typ → Expr
  | store  : Expr → Expr → Expr
  | assert : Expr → Expr
  | tuple  : List Expr → Expr
  | inj    : Nat → Nat → Expr → Expr
  | cast   : Expr → Typ → Expr
  | match_ : Expr → List (Binder × Expr) → Typ → Expr
```

Every node has a syntax-directed type via `Expr.ty`. Constants use `Const.ty`.

Intended reading:

- `inj tag arity payload` is the structural core form for constructors; it synthesizes the principal narrow sum
- `cast e ty` means "check `e.ty <: ty`"; it erases to the identity at runtime
- `app`, `match_`, `ifThenElse`, `unop`, `binop`, `deref` carry their result types so the verifier need not recompute them
- `global name tyArgs ty` is used for **all** function references (monomorphic functions use empty `tyArgs`); it carries both the type instantiation and the instantiated type
- `fix tparams self args retTy body` declares which type variables are polymorphic over via `tparams`

We do not add a separate explicit `unfold` node. Recursive structure is exposed only by typed `match`.

## 4. Untyped To Typed Elaboration

Type-directed elaboration performs the work that we do not want in the verifier:

- instantiate polymorphic globals
- propagate expected types
- insert `cast`
- choose result types for `app` and `match`
- generalize type variables on function definitions

This keeps the verifier mostly syntax-directed and proof-friendly.

The core elaboration functions are `infer` (synthesizes a type and produces a typed expression) and `check` (a thin wrapper that infers and then tests subtyping, inserting `cast` if needed).

Elaboration may use mutable metavariables internally for unification. Those metavariables are an implementation device of elaboration only; they do not appear in `Typed.Expr`. The verifier checks the elaborated typed term case by case, so we do not need a proof of the inference algorithm itself.

This is the main benefit of the architecture: unification is confined to elaboration. The verifier consumes a meta-free typed term and does not need to solve type variables.

**Key constraint:** after zonking, every `cast` node that elaboration inserts must pass the verifier's subtyping check. Elaboration's unification may be more powerful than the verifier's subtyping, but the concrete results it produces must be verifiable by the simpler check.

For applications, instantiation is determined by subtype checking with unification:

- synthesize the function expression
- if it is polymorphic, instantiate its type parameters with fresh metavariables
- synthesize the argument expression
- solve `argTy <: paramTy` by a subtype procedure that may assign those metavariables
- zonk the result and emit a meta-free typed term

If a metavariable remains unconstrained after elaboration, the term is rejected.

## 5. Constructor Elaboration

Constructors fit into the elaboration story without any special folding rule.

After constructor resolution, a constructor application is just `Expr.inj tag arity payload` and always synthesizes its principal narrow sum (see `Expr.ty` above). Named datatype parameters are never needed at the construction site. Instead, use sites recover them through subtype checking.

**Example.** Given:

```lean
size : ∀ a, tree a → int
```

For:

```lean
size (Node (1, Empty, Empty))
```

the constructor expression synthesizes:

```lean
Typ.sum
  [ Typ.empty
  , Typ.tuple
      [ Typ.int
      , Typ.sum [Typ.unit, Typ.empty]
      , Typ.sum [Typ.unit, Typ.empty]
      ]
  ]
```

Elaboration instantiates `size` to `tree ?a → int` and solves:

```lean
Typ.sum
  [ Typ.empty
  , Typ.tuple
      [ Typ.int
      , Typ.sum [Typ.unit, Typ.empty]
      , Typ.sum [Typ.unit, Typ.empty]
      ]
  ]
<:
Typ.named "tree" [?a]
```

by right-unfolding the target and unifying structurally, which forces `?a := Typ.int`.

The same mechanism handles let-bound constructor values:

```lean
let x = Node (1, Empty, Empty) in size x
```

without any special case — `x` has the narrow structural type, and the cast to `tree int` is inserted at the call site.

Nullary constructors behave identically. `Empty` synthesizes `Typ.sum [Typ.unit, Typ.empty]`, and any needed datatype instantiation is recovered from use-site constraints.

## 6. Subtyping And Unfolding

Subtyping remains structural except for named recursive types. The subtyping check takes a type environment `Θ` and a `FoldStatus` tracking whether right-unfolding is still allowed at the current level:

```lean
inductive FoldStatus where
  | canFold    -- right-unfolding is allowed
  | exhausted  -- right-unfolding has been used at this level

def Typ.sub (Θ : TypeEnv) : FoldStatus → Typ → Typ → Bool
```

The key rule is: `sub Θ .canFold s (.named T args)` unfolds the right-hand side via `TypeName.unfold Θ T args` and recurses with `.exhausted`.

There is no general left-unfolding rule in subtyping.

Instead, `match` is the only place that exposes recursive structure on the left. Both `infer` (during elaboration) and `compile` (in the verifier) unfold named scrutinee types when processing a `match_`.

Why this restriction:

- it keeps recursive variants opaque by default
- it gives one obvious place where recursive structure becomes visible
- it avoids needing projections, application, dereference, and other eliminators to know about recursive representation

### Termination

The right-unfolding step terminates by a lexicographic measure on `(size of left-hand type, FoldStatus)`.

Right-unfolding replaces `named T args` with its (potentially larger) body and sets the status to `.exhausted`, decreasing the second component. The subsequent structural recursive calls decompose both sides into subterms, decreasing the first component, which resets the status to `.canFold`. This means recursive occurrences of `named T args` inside the unfolded body can themselves be unfolded when reached, because at that point the left-hand subterm is strictly smaller.

## 7. ValHasType

`ValHasType` is parameterized by a type environment `Θ` and a type interpretation `ι`:

```lean
abbrev TyInterp := TyVar → (Runtime.Val → Prop)

inductive ValHasType (Θ : TypeEnv) (ι : TyInterp) : Runtime.Val → Typ → Prop where
  | int  : ValHasType Θ ι (.int n) .int
  | bool : ValHasType Θ ι (.bool b) .bool
  | unit : ValHasType Θ ι .unit .unit
  | tvar : ι α v → ValHasType Θ ι v (.tvar α)
  | inj  : ...
  | tuple : ...
  | any  : ValHasType Θ ι v .value
  | named : TypeName.unfold Θ T args = some ty →
            ValHasType Θ ι v ty →
            ValHasType Θ ι v (.named T args)
```

For polymorphic functions, `ι` is universally quantified in `Spec.isPrecondFor` — the specification holds for all type interpretations. The same `ι` is used for both arguments and return values. At a concrete call site, the caller instantiates `ι` to match the chosen type arguments.

## 8. Rejected For Now

We reject recursive non-variant declarations, for example:

```lean
type t = int * t
type t = t -> int
```

The issue is representation, not soundness. If such declarations are not kept nominal, then the core needs a general recursive structural type representation (`mu`-types or equivalent). If they are kept nominal, then more eliminators become unfolding sites.

That complexity is postponed deliberately.

If we later support recursive non-variant declarations, the intended extension is:

- keep them nominal in typed source
- insert unfoldings at the corresponding eliminators during type-directed elaboration

## 9. Runtime Preservation

Both source languages erase to runtime:

```lean
Untyped.Expr.runtime : Untyped.Expr → Runtime.Expr
Typed.Expr.runtime   : Typed.Expr   → Runtime.Expr
```

`cast` erases to the identity: `(Expr.cast e ty).runtime = e.runtime`.

The key elaboration theorems state:

```lean
theorem infer_runtime (Γ : TyCtx) (e : Untyped.Expr) (ty : Typ) (e' : Typed.Expr) :
    infer Γ e = .ok (ty, e') → e'.runtime = e.runtime

theorem check_runtime (Γ : TyCtx) (e : Untyped.Expr) (expected : Typ) (e' : Typed.Expr) :
    check Γ e expected = .ok e' → e'.runtime = e.runtime
```

This is why the verifier can move to typed source without changing the top-level semantic statements, which can remain phrased over untyped source.

## 10. Verifier Consequence

`compile` moves from untyped source to typed source. It takes a type environment `Θ` and checks the typed IR locally.

The verifier still checks types, but only locally. In particular, it no longer has to invent:

- polymorphic instantiations
- where casts are needed
- where recursive structure should be exposed

That information is already fixed by typed elaboration.
