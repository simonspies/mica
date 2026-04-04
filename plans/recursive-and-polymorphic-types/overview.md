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

This stays close to the original type-system plan, but improves the architecture by separating:

- syntactic elaboration
- type-directed elaboration
- verification / SMT compilation

## 1. IRs

We use three expression languages inside `TinyML`:

- `TinyML.Source.Untyped.Expr`
  - output of syntactic elaboration
  - constructors resolved to tags and arities
  - no resolved polymorphic instantiations
  - no inserted casts

- `TinyML.Source.Typed.Expr`
  - output of type-directed elaboration
  - binders carry types
  - polymorphic globals are explicitly instantiated
  - verifier input

- `TinyML.Runtime.Expr`
  - executable language

Why this split:

- `compile_correct` currently relies on recursive compilation producing a type witness for each subexpression
- therefore the verifier cannot simply consume an untyped IR after the frontend has "already checked types"
- instead, the frontend must elaborate to a locally typed IR, and the verifier must check that IR locally while compiling it

Both source IRs erase to `Runtime.Expr`.

## 2. Types

Typed source uses monotypes plus explicit schemes for globals and type declarations.

Lean-style sketch:

```lean
abbrev TyVar := String
abbrev TypeName := String

inductive Ty where
  | tvar  : TyVar → Ty
  | int   : Ty
  | bool  : Ty
  | unit  : Ty
  | empty : Ty
  | value : Ty
  | arrow : Ty → Ty → Ty
  | tuple : List Ty → Ty
  | sum   : List Ty → Ty
  | named : TypeName → List Ty → Ty

structure Scheme where
  tparams : List TyVar
  body    : Ty

structure DataDecl where
  tparams  : List TyVar
  payloads : List Ty
```

Recursive variant declarations are stored in a map `TypeName → DataDecl`. Each `DataDecl` lists the payload types of the variants, implicitly viewed as a one-layer `Ty.sum`.

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
abbrev Global := String

structure Binder where
  name? : Option Var
  ty    : Ty

mutual
  structure Branch where
    binder : Binder
    body   : Expr

  inductive Expr where
    | var    : Var → Ty → Expr
    | global : Global → List Ty → Ty → Expr
    | int    : Int → Expr
    | bool   : Bool → Expr
    | unit   : Expr
    | lam    : Binder → Expr → Expr
    | app    : Expr → Expr → Ty → Expr
    | tuple  : List Expr → Expr
    | inj    : Nat → Nat → Expr → Expr
    | let_   : Binder → Expr → Expr → Expr
    | cast   : Expr → Ty → Expr
    | match_ : Expr → List Branch → Ty → Expr
end
```

Every node has a syntax-directed type:

```lean
def Expr.ty : Expr → Ty
  | .var _ ty        => ty
  | .global _ _ ty   => ty
  | .int _           => .int
  | .bool _          => .bool
  | .unit            => .unit
  | .lam b body      => .arrow b.ty body.ty
  | .app _ _ ty      => ty
  | .tuple es        => .tuple (es.map Expr.ty)
  | .let_ _ _ body   => body.ty
  | .inj tag arity e => .sum ((List.replicate arity .empty).set tag e.ty)
  | .cast _ ty       => ty
  | .match_ _ _ ty   => ty
```

Intended reading:

- `inj tag arity payload` is the structural core form for constructors; it synthesizes the principal narrow sum
- `cast e ty` means "check `e.ty <: ty`"; it erases to the identity (just `e`) at runtime
- `app f x ty` and `match_ scrut branches ty` carry their result types so the verifier need not recompute them
- `global g tyArgs ty` carries both the type instantiation (`tyArgs`, needed by the verifier) and the instantiated type (`ty`)

We do not add a separate explicit `unfold` node. Recursive structure is exposed only by typed `match`.

## 4. Untyped To Typed Elaboration

Type-directed elaboration performs the work that we do not want in the verifier:

- instantiate polymorphic globals
- propagate expected types
- insert `cast`
- choose result types for `app` and `match`

This keeps the verifier mostly syntax-directed and proof-friendly.

Elaboration may use mutable metavariables internally. Those metavariables are an implementation device of elaboration only; they do not appear in `Source.Typed.Expr`. The verifier checks the elaborated typed term case by case, so we do not need a proof of the inference algorithm itself.

This is the main benefit of the architecture: unification is confined to elaboration. The verifier consumes a meta-free typed term and does not need to solve type variables.

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
Ty.sum
  [ Ty.empty
  , Ty.tuple
      [ Ty.int
      , Ty.sum [Ty.unit, Ty.empty]
      , Ty.sum [Ty.unit, Ty.empty]
      ]
  ]
```

Elaboration instantiates `size` to `tree ?a → int` and solves:

```lean
Ty.sum
  [ Ty.empty
  , Ty.tuple
      [ Ty.int
      , Ty.sum [Ty.unit, Ty.empty]
      , Ty.sum [Ty.unit, Ty.empty]
      ]
  ]
<:
Ty.named "tree" [?a]
```

by right-unfolding the target and unifying structurally, which forces `?a := Ty.int`.

The same mechanism handles let-bound constructor values:

```lean
let x = Node (1, Empty, Empty) in size x
```

without any special case — `x` has the narrow structural type, and the cast to `tree int` is inserted at the call site.

Nullary constructors behave identically. `Empty` synthesizes `Ty.sum [Ty.unit, Ty.empty]`, and any needed datatype instantiation is recovered from use-site constraints.

## 6. Subtyping And Unfolding

Subtyping remains structural except for named recursive types.

The key rule is:

```lean
sub Γ S (.named T args) = true
```

when the unfolded body of `T args` exists and:

```lean
sub Γ S (unfoldType Γ T args) = true
```

That is, recursive named types may unfold on the right.

During elaboration we use the same shape of relation, but with metavariables and assignment on the right-hand side. Conceptually:

```lean
subtypeSolve : InferState → Ty → Ty → Option InferState
```

The pure verifier check is the meta-free fragment of this same procedure.

There is no general left-unfolding rule in subtyping.

Instead, `match` is the only place that exposes recursive structure on the left. Operationally, checking a typed match uses a rule of the form:

```lean
check Γ (.match_ scrut branches retTy) :=
  match scrut.ty with
  | .sum ts =>
      -- check branches against ts and retTy
  | .named T args =>
      -- unfold one layer, require unfoldType Γ T args = .sum ts,
      -- then check branches against ts and retTy
  | _ => false
```

Why this restriction:

- it keeps recursive variants opaque by default
- it gives one obvious place where recursive structure becomes visible
- it avoids needing projections, application, dereference, and other eliminators to know about recursive representation

### Termination

The new right-unfolding step terminates by a lexicographic measure on `(size of left-hand type, right-unfolding allowed)`.

Right-unfolding replaces `named T args` with its (potentially larger) body and sets the flag to `false`, decreasing the second component. The subsequent structural recursive calls decompose both sides into subterms, decreasing the first component, which resets the flag to `true`. This means recursive occurrences of `named T args` inside the unfolded body can themselves be unfolded when reached, because at that point the left-hand subterm is strictly smaller.

## 7. Rejected For Now

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

## 8. Runtime Preservation

Both source languages erase to runtime:

```lean
Source.Untyped.Expr.runtime : Source.Untyped.Expr → Runtime.Expr
Source.Typed.Expr.runtime   : Source.Typed.Expr   → Runtime.Expr
```

`cast` erases to the identity: `(Expr.cast e ty).runtime = e.runtime`.

The key elaboration theorem should state:

```lean
theorem elaborate_runtime
    (h : elaborate e = e') :
    e.runtime = e'.runtime
```

This is why the verifier can move to typed source without changing the top-level semantic statements, which can remain phrased over untyped source.

## 9. Verifier Consequence

`compile` should move from untyped source to typed source.

The verifier still checks types, but only locally. In particular, it no longer has to invent:

- polymorphic instantiations
- where casts are needed
- where recursive structure should be exposed

That information is already fixed by typed elaboration.
