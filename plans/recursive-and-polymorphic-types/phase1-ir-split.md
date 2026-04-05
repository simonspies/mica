# Phase 1: IR Split

## Goal

Split the current `TinyML.Expr` into two expression types — `Untyped.Expr` and `Typed.Expr` (initially identical) — in separate files with shared common definitions. Rename `Type_` to `Typ` everywhere. Wire up a trivial elaboration function between them. Move the verifier to consume `Typed.Expr`. The project must build and all existing functionality must be preserved.

## Background

Currently there is one source expression type (`TinyML.Expr` in `Mica/TinyML/Expr.lean`) and one runtime expression type (`Runtime.Expr` in `Mica/TinyML/RuntimeExpr.lean`). The verifier (`Mica/Verifier/`) consumes `TinyML.Expr` directly. The frontend (`Mica/Frontend/`) produces `TinyML.Expr`.

After this phase, the pipeline becomes:

```
Frontend → Untyped.Expr → elaborate → Typed.Expr → Verifier
                               ↘                      ↘
                           (identity)            (unchanged logic)
```

## File Layout

Currently `Mica/TinyML/Expr.lean` contains everything: `Var`, `Type_`, `BinOp`, `UnOp`, `Const`, `Binder`, `Expr`, `Decl`, `Program`. This must be split into three files:

### `Mica/TinyML/Common.lean` — shared definitions

Extract from the current `Expr.lean`:

- `TinyML.Var` (= `String`)
- `TinyML.Typ` — renamed from `Type_` (with `DecidableEq`, `BEq`, `LawfulBEq` instances)
- `TinyML.BinOp`
- `TinyML.UnOp`
- `TinyML.Const`
- `TinyML.TyCtx` (= `Var → Option Typ`)

The rename `Type_` → `Typ` applies throughout the entire codebase: Common, Untyped, Typed, Runtime, Verifier, Frontend, Typing, etc. This is a mechanical find-and-replace.

### `Mica/TinyML/Untyped.lean` — untyped source IR

Imports `Common`. Contains:

- `Untyped.Binder` — the current `TinyML.Binder` (carries `Option Typ`)
- `Untyped.Expr` — the current `TinyML.Expr`
- `Untyped.Decl` — the current `TinyML.Decl`
- `Untyped.Program` — the current `TinyML.Program`
- The `DecidableEq` / `BEq` instances for these types

The namespace is `Untyped` (or `TinyML.Untyped`). These types are structurally identical to the current definitions — just under a new namespace.

### `Mica/TinyML/Typed.lean` — typed source IR

Imports `Common`. Contains:

- `Typed.Binder` — identical to `Untyped.Binder` at this stage
- `Typed.Expr` — identical to `Untyped.Expr` at this stage
- `Typed.Decl` — identical to `Untyped.Decl` at this stage
- `Typed.Program` — identical to `Untyped.Program` at this stage

### What happens to `Mica/TinyML/Expr.lean`

Delete it. All contents should be moved to `Common.lean` and `Untyped.lean`, and all consumers updated.

## Other Deliverables

### Define `elaborate`

Define a function that structurally translates from `Untyped.Expr` to `Typed.Expr`:

```lean
def elaborate : Untyped.Expr → Typed.Expr
```

This is a straightforward recursive copy — every constructor maps to the corresponding constructor. Also define the corresponding functions for `Binder`, `Const`, `Decl`, and `Program`.

This function will become non-trivial in Phase 2. For now it is the identity (up to namespace).

### Define `Typed.Expr.runtime`

Define:

```lean
def Typed.Expr.runtime : Typed.Expr → Runtime.Expr
```

matching the structure of the existing `TinyML.Expr.runtime` (in `Mica/TinyML/RuntimeExpr.lean`). Also define `Typed.Binder.runtime`, `Typed.Const.runtime`, `Typed.Decl.runtime`, `Typed.Program.runtime`.

The existing `TinyML.Expr.runtime` should be renamed to `Untyped.Expr.runtime`.

### Prove `elaborate_runtime`

Prove:

```lean
theorem elaborate_runtime (e : Untyped.Expr) :
    (elaborate e).runtime = e.runtime
```

This should be a straightforward induction since both sides do the same thing. Also prove the `Program`-level version.

### Update the verifier to consume `Typed.Expr`

The verifier files that reference `TinyML.Expr` must be updated to reference `Typed.Expr` instead. The key files are:

- `Mica/Verifier/Expressions.lean` — `compile` takes `Untyped.Expr`, change to `Typed.Expr`
- `Mica/Verifier/Functions.lean` — `checkSpec` takes `Untyped.Expr`, change to `Typed.Expr`
- `Mica/Verifier/Programs.lean` — `Program.check` takes `Untyped.Program`, change to `Typed.Program`
- `Mica/Verifier/Utils.lean` — `Bindings` references `TinyML.Var`; this can stay since both IRs reuse the same `Var = String`

Since `Typed.Expr` is structurally identical to `Untyped.Expr` at this stage, the verifier code changes are purely mechanical namespace replacements. The proof structure should not change.

All references to `Type_` in the verifier become `Typ`.

### Update the frontend

The frontend currently produces `TinyML.Expr`. Update it to produce `Untyped.Expr`:

- `Mica/Frontend/Elaborate.lean` — `Frontend.Program.elaborate` returns `Untyped.Program`
- `Mica/Frontend/SpecParser.lean` — `Spec.parse` takes `Untyped.Expr`
- `Mica/Frontend/Printer.lean` — `TinyML.Program.print` becomes `Untyped.Program.print` (or similar)
- Any other files referencing `TinyML.Expr`, `TinyML.Binder`, etc.

All references to `Type_` in the frontend become `Typ`.

### Update `Mica/TinyML/RuntimeExpr.lean`

This file currently imports `Mica.TinyML.Expr` and defines `TinyML.Expr.runtime`. Update:

- Import `Common` and `Untyped` instead of `Expr`
- Rename `TinyML.Expr.runtime` to `Untyped.Expr.runtime`
- `Runtime.Expr` and `Runtime.Val` stay as they are

### Update `Main.lean`

The pipeline becomes:

```lean
let prog ← Frontend.Program.elaborate frontendProg    -- produces Untyped.Program
let typed := Typed.Program.elaborate prog              -- produces Typed.Program
let strategy := Program.verify typed                   -- consumes Typed.Program
```

### Update other TinyML files

- `Mica/TinyML/Typing.lean` — references `TinyML.Expr` and `Type_`; update to `Untyped.Expr` (or `Typed.Expr` if it's used by the verifier) and `Typ`
- `Mica/TinyML/OpSem.lean` — operational semantics are over `Runtime.Expr`, should not need changes beyond `Type_` → `Typ` if referenced
- `Mica/TinyML/WeakestPre.lean` — `wp` is over `Runtime.Expr`, should not need changes
- `Mica/TinyML/Heap.lean` — uses `Runtime.Location` and `Runtime.Val`, should not need changes

## What NOT to do

- Do not change the structure of any type (beyond the `Type_` → `Typ` rename). `Typed.Expr` must be identical to `Untyped.Expr`.
- Do not add type annotations, `Expr.ty`, or any typed-IR features. That is Phase 2.
- Do not change `Runtime.Expr` or the operational semantics.
- Do not change `ValHasType` or `wp`.

## Verification

After all changes, `lake build` must succeed and `lake run testsuite Examples/` must pass.
