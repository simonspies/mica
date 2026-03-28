# Phase 5: Expose Function Declarations at Verifier Layer

## Objective

Add SMT commands and monadic operations for declaring uninterpreted constants, unary functions, and binary functions. Wire through Command → ScopedM → VerifM. Fresh name generation checks all `Signature` components to avoid collisions.

## Step 1: Add commands (Command.lean)

Add to the `Command` inductive:
```lean
| declareUninterpretedConst (name : String) (sort : Srt) : Command Unit
| declareUnary (name : String) (arg : Srt) (ret : Srt) : Command Unit
| declareBinary (name : String) (arg1 arg2 : Srt) (ret : Srt) : Command Unit
```

Add serialization in `Command.query`:
```lean
| .declareUninterpretedConst name sort => s!"(declare-const {name} {sort.toSMTLIB})"
| .declareUnary name arg ret => s!"(declare-fun {name} ({arg.toSMTLIB}) {ret.toSMTLIB})"
| .declareBinary name arg1 arg2 ret => s!"(declare-fun {name} ({arg1.toSMTLIB} {arg2.toSMTLIB}) {ret.toSMTLIB})"
```

Add `Command.parseResponse` cases (all return `()` like `declareConst`).

Update `SmtState.step` to add declarations to the current frame's `Signature`:
- `declareUninterpretedConst name sort`: add `⟨name, sort⟩` to `frame.decls.consts`
- `declareUnary name arg ret`: add `⟨name, arg, ret⟩` to `frame.decls.unary`
- `declareBinary name arg1 arg2 ret`: add `⟨name, arg1, arg2, ret⟩` to `frame.decls.binary`

## Step 2: Add ScopedM constructors (Scoped.lean)

```lean
inductive ScopedM : Type → Type 1 where
  -- ... existing constructors ...
  | declareUninterpretedConst : String → Srt → (Unit → ScopedM α) → ScopedM α
  | declareUnary : String → Srt → Srt → (Unit → ScopedM α) → ScopedM α
  | declareBinary : String → Srt → Srt → Srt → (Unit → ScopedM α) → ScopedM α
```

Extend `ScopedM.translate` to emit the corresponding `Command` via `.exec`.

Add `FlatCtx.addConst`, `FlatCtx.addUnary`, `FlatCtx.addBinary` to update the appropriate `Signature` component.

Extend `ScopedM.eval` with inversion lemmas for the new constructors, following the pattern of `eval_declareConst`.

## Step 3: Add VerifM operations (Monad.lean)

```lean
inductive VerifM : Type → Type 1 where
  -- ... existing constructors ...
  | declConst : Option String → Srt → VerifM FOL.Const
  | declUnary : Option String → Srt → Srt → VerifM FOL.Unary
  | declBinary : Option String → Srt → Srt → Srt → VerifM FOL.Binary
```

These return the named declaration structures so callers can build `Const.uninterpreted`, `UnOp.uninterpreted`, or `BinOp.uninterpreted` terms directly from the result.

## Step 4: Fresh name generation (Monad.lean)

Update `TransState.freshVar` (or add `TransState.freshName`) to check freshness against **all** `Signature` components — not just `.vars`. Collect all names from `.vars`, `.consts`, `.unary`, `.binary` and pick a name not in any of them.

## Step 5: Extend `VerifM.translate` (Monad.lean)

```lean
| .declConst hint τ => do
    let name := st.freshName hint
    let decl : FOL.Const := ⟨name, τ⟩
    ScopedM.declareUninterpretedConst name τ fun () =>
      k (.ok decl) { st with decls := { st.decls with consts := decl :: st.decls.consts } }
```

Similarly for `declUnary`, `declBinary`.

## Step 6: Extend `VerifM.eval` (Monad.lean)

Add evaluation semantics. `declConst` is universally quantified over all interpretations (like `decl` for variables):
```lean
| .declConst _ τ => ∀ v : τ.denote,
    P decl { st with decls := ... } (ρ.updateConst τ decl.name v)
```

`declUnary` quantifies over all functions `τ₁.denote → τ₂.denote`. `declBinary` over all `τ₁.denote → τ₂.denote → τ₃.denote`.

## Step 7: Adequacy / inversion lemmas

Add `eval_declConst`, `eval_declUnary`, `eval_declBinary` following the pattern of `eval_decl` in Monad.lean.

## Verification

Run `lake build`. The new operations exist but are not called yet by any verification code.
