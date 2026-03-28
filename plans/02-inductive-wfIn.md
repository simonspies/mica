# Phase 2: Make `wfIn` Inductive

## Objective

Change `Term.wfIn` and `Formula.wfIn` from "collect free vars, check membership" to recursive predicates that inspect each node. Update `checkWf` to match. No bridge lemmas to the old definition — all downstream proofs are updated to use the inductive structure directly.

## Step 1: Replace `Term.wfIn` (Terms.lean)

Current (line 62):
```lean
def Term.wfIn (t : Term τ) (Δ : Signature) : Prop :=
  ∀ v ∈ t.freeVars, v ∈ Δ.vars
```

New — recursive:
```lean
def Term.wfIn : Term τ → Signature → Prop
  | .var τ x, Δ     => ⟨x, τ⟩ ∈ Δ.vars
  | .const _, _      => True
  | .unop _ a, Δ     => a.wfIn Δ
  | .binop _ a b, Δ  => a.wfIn Δ ∧ b.wfIn Δ
  | .ite c t e, Δ    => c.wfIn Δ ∧ t.wfIn Δ ∧ e.wfIn Δ
```

Note: `.const` is `True` and `.unop`/`.binop` only recurse into subterms. Phase 4 will add cases for `.uninterpreted` checking against `Δ.consts`/`.unary`/`.binary`.

## Step 2: Update `Term.checkWf` (Terms.lean)

Replace the `freeVars.find?` approach with a recursive check matching `wfIn`:
```lean
def Term.checkWf : Term τ → Signature → Except String Unit
  | .var τ x, Δ     => if ⟨x, τ⟩ ∈ Δ.vars then .ok () else .error s!"variable {repr x} not in scope"
  | .const _, _      => .ok ()
  | .unop _ a, Δ     => a.checkWf Δ
  | .binop _ a b, Δ  => do a.checkWf Δ; b.checkWf Δ
  | .ite c t e, Δ    => do c.checkWf Δ; t.checkWf Δ; e.checkWf Δ
```

Update `Term.checkWf_ok` (line 70): proof changes from `List.find?` argument to induction on the term.

## Step 3: Update `Term.wfIn` lemmas

- `Term.wfIn_mono` (line 82): prove by induction on term. Needs a notion of `Signature` subset (component-wise). For now only `.vars` subset matters.
- `Term.wfIn_freeVars` (line 79): may be deleted or restated — it said `t.wfIn t.freeVars` which no longer type-checks directly. Restate if needed as `t.wfIn (Signature with vars := t.freeVars ...)`.

## Step 4: Replace `Formula.wfIn` (Formulas.lean)

New — recursive:
```lean
def Formula.wfIn : Formula → Signature → Prop
  | .true_, _             => True
  | .false_, _            => True
  | .eq _ t₁ t₂, Δ       => t₁.wfIn Δ ∧ t₂.wfIn Δ
  | .unpred _ t, Δ        => t.wfIn Δ
  | .binpred _ t₁ t₂, Δ  => t₁.wfIn Δ ∧ t₂.wfIn Δ
  | .not φ, Δ             => φ.wfIn Δ
  | .and φ ψ, Δ           => φ.wfIn Δ ∧ ψ.wfIn Δ
  | .or φ ψ, Δ            => φ.wfIn Δ ∧ ψ.wfIn Δ
  | .implies φ ψ, Δ       => φ.wfIn Δ ∧ ψ.wfIn Δ
  | .forall_ x τ φ, Δ     => φ.wfIn { Δ with vars := ⟨x, τ⟩ :: Δ.vars }
  | .exists_ x τ φ, Δ     => φ.wfIn { Δ with vars := ⟨x, τ⟩ :: Δ.vars }
```

Update `Formula.checkWf` and `Formula.checkWf_ok` to match.

## Step 5: Update `Formula.wfIn` lemmas

- `Formula.wfIn_body_of_wfIn_quant` (Formulas.lean:65): now follows directly from the definition.
- `Context.wfIn` (Formulas.lean:74): unchanged in structure, just uses new `Formula.wfIn`.

## Step 6: Update downstream `wfIn` definitions

These define `wfIn` in terms of `Term.wfIn`/`Formula.wfIn` — they should mostly need proof adjustments only:

- `Atom.wfIn` (Atoms.lean:139): delegates to `Term.wfIn`
- `Atom.checkWf` (Atoms.lean:144)
- `Assertion.wfIn` (Assertions.lean:76): recursive, extends signature with let-bound vars
- `Assertion.checkWf` (Assertions.lean:85)
- `PredTrans.wfIn` (PredicateTransformers.lean:31)
- `Spec.wfIn` (Specifications.lean:59)
- `compileUnop_wfIn`, `compileOp_wfIn` (Expressions.lean:77, 101)
- `Subst.wfIn` (Subst.lean:24)

Key: proofs that previously used `freeVars` membership + list reasoning now use induction on the term/formula structure. This is more natural and scales to Phase 4.

## Verification

Run `lake build`. Semantics are unchanged — the recursive predicate is equivalent to the membership-based one, just stated differently.
