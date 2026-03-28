# Phase 4: Add `.uninterpreted` Constructors

## Objective

Add `Const.uninterpreted`, `UnOp.uninterpreted`, `BinOp.uninterpreted`. Define separate `Const.wfIn`, `UnOp.wfIn`, `BinOp.wfIn` predicates. Evaluation uses `Env` for the uninterpreted cases. Printing emits function application syntax.

## Step 1: Add constructors (Terms.lean)

```lean
inductive Const : Srt → Type where
  | i    : Int  → Const .int
  | b    : Bool → Const .bool
  | unit : Const .value
  | vnil : Const .vallist
  | uninterpreted : String → (τ : Srt) → Const τ

inductive UnOp : Srt → Srt → Type where
  -- ... existing 15 constructors ...
  | uninterpreted : String → (τ₁ τ₂ : Srt) → UnOp τ₁ τ₂

inductive BinOp : Srt → Srt → Srt → Type where
  -- ... existing 10 constructors ...
  | uninterpreted : String → (τ₁ τ₂ τ₃ : Srt) → BinOp τ₁ τ₂ τ₃
```

## Step 2: Extend evaluation (Terms.lean)

Add the uninterpreted case to each (Phase 3 already added the `Env` parameter):
```lean
@[simp] def Const.denote : Env → Const τ → τ.denote
  -- ... existing cases with _ for env ...
  | ρ, .uninterpreted name τ => ρ.consts τ name

@[simp] def UnOp.eval : Env → UnOp τ₁ τ₂ → τ₁.denote → τ₂.denote
  -- ... existing cases with _ for env ...
  | ρ, .uninterpreted name τ₁ τ₂, x => ρ.unary τ₁ τ₂ name x

@[simp] def BinOp.eval : Env → BinOp τ₁ τ₂ τ₃ → τ₁.denote → τ₂.denote → τ₃.denote
  -- ... existing cases with _ for env ...
  | ρ, .uninterpreted name τ₁ τ₂ τ₃, x, y => ρ.binary τ₁ τ₂ τ₃ name x y
```

## Step 3: Define operator `wfIn` predicates (Terms.lean)

Separate definitions rather than inlining into `Term.wfIn`:
```lean
def Const.wfIn : Const τ → Signature → Prop
  | .uninterpreted name τ, Δ => ⟨name, τ⟩ ∈ Δ.consts  -- using FOL.Const membership
  | _, _                      => True

def UnOp.wfIn : UnOp τ₁ τ₂ → Signature → Prop
  | .uninterpreted name τ₁ τ₂, Δ => ⟨name, τ₁, τ₂⟩ ∈ Δ.unary  -- using FOL.Unary membership
  | _, _                           => True

def BinOp.wfIn : BinOp τ₁ τ₂ τ₃ → Signature → Prop
  | .uninterpreted name τ₁ τ₂ τ₃, Δ => ⟨name, τ₁, τ₂, τ₃⟩ ∈ Δ.binary
  | _, _                              => True
```

## Step 4: Update `Term.wfIn` (Terms.lean)

Integrate the operator `wfIn` predicates:
```lean
def Term.wfIn : Term τ → Signature → Prop
  | .var τ x, Δ          => ⟨x, τ⟩ ∈ Δ.vars
  | .const c, Δ          => c.wfIn Δ
  | .unop op a, Δ        => op.wfIn Δ ∧ a.wfIn Δ
  | .binop op a b, Δ     => op.wfIn Δ ∧ a.wfIn Δ ∧ b.wfIn Δ
  | .ite c t e, Δ        => c.wfIn Δ ∧ t.wfIn Δ ∧ e.wfIn Δ
```

Note: for concrete operators, `op.wfIn Δ` reduces to `True`, so this is backward-compatible with Phase 2's definition (modulo the extra `True ∧` which simp handles).

## Step 5: Update `Env.agreeOn` (Variables.lean)

`Env.agreeOn` was already defined over all four `Signature` components in Phase 1. No change needed to the definition.

## Step 6: Update `Term.eval_env_agree` (Terms.lean)

The proof gains new cases. For `.const (.uninterpreted name τ)`: `wfIn` gives `⟨name, τ⟩ ∈ Δ.consts`, and `agreeOn` gives agreement on `.consts`, so `ρ.consts τ name = ρ'.consts τ name`. Similarly for unary/binary uninterpreted ops.

Add helper lemmas:
```lean
theorem Const.denote_env_agree (c : Const τ) (h : c.wfIn Δ) (ha : Env.agreeOn Δ ρ ρ') :
    c.denote ρ = c.denote ρ'

theorem UnOp.eval_env_agree (op : UnOp τ₁ τ₂) (h : op.wfIn Δ) (ha : Env.agreeOn Δ ρ ρ') :
    op.eval ρ = op.eval ρ'

theorem BinOp.eval_env_agree (op : BinOp τ₁ τ₂ τ₃) (h : op.wfIn Δ) (ha : Env.agreeOn Δ ρ ρ') :
    op.eval ρ = op.eval ρ'
```

These make `Term.eval_env_agree` compositional.

## Step 7: Extend printing (Printing.lean)

SMT-LIB serialization — add to existing `toSMTLIB` functions:
```lean
-- Const:
| .uninterpreted name _ => name

-- UnOp:
| .uninterpreted name _ _ => name

-- BinOp:
| .uninterpreted name _ _ _ => name
```

The existing `Term.toSMTLIB` already wraps unop/binop as `(op arg1 ...)`, so this produces correct SMT-LIB like `(fibonacci x)`.

Human-readable printing: same, use the function name.

## Step 8: Fix exhaustiveness in downstream code

Every `match` on `Const`, `UnOp`, `BinOp` needs the new case:
- `compileOp` (Expressions.lean:23): add catch-all returning `none` (compilation never produces uninterpreted ops)
- `compileUnop` (Expressions.lean:69): same
- `compileOp_eval`, `compileUnop_eval`: proofs — new case is vacuous since compilation returns `none`

## Step 9: Update `checkWf` functions

`Term.checkWf`, `Formula.checkWf`: add computational checks for the new `wfIn` cases, checking operator membership in `Signature`.

## Verification

Run `lake build`. The new constructors exist but are not produced by any code path — they're only usable by manually constructing terms.
