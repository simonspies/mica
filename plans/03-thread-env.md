# Phase 3: Thread `Env` Through Operator Evaluation

## Objective

Add an `Env` parameter to `Const.denote`, `UnOp.eval`, and `BinOp.eval`. Existing concrete constructors ignore it. This forces statement updates across all `eval` and `agreeOn` lemmas but should not require deep proof changes since the parameter is unused.

## Step 1: Change `Const.denote` (Terms.lean)

Current (line 41):
```lean
@[simp] def Const.denote : Const τ → τ.denote
```

New:
```lean
@[simp] def Const.denote : Env → Const τ → τ.denote
  | _, .i n  => n
  | _, .b v  => v
  | _, .unit => Runtime.Val.unit
  | _, .vnil => []
```

## Step 2: Change `UnOp.eval` (Terms.lean)

Current (line 87):
```lean
@[simp] def UnOp.eval : UnOp τ₁ τ₂ → τ₁.denote → τ₂.denote
```

New:
```lean
@[simp] def UnOp.eval : Env → UnOp τ₁ τ₂ → τ₁.denote → τ₂.denote
  | _, .ofInt, n => ...
  -- all existing cases get a `_` for env
```

## Step 3: Change `BinOp.eval` (Terms.lean)

Same pattern:
```lean
@[simp] def BinOp.eval : Env → BinOp τ₁ τ₂ τ₃ → τ₁.denote → τ₂.denote → τ₃.denote
  | _, .add, a, b => a + b
  -- etc.
```

## Step 4: Update `Term.eval` (Terms.lean)

Current (line 116):
```lean
@[simp] def Term.eval (ρ : Env) : Term τ → τ.denote
  | .var τ y     => ρ.lookup τ y
  | .const c     => c.denote
  | .unop op a   => op.eval (a.eval ρ)
  | .binop op a b => op.eval (a.eval ρ) (b.eval ρ)
  | .ite c t e   => if c.eval ρ then t.eval ρ else e.eval ρ
```

New — pass `ρ` to operator evaluation:
```lean
@[simp] def Term.eval (ρ : Env) : Term τ → τ.denote
  | .var τ y     => ρ.lookup τ y
  | .const c     => c.denote ρ
  | .unop op a   => op.eval ρ (a.eval ρ)
  | .binop op a b => op.eval ρ (a.eval ρ) (b.eval ρ)
  | .ite c t e   => if c.eval ρ then t.eval ρ else e.eval ρ
```

## Step 5: Update `Term.eval_env_agree` (Terms.lean)

Current (line 123): proves `Term.eval ρ t = Term.eval ρ' t` when `agreeOn Δ ρ ρ'` and `t.wfIn Δ`.

The proof is by induction on `t`. For `.const`, `.unop`, `.binop` cases, the operator evaluation now takes `ρ`, so the proof needs to show that the operator result is the same under `ρ` and `ρ'`. Since concrete operators ignore `ρ`, this follows from the simp lemmas (they all match `| _, ...`).

This is the key observation: **because all existing constructors wildcard-match `Env`, `simp` should close these cases automatically.** The proofs should mostly go through with minor `simp` hint adjustments.

## Step 6: Cascade through FOL layer

- `Formula.eval` (Formulas.lean:90): calls `Term.eval` which now threads `ρ` internally — `Formula.eval` itself doesn't change signature.
- `Formula.eval_env_agree` (Formulas.lean:106): should go through since `Term.eval_env_agree` still holds.
- `Subst.eval` (Subst.lean:166): builds `Env` and calls `Term.eval` — signature of `Term.eval` unchanged.
- `Term.subst_eval` (Subst.lean): should go through.

## Step 7: Cascade through verifier layer

These use `Term.eval` or operator eval:
- `Atom.eval` / `Atom.toFormula_eval_iff` (Atoms.lean): may need simp hint updates if they unfold `UnOp.eval`
- `Atom.candidates_correct` (Atoms.lean): unfolds `UnOp.eval` — add `ρ` wildcard
- `Assertion.pre` / `Assertion.post` (Assertions.lean): call `Term.eval`, signature unchanged
- `Assertion.pre_env_agree` (Assertions.lean): cascades from `Term.eval_env_agree`
- `compileOp_eval` (Expressions.lean): unfolds `BinOp.eval` / `UnOp.eval` — add `ρ` wildcards in simp calls
- `PredTrans.apply` / `PredTrans.apply_env_agree` (PredicateTransformers.lean)
- `Spec.argsEnv` (Specifications.lean): builds `Env` via updates — only touches `.vars`, unaffected
- `typeConstraints_hold` (Specifications.lean): may unfold `UnOp.eval`

## Expected Difficulty

**Low-medium.** The signature of `Term.eval` doesn't change (it already takes `Env`). The internal threading is new but invisible to callers. The main work is updating `simp` calls that explicitly mention `UnOp.eval`, `BinOp.eval`, or `Const.denote` — they now take an extra argument but wildcard it away for concrete constructors.

## Verification

Run `lake build`. Semantics are unchanged — concrete operators still evaluate the same way.
