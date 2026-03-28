# Phase 1: Generalize `Env` and `Signature`

## Objective

Change `Env` from a type alias to a structure with four fields. Introduce `Signature` with named declaration structures replacing `VarCtx` in FOL/SMT contexts. Define `Env.agreeOn` over the full signature from the start. Add `Env.updateConst`, `Env.updateUnary`, `Env.updateBinary` alongside existing `Env.update`. Nothing uses the new fields yet.

## Step 1: Define `Signature` and its component types (Variables.lean)

```lean
namespace FOL

structure Const where
  name : String
  sort : Srt
  deriving DecidableEq, Repr

structure Unary where
  name : String
  arg  : Srt
  ret  : Srt
  deriving DecidableEq, Repr

structure Binary where
  name : String
  arg1 : Srt
  arg2 : Srt
  ret  : Srt
  deriving DecidableEq, Repr

end FOL

structure Signature where
  vars   : VarCtx
  consts : List FOL.Const
  unary  : List FOL.Unary
  binary : List FOL.Binary
```

Add `Signature.empty`, and operations to extend each component (e.g., `Signature.addVar`, `Signature.addConst`, etc.). No coercion to `VarCtx` — code that needs `.vars` projects explicitly.

## Step 3: Restructure `Env` (Variables.lean)

Current definition (line 45):
```lean
def Env := (τ : Srt) → String → τ.denote
```

New definition:
```lean
structure Env where
  vars   : (τ : Srt) → String → τ.denote
  consts : (τ : Srt) → String → τ.denote
  unary  : (τ₁ τ₂ : Srt) → String → τ₁.denote → τ₂.denote
  binary : (τ₁ τ₂ τ₃ : Srt) → String → τ₁.denote → τ₂.denote → τ₃.denote
```

Update `Env.lookup` (line 47) to access `.vars`:
```lean
def Env.lookup (ρ : Env) (τ : Srt) (x : String) : τ.denote := ρ.vars τ x
```

Update `Env.update` (line 49) to update `.vars`, preserving other fields:
```lean
def Env.update (ρ : Env) (τ : Srt) (x : String) (v : τ.denote) : Env :=
  { ρ with vars := fun τ' y => if h : τ' = τ ∧ y = x then h.1 ▸ v else ρ.vars τ' y }
```

Add analogous update operations for the new fields:
```lean
def Env.updateConst (ρ : Env) (τ : Srt) (x : String) (v : τ.denote) : Env :=
  { ρ with consts := fun τ' y => if h : τ' = τ ∧ y = x then h.1 ▸ v else ρ.consts τ' y }

def Env.updateUnary (ρ : Env) (τ₁ τ₂ : Srt) (x : String) (f : τ₁.denote → τ₂.denote) : Env :=
  { ρ with unary := fun τ₁' τ₂' y =>
    if h : τ₁' = τ₁ ∧ τ₂' = τ₂ ∧ y = x then h.1 ▸ h.2.1 ▸ f else ρ.unary τ₁' τ₂' y }

def Env.updateBinary (ρ : Env) (τ₁ τ₂ τ₃ : Srt) (x : String) (f : τ₁.denote → τ₂.denote → τ₃.denote) : Env :=
  { ρ with binary := fun τ₁' τ₂' τ₃' y =>
    if h : τ₁' = τ₁ ∧ τ₂' = τ₂ ∧ τ₃' = τ₃ ∧ y = x then h.1 ▸ h.2.1 ▸ h.2.2.1 ▸ f else ρ.binary τ₁' τ₂' τ₃' y }
```

Update `Env.empty`:
```lean
def Env.empty : Env :=
  ⟨fun _ _ => default, fun _ _ => default, fun _ _ _ _ => default, fun _ _ _ _ _ => default⟩
```

Simp lemmas (lines 56-114) should go through with minor adjustments since `lookup`/`update` still operate on `.vars`.

## Step 4: Define `Env.agreeOn` over full `Signature` (Variables.lean)

```lean
def Env.agreeOn (Δ : Signature) (ρ ρ' : Env) : Prop :=
  (∀ v ∈ Δ.vars, ρ.vars v.sort v.name = ρ'.vars v.sort v.name) ∧
  (∀ c ∈ Δ.consts, ρ.consts c.sort c.name = ρ'.consts c.sort c.name) ∧
  (∀ u ∈ Δ.unary, ρ.unary u.arg u.ret u.name = ρ'.unary u.arg u.ret u.name) ∧
  (∀ b ∈ Δ.binary, ρ.binary b.arg1 b.arg2 b.ret b.name = ρ'.binary b.arg1 b.arg2 b.ret b.name)
```

Note: `c.sort`, `u.arg`, etc. use the named fields from `FOL.Const`, `FOL.Unary`, `FOL.Binary`.

Update `agreeOn_refl`, `_symm`, `_trans`, `_mono`, `_update` (lines 76-99). These should be straightforward — each is a conjunction of four independent statements. `_update` only affects the `.vars` component, so the other three conjuncts are preserved trivially.

## Step 5: Replace `VarCtx` with `Signature` in FOL layer

Replace `Δ : VarCtx` with `Δ : Signature` in these definitions, accessing `Δ.vars` for variable membership:

- `Term.wfIn` (Terms.lean:62): `∀ v ∈ t.freeVars, v ∈ Δ.vars`
- `Term.checkWf` (Terms.lean:65): check against `Δ.vars`
- `Term.checkWf_ok` (Terms.lean:70)
- `Term.wfIn_mono` (Terms.lean:82): needs component-wise subset on `Signature`
- `Term.eval_env_agree` (Terms.lean:123): takes `Δ : Signature`, uses full `agreeOn` as hypothesis — proof only needs the `.vars` component for now
- `Formula.wfIn` (Formulas.lean:42): access `Δ.vars`; quantifiers extend via `{ Δ with vars := ⟨x, τ⟩ :: Δ.vars }`
- `Formula.checkWf` (Formulas.lean:45)
- `Formula.wfIn_body_of_wfIn_quant` (Formulas.lean:65)
- `Context.wfIn` (Formulas.lean:74)
- `Formula.eval_env_agree` (Formulas.lean:106): takes full `agreeOn`
- `Formula.eval_update_not_in_sig` (Formulas.lean:147)
- Remove `abbrev Signature := VarCtx` (Formulas.lean:72) — now imported from Variables.lean
- All `Subst.wfIn` and related in Subst.lean

Watch for: `Subst.eval` (Subst.lean:166) constructs an `Env` as a raw lambda — must now construct a full `Env` structure. Same for quantifier cases in `Formula.eval` that build environments.

## Step 6: Replace `VarCtx` with `Signature` in SMT state

- `SmtFrame.decls` (Command.lean:11): change type to `Signature`
- `SmtState.allDecls` (Command.lean:93): merge signatures across frames
- `Satisfiable` (Command.lean:132): takes `Signature`
- `FlatCtx.decls` (Scoped.lean:33): change to `Signature`
- `FlatCtx.addDecl` (Scoped.lean:41): adds to `.vars` component
- `SmtState.flatten` (Scoped.lean:50): merges signatures

## Step 7: Keep `VarCtx` for variable-list uses

These stay as `List Var`:
- `Bindings` in Verifier/Utils.lean
- `FiniteSubst` in Verifier/Utils.lean
- `Spec.argVars` in Specifications.lean

## Verification

Run `lake build`. Every file should compile. No semantic change — the new `Signature` fields are empty, `Env`'s new fields are defaulted, and `agreeOn`'s new conjuncts are vacuously true.
