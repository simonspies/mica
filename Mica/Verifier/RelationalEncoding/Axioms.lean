-- SUMMARY: Solver-facing axioms and validity theorems for the skolemized relational encoding.
import Mica.Verifier.RelationalEncoding.Skolemize
import Mica.Verifier.Guard


/-!
# Axioms of the func-form encoding

For each relation-marked recursive function, Skolemization exposes the
relational graph through two solver-facing symbols:

* `f_def(x)` says the function is defined on input `x`;
* `f_val(x)` is the value returned at `x` when it is defined.

If `body_def(x)` and `body_val(x)` are the definedness and value expressions
computed by the func-form body encoding, this file emits and proves valid three
axioms:

1. `body_def(x) -> f_def(x)` (`SpecFn.Axioms.definedIntro`);
2. `f_def(x) -> f_val(x) = body_val(x)` (`SpecFn.Axioms.value`);
3. `f_def(x) -> body_def(x)` (`SpecFn.Axioms.definedElim`).

Together, the two definedness implications make `f_def(x)` equivalent to the
body being defined, and the value axiom pins `f_val(x)` to the encoded body
value on that domain.

A declaration whose definedness is proved outright, by the termination check
that `[@@decreases]` triggers, needs neither implication: `f_def(x)` then holds
at every input, so only the value axiom is emitted (`SpecFn.Axioms.measured`).

For a fibonacci-style definition

```text
fib n = if n <= 1 then n else fib (n - 1) + fib (n - 2)
```

the func-form body has a definedness condition like

```text
n <= 1 || (fib_def(n - 1) && fib_def(n - 2))
```

and a value expression like

```text
if n <= 1 then n else fib_val(n - 1) + fib_val(n - 2)
```

so the emitted axioms state that the recursive-call definedness condition is
exactly `fib_def(n)`, and that `fib_val(n)` equals the conditional value
expression whenever `fib_def(n)` holds.
-/

namespace Verifier.RelationalEncoding
namespace Skolemize
open Relation

-- Axioms

/-- If the encoded body is defined on input `x`, the function is defined on `x`. -/
private def SpecFn.Axioms.definedIntro (fn : SpecFn) (x : TinyML.Var) (body : DefVal) : Formula :=
  .forall_ x .value
    [.unpred (.uninterpreted fn.defName .value) (.var .value x)]
    (.implies body.defined (fn.isDefined (.var .value x)))

/-- If the function is defined on input `x`, its solver-facing value equals the
encoded body value. -/
def SpecFn.Axioms.value (fn : SpecFn) (x : TinyML.Var) (body : DefVal) : Formula :=
  .forall_ x .value
    [.term (fn.call (.var .value x))]
    (.implies
      (fn.isDefined (.var .value x))
      (.eq .value (fn.call (.var .value x)) body.value))

/-- Converse of `SpecFn.Axioms.definedIntro`: if the function is defined on `x`, then the
encoded body is defined on `x`. Experimental — exposing this lets the SMT
backend propagate definedness from a parent call into its recursive subterms.
Unlike its converse it carries no trigger, so the solver instantiates it
without a matching pattern. -/
private def SpecFn.Axioms.definedElim (fn : SpecFn) (x : TinyML.Var) (body : DefVal) : Formula :=
  .all x .value
    (.implies (fn.isDefined (.var .value x)) body.defined)

/-- The solver-facing axioms emitted for a relation-marked function. All three
are quantified, so they are guarded (`.high`). -/
def SpecFn.Axioms.all (fn : SpecFn) (x : TinyML.Var) (body : DefVal) : List Axiom :=
  [⟨SpecFn.Axioms.definedIntro fn x body, .high⟩, ⟨SpecFn.Axioms.value fn x body, .high⟩,
   ⟨SpecFn.Axioms.definedElim fn x body, .high⟩]

/-- The axiom the solver e-matches on to unfold a recursive definition. -/
def SpecFn.Axioms.equation (fn : SpecFn) (x : TinyML.Var) (body : DefVal) : Axiom :=
  ⟨SpecFn.Axioms.value fn x body, .high⟩

/-- The subset of `SpecFn.Axioms.all` emitted once definedness is proved to hold
at every input. Both definedness implications then say nothing the totality
assertion does not already say, so the value axiom is all that remains. -/
def SpecFn.Axioms.measured (fn : SpecFn) (x : TinyML.Var) (body : DefVal) : List Axiom :=
  [⟨SpecFn.Axioms.value fn x body, .high⟩]

theorem SpecFn.Axioms.measured_subset_all {fn : SpecFn} {x : TinyML.Var} {body : DefVal} :
    ∀ ax ∈ SpecFn.Axioms.measured fn x body, ax ∈ SpecFn.Axioms.all fn x body := by
  simp [SpecFn.Axioms.measured, SpecFn.Axioms.all]

private theorem SpecFn.Axioms.all_wfIn {Δ : Signature} {fn : SpecFn} {x : String} {body : DefVal}
    (hΔx : (Δ.declVar ⟨x, .value⟩).wf)
    (hbody : body.wfIn (Δ.declVar ⟨x, .value⟩))
    (hfun : fn.func ∈ (Δ.declVar ⟨x, .value⟩).unary)
    (hrel : fn.defined ∈ (Δ.declVar ⟨x, .value⟩).unaryRel) :
    ∀ ax ∈ SpecFn.Axioms.all fn x body, ax.formula.wfIn Δ := by
  have hx : (Term.var .value x).wfIn (Δ.declVar ⟨x, .value⟩) :=
    var_value_wfIn hΔx (Signature.var_mem_declVar Δ ⟨x, .value⟩)
  have hdef : (fn.isDefined (.var .value x)).wfIn (Δ.declVar ⟨x, .value⟩) :=
    SpecFn.isDefined_wfIn hrel hΔx hx
  have hcall : (fn.call (.var .value x)).wfIn (Δ.declVar ⟨x, .value⟩) :=
    SpecFn.call_wfIn hfun hΔx hx
  intro ax hmem
  simp [SpecFn.Axioms.all] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact ⟨(by intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact hdef),
      hbody.2, hdef⟩
  · exact ⟨(by intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact hcall),
      hdef, hcall, hbody.1⟩
  · exact ⟨(by intro p hp; cases hp), hdef, hbody.2⟩


/-- The relation the current recursive body denotes is exactly the graph of the
func-form definedness predicate and the chosen value function. -/
def Agreement (sd : SpecDef) (ρ : Env) (body : DefVal) : Prop :=
  ∀ vin vout,
    SpecFn.Semantics.rel sd ρ vin vout ↔
      SpecFn.Semantics.defined sd ρ body vin ∧
        ValRel.toFunc (SpecFn.Semantics.rel sd ρ) vin = vout


/-- The definedness-introduction axiom is valid at the definedness least
fixpoint. This is the first solver-facing axiom and does not need the eventual
relation/graph equivalence. -/
private theorem SpecFn.Axioms.definedIntro_eval {sd : SpecDef} {ρ : Env}
    {body : DefVal} (henc : encodeDefVal sd = .ok body) :
    (SpecFn.Axioms.definedIntro sd.fn sd.x body).eval (SpecFn.Semantics.env sd ρ body) := by
  simp only [SpecFn.Axioms.definedIntro, Formula.eval]
  intro vin hbody
  exact (SpecFn.Semantics.env_isDefined (sd := sd) (ρ := ρ) (body := body) vin).mpr
    ((SpecFn.Semantics.defined_unfold (ρ := ρ) henc vin).mpr hbody)

/-- The relation induced by the relational encoding agrees with the graph of the
func-form definedness fixpoint and the chosen value
function. This is a theorem of the two encodings, not an external invariant:
tail compatibility handles old function symbols, freshness prevents the new
symbols from clobbering them, and the equivalence proof for the shared IR handles the
recursive body. -/
private theorem SpecFn.Semantics.rel_agreement {sd : SpecDef} {ρ : Env}
    (hlaw : sd.primitives.Lawful)
    {body : DefVal} (henc : encodeDefVal sd = .ok body)
    (hΓ : sd.Γ.Agreement ρ)
    (hΓwf : sd.Γ.wfIn sd.Δ)
    (hΔ : sd.Δ.wf) (hheadFresh : sd.Fresh) :
    Skolemize.Agreement sd ρ body := by
  intro vin vout
  constructor
  · intro hrel
    have hdefval :=
      SpecFn.Semantics.rel_complete hlaw henc hΓ hΓwf hΔ hheadFresh
        vin vout hrel
    have hdefined : ValRel.toDef (SpecFn.Semantics.rel sd ρ) vin := ⟨vout, hrel⟩
    have hfun :
      ValRel.toFunc (SpecFn.Semantics.rel sd ρ) vin = vout :=
      SpecFn.Semantics.rel_functional hlaw hΓwf.rel hΓ hΔ hheadFresh vin
        (ValRel.toFunc (SpecFn.Semantics.rel sd ρ) vin) vout
        (ValRel.toFunc_spec hdefined) hrel
    exact ⟨hdefval.1, hfun⟩
  · intro hgraph
    rcases hgraph with ⟨hdef, hfun⟩
    let vbody :=
      body.value.eval
        ((SpecFn.Semantics.env sd ρ body).updateConst .value sd.x vin)
    have hrelBody :
        SpecFn.Semantics.rel sd ρ vin vbody :=
      SpecFn.Semantics.rel_sound hlaw henc hΓ hΓwf hΔ hheadFresh vin vbody
        hdef rfl
    have hdefined : ValRel.toDef (SpecFn.Semantics.rel sd ρ) vin := ⟨vbody, hrelBody⟩
    have hchosen :
        vbody = ValRel.toFunc (SpecFn.Semantics.rel sd ρ) vin :=
      SpecFn.Semantics.rel_functional hlaw hΓwf.rel hΓ hΔ hheadFresh vin vbody
        (ValRel.toFunc (SpecFn.Semantics.rel sd ρ) vin)
        hrelBody (ValRel.toFunc_spec hdefined)
    exact SpecFn.Semantics.rel_sound hlaw henc hΓ hΓwf hΔ hheadFresh vin vout
      hdef (hchosen.trans hfun)

/-- The value axiom is valid at the canonical func-form interpretation extracted
from the relation. -/
private theorem SpecFn.Axioms.value_eval {sd : SpecDef} {ρ : Env}
    (hlaw : sd.primitives.Lawful)
    {body : DefVal} (henc : encodeDefVal sd = .ok body)
    (hΓ : sd.Γ.Agreement ρ)
    (hΓwf : sd.Γ.wfIn sd.Δ)
    (hΔ : sd.Δ.wf) (hheadFresh : sd.Fresh) :
    (SpecFn.Axioms.value sd.fn sd.x body).eval
      (SpecFn.Semantics.env sd ρ body) := by
  simp only [SpecFn.Axioms.value, Formula.eval]
  intro vin hdef
  have hsem := (SpecFn.Semantics.env_isDefined (sd := sd) (ρ := ρ) (body := body) vin).mp hdef
  rw [SpecFn.Semantics.env_call (sd := sd) (ρ := ρ) (body := body) vin]
  have hgraph := SpecFn.Semantics.rel_agreement hlaw henc hΓ hΓwf hΔ hheadFresh
  have hrel :
      SpecFn.Semantics.rel sd ρ vin
        (ValRel.toFunc (SpecFn.Semantics.rel sd ρ) vin) :=
    (hgraph vin (ValRel.toFunc (SpecFn.Semantics.rel sd ρ) vin)).mpr ⟨hsem, rfl⟩
  exact (SpecFn.Semantics.rel_complete hlaw henc hΓ hΓwf hΔ hheadFresh
    vin (ValRel.toFunc (SpecFn.Semantics.rel sd ρ) vin) hrel).2.symm

/-- Semantic validity of the converse definedness axiom: under the least
fixpoint of `SpecFn.Semantics.defined`, the `SpecFn.Semantics.defined`/`Skolemize.eval` unfolding goes both ways, so
`isDefined fn x` implies `body.defined` on `x`. -/
private theorem SpecFn.Axioms.definedElim_eval {sd : SpecDef} {ρ : Env}
    {body : DefVal} (henc : encodeDefVal sd = .ok body) :
    (SpecFn.Axioms.definedElim sd.fn sd.x body).eval (SpecFn.Semantics.env sd ρ body) := by
  simp only [SpecFn.Axioms.definedElim, Formula.all, Formula.eval]
  intro vin hdef
  exact (SpecFn.Semantics.defined_unfold (ρ := ρ) henc vin).mp
    ((SpecFn.Semantics.env_isDefined (sd := sd) (ρ := ρ) (body := body) vin).mp hdef)

/-- Validity of all three axioms at the canonical func-form
interpretation. -/
private theorem SpecFn.Axioms.all_eval {sd : SpecDef} {ρ : Env}
    (hlaw : sd.primitives.Lawful)
    {body : DefVal} (henc : encodeDefVal sd = .ok body)
    (hΓ : sd.Γ.Agreement ρ)
    (hΓwf : sd.Γ.wfIn sd.Δ)
    (hΔ : sd.Δ.wf) (hheadFresh : sd.Fresh) :
    ∀ ax ∈ SpecFn.Axioms.all sd.fn sd.x body,
      ax.formula.eval (SpecFn.Semantics.env sd ρ body) := by
  intro ax hmem
  simp [SpecFn.Axioms.all] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact SpecFn.Axioms.definedIntro_eval henc
  · exact SpecFn.Axioms.value_eval hlaw henc hΓ hΓwf hΔ hheadFresh
  · exact SpecFn.Axioms.definedElim_eval henc

/-! ## The verifier-facing entry point

`encode` is the top-level entry point for the verifier: given a relation-marked
function and its body, it returns the encoded body and the guarded solver-facing
axioms over the func-form symbols.

The lemmas below lift the corresponding `SpecFn.Axioms.*` results to the `encode`
level. -/

/-- Verifier-facing entry point for the func-form (definedness/value) encoding.
The declared symbols (`fn.rel`, `fn.func`, `fn.defined`) are determined by the
definition, so this returns only the data the encoder computes: the encoded body
and the solver-emitted axioms. -/
def encode (sd : SpecDef) : Except String (DefVal × List Axiom) := do
  let bv ← encodeDefVal sd
  pure (bv, SpecFn.Axioms.all sd.fn sd.x bv)

private theorem encode_inv {sd : SpecDef} {bv : DefVal} {axs : List Axiom}
    (hinfo : Skolemize.encode sd = .ok (bv, axs)) :
    encodeDefVal sd = .ok bv ∧ axs = SpecFn.Axioms.all sd.fn sd.x bv := by
  unfold Skolemize.encode at hinfo
  simp only [bind, Except.bind] at hinfo
  split at hinfo
  · cases hinfo
  rename_i bv' henc
  cases hinfo
  exact ⟨henc, rfl⟩

theorem encode_equation {sd : SpecDef} {bv : DefVal} {axs : List Axiom}
    (hinfo : Skolemize.encode sd = .ok (bv, axs)) :
    SpecFn.Axioms.equation sd.fn sd.x bv ∈ axs := by
  obtain ⟨_, rfl⟩ := encode_inv hinfo
  simp [SpecFn.Axioms.equation, SpecFn.Axioms.all]

theorem encode_measured {sd : SpecDef} {bv : DefVal} {axs : List Axiom}
    (hinfo : Skolemize.encode sd = .ok (bv, axs)) :
    ∀ ax ∈ SpecFn.Axioms.measured sd.fn sd.x bv, ax ∈ axs := by
  obtain ⟨_, rfl⟩ := encode_inv hinfo
  exact SpecFn.Axioms.measured_subset_all

/-- `definedIntro` read as a closure property: the encoded body being defined at
a value closes definedness of `fn` under that value. This is what the
termination check inducts on. -/
theorem encode_closed {sd : SpecDef} {bv : DefVal} {axs : List Axiom} {ρ : Env}
    (hinfo : Skolemize.encode sd = .ok (bv, axs))
    (haxs : ∀ ax ∈ axs, ax.formula.eval ρ) :
    ∀ v, bv.defined.eval (ρ.updateConst .value sd.x v) →
      (sd.fn.isDefined (.var .value sd.x)).eval (ρ.updateConst .value sd.x v) := by
  obtain ⟨_, rfl⟩ := encode_inv hinfo
  exact haxs _ (List.Mem.head _)

theorem encode_wfIn {sd : SpecDef} {bv : DefVal} {axs : List Axiom}
    (hlaw : sd.primitives.Lawful)
    (hinfo : Skolemize.encode sd = .ok (bv, axs))
    (hΔ : sd.Δ.wf) (hΓwf : sd.Γ.wfIn sd.Δ)
    (hheadFresh : sd.Fresh) :
    ∀ ax ∈ axs,
      ax.formula.wfIn
        (((sd.Δ.addBinaryRel sd.fn.rel).addUnary sd.fn.func).addUnaryRel sd.fn.defined) := by
  obtain ⟨henc, rfl⟩ := Skolemize.encode_inv hinfo
  set Δext : Signature :=
    ((sd.Δ.addBinaryRel sd.fn.rel).addUnary sd.fn.func).addUnaryRel sd.fn.defined with hΔext_def
  have hΔx_wf : (Δext.declVar ⟨sd.x, .value⟩).wf := by
    simpa [Δext, SpecFn.Sig.bothArg, SpecFn.Sig.both, SpecFn.Sig.func, SpecFn.Sig.rel] using
      hheadFresh.toSpecFnFresh.sigBothArg_wf (x := sd.x) hΔ
  have hbody_x : bv.wfIn (Δext.declVar ⟨sd.x, .value⟩) := by
    show bv.wfIn (SpecFn.Sig.bothArg sd.Δ sd.fn sd.x)
    exact encodeDefVal_wfIn_bothArg hlaw hΔ hΓwf.func hheadFresh henc
  have hfun_mem : sd.fn.func ∈ (Δext.declVar ⟨sd.x, .value⟩).unary :=
    Signature.mem_remove_unary.mpr
      ⟨List.Mem.head _, fun heq => hheadFresh.toSpecFnFresh.argNe.2.2.1 heq.symm⟩
  have hrel_mem : sd.fn.defined ∈ (Δext.declVar ⟨sd.x, .value⟩).unaryRel :=
    Signature.mem_remove_unaryRel.mpr
      ⟨List.Mem.head _, fun heq => hheadFresh.toSpecFnFresh.argNe.2.2.2 heq.symm⟩
  intro ax hmem
  exact SpecFn.Axioms.all_wfIn (Δ := Δext) hΔx_wf hbody_x hfun_mem hrel_mem ax hmem


/-- The axioms remain valid under any choice of binary relation
interpretation for `fn`. The body and axiom shapes only mention the
solver-facing func-form symbols, never `fn` as a binary predicate, so updating
`fn`'s binary interpretation is irrelevant. -/
private theorem SpecFn.Axioms.all_eval_updateBinaryRel {sd : SpecDef} {ρ : Env}
    (hlaw : sd.primitives.Lawful)
    {body : DefVal} (henc : encodeDefVal sd = .ok body)
    (hΓ : sd.Γ.Agreement ρ)
    (hΓwf : sd.Γ.wfIn sd.Δ)
    (hΔ : sd.Δ.wf) (hheadFresh : sd.Fresh)
    (R : ValRel) :
    ∀ ax ∈ SpecFn.Axioms.all sd.fn sd.x body,
      ax.formula.eval ((SpecFn.Semantics.env sd ρ body).updateBinaryRel
        .value .value sd.fn.relName R) := by
  intro ax hmem
  have hbase := SpecFn.Axioms.all_eval hlaw henc hΓ hΓwf hΔ hheadFresh ax hmem
  set Δsmall : Signature :=
    (sd.Δ.addUnary sd.fn.func).addUnaryRel sd.fn.defined with hΔsmall_def
  have hΔbig_wf : (Δsmall.declVar ⟨sd.x, .value⟩).wf := by
    show (SpecFn.Sig.funcArg sd.Δ sd.fn sd.x).wf
    exact hheadFresh.toSpecFnFresh.sigFuncArg_wf (x := sd.x) hΔ
  have hbody_wf : body.wfIn (Δsmall.declVar ⟨sd.x, .value⟩) := by
    show body.wfIn (SpecFn.Sig.funcArg sd.Δ sd.fn sd.x)
    exact encodeDefVal_wfIn_funcArg hlaw hΔ hΓwf.func hheadFresh henc
  have hxNeFun : sd.x ≠ sd.fn.funcName := fun heq =>
    hheadFresh.toSpecFnFresh.argFresh_sigFunc (heq ▸ Signature.mem_allNames_of_unary
      (Δ := Δsmall) (u := sd.fn.func) (List.Mem.head _))
  have hxNeDef : sd.x ≠ sd.fn.defName := fun heq =>
    hheadFresh.toSpecFnFresh.argFresh_sigFunc (heq ▸ Signature.mem_allNames_of_unaryRel
      (Δ := Δsmall) (u := sd.fn.defined) (List.Mem.head _))
  have hfun_mem : sd.fn.func ∈ (Δsmall.declVar ⟨sd.x, .value⟩).unary :=
    Signature.mem_remove_unary.mpr ⟨List.Mem.head _, fun heq => hxNeFun heq.symm⟩
  have hrel_mem : sd.fn.defined ∈ (Δsmall.declVar ⟨sd.x, .value⟩).unaryRel :=
    Signature.mem_remove_unaryRel.mpr ⟨List.Mem.head _, fun heq => hxNeDef heq.symm⟩
  have hax_wf : ax.formula.wfIn Δsmall :=
    SpecFn.Axioms.all_wfIn (Δ := Δsmall) hΔbig_wf hbody_wf hfun_mem hrel_mem ax hmem
  have hrelFresh_small : sd.fn.rel.name ∉ Δsmall.allNames :=
    Signature.not_mem_allNames_addUnaryRel
      (Signature.not_mem_allNames_addUnary hheadFresh.relFresh
        (show sd.fn.relName ≠ sd.fn.func.name from (SpecFn.funcName_ne_relName sd.fn).symm))
      (show sd.fn.relName ≠ sd.fn.defined.name from (SpecFn.defName_ne_relName sd.fn).symm)
  have hagree :
      Env.agreeOn Δsmall
        (SpecFn.Semantics.env sd ρ body)
        ((SpecFn.Semantics.env sd ρ body).updateBinaryRel
          .value .value sd.fn.relName R) :=
    Env.agreeOn_update_fresh_binaryRel
      (b := sd.fn.rel) hrelFresh_small
  exact (Formula.eval_env_agree hax_wf hagree).mp hbase

/-- Agreement of the three symbols at the newly declared relation. -/
theorem encode_agreement {sd : SpecDef} {ρ : Env} {bv : DefVal} {axs : List Axiom}
    (hlaw : sd.primitives.Lawful)
    (hinfo : Skolemize.encode sd = .ok (bv, axs))
    (hΓ : sd.Γ.Agreement ρ)
    (hΓwf : sd.Γ.wfIn sd.Δ)
    (hΔ : sd.Δ.wf) (hheadFresh : sd.Fresh) :
    Skolemize.Agreement sd ρ bv := by
  obtain ⟨henc, rfl⟩ := Skolemize.encode_inv hinfo
  exact SpecFn.Semantics.rel_agreement hlaw henc hΓ hΓwf hΔ hheadFresh

/-- Verifier-facing variant of `SpecFn.Axioms.all_eval_updateBinaryRel`: the SpecFn.Axioms.all emitted
by `Skolemize.encode` evaluate to true under any choice of binary-relation
interpretation for the freshly declared `fn` symbol. -/
theorem encode_eval_updateBinaryRel {sd : SpecDef} {ρ : Env} {bv : DefVal} {axs : List Axiom}
    (hlaw : sd.primitives.Lawful)
    (hinfo : Skolemize.encode sd = .ok (bv, axs))
    (hΓ : sd.Γ.Agreement ρ)
    (hΓwf : sd.Γ.wfIn sd.Δ)
    (hΔ : sd.Δ.wf) (hheadFresh : sd.Fresh)
    (R : ValRel) :
    ∀ ax ∈ axs,
      ax.formula.eval ((SpecFn.Semantics.env sd ρ bv).updateBinaryRel
        .value .value sd.fn.relName R) := by
  obtain ⟨henc, rfl⟩ := Skolemize.encode_inv hinfo
  exact SpecFn.Axioms.all_eval_updateBinaryRel hlaw henc hΓ hΓwf hΔ hheadFresh R

end Skolemize
end Verifier.RelationalEncoding
