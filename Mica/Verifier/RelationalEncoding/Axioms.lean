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
encoded body is defined on `x`.  Experimental — exposing this lets the SMT
backend propagate definedness from a parent call into its recursive subterms. -/
private def SpecFn.Axioms.definedElim (fn : SpecFn) (x : TinyML.Var) (body : DefVal) : Formula :=
  .all x .value
    (.implies (fn.isDefined (.var .value x)) body.defined)

/-- The solver-facing axioms emitted for a relation-marked function. All three
are quantified, so they are guarded (`.high`). -/
def SpecFn.Axioms.all (fn : SpecFn) (x : TinyML.Var) (body : DefVal) : List Axiom :=
  [⟨SpecFn.Axioms.definedIntro fn x body, .high⟩, ⟨SpecFn.Axioms.value fn x body, .high⟩,
   ⟨SpecFn.Axioms.definedElim fn x body, .high⟩]

private theorem SpecFn.Axioms.all_wfIn {Δ : Signature} {fn : SpecFn} {x : String} {body : DefVal}
    (hΔx : (Δ.declVar ⟨x, .value⟩).wf)
    (hbody : body.wfIn (Δ.declVar ⟨x, .value⟩))
    (hfun : fn.func ∈ (Δ.declVar ⟨x, .value⟩).unary)
    (hrel : fn.defined ∈ (Δ.declVar ⟨x, .value⟩).unaryRel) :
    ∀ ax ∈ SpecFn.Axioms.all fn x body, ax.formula.wfIn Δ := by
  intro ax hmem
  simp [SpecFn.Axioms.all] at hmem
  rcases hmem with rfl | rfl | rfl
  · simp only [SpecFn.Axioms.definedIntro, Formula.wfIn]
    exact ⟨by
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact SpecFn.isDefined_wfIn hrel hΔx
        (var_value_wfIn hΔx (Signature.var_mem_declVar Δ ⟨x, .value⟩)),
      ⟨hbody.2,
      SpecFn.isDefined_wfIn hrel hΔx
        (var_value_wfIn hΔx (Signature.var_mem_declVar Δ ⟨x, .value⟩))⟩⟩
  · simp only [SpecFn.Axioms.value, Formula.wfIn]
    have hx : (Term.var .value x).wfIn (Δ.declVar ⟨x, .value⟩) :=
      var_value_wfIn hΔx (Signature.var_mem_declVar Δ ⟨x, .value⟩)
    exact ⟨by
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact SpecFn.call_wfIn hfun hΔx hx,
      ⟨SpecFn.isDefined_wfIn hrel hΔx hx,
        SpecFn.call_wfIn hfun hΔx hx, hbody.1⟩⟩
  · simp only [SpecFn.Axioms.definedElim]
    exact ⟨(by
      intro p hp
      cases hp),
      ⟨SpecFn.isDefined_wfIn hrel hΔx
        (var_value_wfIn hΔx (Signature.var_mem_declVar Δ ⟨x, .value⟩)),
      hbody.2⟩⟩


/-- The relation the current recursive body denotes is exactly the graph of the
func-form definedness predicate and the chosen value function. -/
def Agreement (primitives : PrimEncodings)
    (Γ : FunCtx) (Δ : Signature) (ρ : Env)
    (f : TinyML.Var) (fn : SpecFn) (x res : TinyML.Var) (e : Typed.Expr)
    (body : DefVal) : Prop :=
  ∀ vin vout,
    SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e vin vout ↔
      SpecFn.Semantics.defined primitives Γ Δ ρ f fn x res e body vin ∧
        ValRel.toFunc (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e) vin = vout


/-- The definedness-introduction axiom is valid at the definedness least
fixpoint. This is the first solver-facing axiom and does not need the eventual
relation/graph equivalence. -/
private theorem SpecFn.Axioms.definedIntro_eval {primitives : PrimEncodings}
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (henc : encodeDefVal primitives Γ Δ f fn x res e = .ok body) :
    (SpecFn.Axioms.definedIntro fn x body).eval
      (SpecFn.Semantics.env primitives Γ Δ ρ f fn x res e body) := by
  simp only [SpecFn.Axioms.definedIntro, Formula.eval]
  intro vin hbody
  have hsem :
      SpecFn.Semantics.defined primitives Γ Δ ρ f fn x res e body vin := by
    exact (SpecFn.Semantics.defined_unfold (ρ := ρ) (x := x) (res := res) henc vin).mpr hbody
  exact (SpecFn.Semantics.env_isDefined (Γ := Γ) (Δ := Δ) (ρ := ρ)
    (f := f) (fn := fn) (x := x) (res := res) (e := e) (body := body) vin).mpr hsem

/-- The relation induced by the relational encoding agrees with the graph of the
func-form definedness fixpoint and the chosen value
function. This is a theorem of the two encodings, not an external invariant:
tail compatibility handles old function symbols, freshness prevents the new
symbols from clobbering them, and the paired-encoding completeness/soundness proof handles the
recursive body. -/
private theorem SpecFn.Semantics.rel_agreement {primitives : PrimEncodings}
    (hlaw : primitives.Lawful)
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (henc : encodeDefVal primitives Γ Δ f fn x res e = .ok body)
    (hΓ : Γ.Agreement ρ)
    (hΓwf : Γ.wfIn Δ)
    (hΔ : Δ.wf) (hheadFresh : EquationFresh Δ fn x res)
    (hρdet : FunCtx.Functional Γ ρ ρ) :
    Skolemize.Agreement primitives Γ Δ ρ f fn x res e body := by
  intro vin vout
  constructor
  · intro hrel
    have hsplit :=
      SpecFn.Semantics.rel_complete hlaw henc hΓ hΓwf hΔ hheadFresh hρdet
        vin vout hrel
    have hdefined : ValRel.toDef (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e) vin := ⟨vout, hrel⟩
    have hfun :
      ValRel.toFunc (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e) vin = vout :=
      SpecFn.Semantics.rel_functional hlaw henc hΔ hΓwf hheadFresh hρdet vin
        (ValRel.toFunc (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e) vin) vout
        (ValRel.toFunc_spec hdefined) hrel
    exact ⟨hsplit.1, hfun⟩
  · intro hgraph
    rcases hgraph with ⟨hdef, hfun⟩
    let vbody :=
      body.value.eval
        ((SpecFn.Semantics.env primitives Γ Δ ρ f fn x res e body).updateConst .value x vin)
    have hrelBody :
        SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e vin vbody :=
      SpecFn.Semantics.rel_sound hlaw henc hΓ hΓwf hΔ hheadFresh vin vbody
        hdef rfl
    have hdefined : ValRel.toDef (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e) vin := ⟨vbody, hrelBody⟩
    have hchosen :
        vbody = ValRel.toFunc (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e) vin :=
      SpecFn.Semantics.rel_functional hlaw henc hΔ hΓwf hheadFresh hρdet vin vbody
        (ValRel.toFunc (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e) vin)
        hrelBody (ValRel.toFunc_spec hdefined)
    exact SpecFn.Semantics.rel_sound hlaw henc hΓ hΓwf hΔ hheadFresh vin vout
      hdef (hchosen.trans hfun)

/-- The value axiom is valid at the canonical func-form interpretation extracted
from the relation. -/
private theorem SpecFn.Axioms.value_eval {primitives : PrimEncodings}
    (hlaw : primitives.Lawful)
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (henc : encodeDefVal primitives Γ Δ f fn x res e = .ok body)
    (hΓ : Γ.Agreement ρ)
    (hΓwf : Γ.wfIn Δ)
    (hΔ : Δ.wf) (hheadFresh : EquationFresh Δ fn x res)
    (hρdet : FunCtx.Functional Γ ρ ρ) :
    (SpecFn.Axioms.value fn x body).eval
      (SpecFn.Semantics.env primitives Γ Δ ρ f fn x res e body) := by
  simp only [SpecFn.Axioms.value, Formula.eval]
  intro vin hdef
  have hsem := (SpecFn.Semantics.env_isDefined (Γ := Γ) (Δ := Δ) (ρ := ρ)
    (f := f) (fn := fn) (x := x) (res := res) (e := e) (body := body) vin).mp hdef
  rw [SpecFn.Semantics.env_call (Γ := Γ) (Δ := Δ) (ρ := ρ)
    (f := f) (fn := fn) (x := x) (res := res) (e := e) (body := body) vin]
  have hgraph := SpecFn.Semantics.rel_agreement hlaw henc hΓ hΓwf hΔ hheadFresh hρdet
  have hrel :
      SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e vin
        (ValRel.toFunc (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e) vin) :=
    (hgraph vin (ValRel.toFunc (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e) vin)).mpr ⟨hsem, rfl⟩
  exact (SpecFn.Semantics.rel_complete hlaw henc hΓ hΓwf hΔ hheadFresh hρdet
    vin (ValRel.toFunc (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e) vin) hrel).2.symm

/-- Semantic validity of the converse definedness axiom: under the least
fixpoint of `SpecFn.Semantics.defined`, the `SpecFn.Semantics.defined`/`Skolemize.eval` unfolding goes both ways, so
`isDefined fn x` implies `body.defined` on `x`. -/
private theorem SpecFn.Axioms.definedElim_eval {primitives : PrimEncodings}
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (henc : encodeDefVal primitives Γ Δ f fn x res e = .ok body) :
    (SpecFn.Axioms.definedElim fn x body).eval
      (SpecFn.Semantics.env primitives Γ Δ ρ f fn x res e body) := by
  simp only [SpecFn.Axioms.definedElim, Formula.all, Formula.eval]
  intro vin hdef
  have hsem : SpecFn.Semantics.defined primitives Γ Δ ρ f fn x res e body vin :=
    (SpecFn.Semantics.env_isDefined (Γ := Γ) (Δ := Δ) (ρ := ρ)
      (f := f) (fn := fn) (x := x) (res := res) (e := e) (body := body) vin).mp hdef
  exact (SpecFn.Semantics.defined_unfold (ρ := ρ) (x := x) (res := res) henc vin).mp hsem

/-- Validity of all three axioms at the canonical func-form
interpretation. -/
private theorem SpecFn.Axioms.all_eval {primitives : PrimEncodings}
    (hlaw : primitives.Lawful)
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (henc : encodeDefVal primitives Γ Δ f fn x res e = .ok body)
    (hΓ : Γ.Agreement ρ)
    (hΓwf : Γ.wfIn Δ)
    (hΔ : Δ.wf) (hheadFresh : EquationFresh Δ fn x res)
    (hρdet : FunCtx.Functional Γ ρ ρ) :
    ∀ ax ∈ SpecFn.Axioms.all fn x body,
      ax.formula.eval (SpecFn.Semantics.env primitives Γ Δ ρ f fn x res e body) := by
  intro ax hmem
  simp [SpecFn.Axioms.all] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact SpecFn.Axioms.definedIntro_eval henc
  · exact SpecFn.Axioms.value_eval hlaw henc hΓ hΓwf hΔ hheadFresh hρdet
  · exact SpecFn.Axioms.definedElim_eval henc

/-! ## The verifier-facing entry point

`encode` is the top-level entry point for the verifier: given a relation-marked
function and its body, it returns the data needed to declare solver symbols
and assume axioms (the binary relation symbol, the value function, the
definedness predicate, a fresh pinned result variable, the encoded body, and
the guarded solver-facing axioms over the func-form symbols).

The lemmas below lift the corresponding `SpecFn.Axioms.*` results to the `encode`
level. -/

/-- Verifier-facing entry point for the func-form (definedness/value) encoding.
The declared symbols (`fn.rel`, `fn.func`, `fn.defined`) are determined by `fn`,
so this returns only the data the encoder computes: the canonical pinned-result
variable, the encoded body, and the list of solver-emitted axioms. -/
def encode (primitives : PrimEncodings)
    (Γ : FunCtx) (Δ : Signature) (f : TinyML.Var) (fn : SpecFn) (x : String) (e : Typed.Expr) :
    Except String (String × DefVal × List Axiom) := do
  let res := Fresh.freshName (Δ.allNames ++ fn.names ++ [x]) "r"
  let bv ← encodeDefVal primitives Γ Δ f fn x res e
  pure (res, bv, SpecFn.Axioms.all fn x bv)

private theorem encode_equationFresh
    {Δ : Signature} {x fn : SpecFn} (hf : SpecFnFresh Δ fn x) :
    EquationFresh Δ fn x (Fresh.freshName (Δ.allNames ++ fn.names ++ [x]) "r") :=
  { toSpecFnFresh := hf
    resFresh := Fresh.freshName_not_in_avoid _ _ }

theorem encode_wfIn {primitives : PrimEncodings}
    (hlaw : primitives.Lawful)
    {Γ : FunCtx} {Δ : Signature} {f : TinyML.Var} {fn : SpecFn} {x : String} {e : Typed.Expr}
    {res : String} {bv : DefVal} {axs : List Axiom}
    (hinfo : Skolemize.encode primitives Γ Δ f fn x e = .ok (res, bv, axs))
    (hΔ : Δ.wf) (hΓwf : Γ.wfIn Δ)
    (hf : SpecFnFresh Δ fn x) :
    ∀ ax ∈ axs,
      ax.formula.wfIn (((Δ.addBinaryRel fn.rel).addUnary fn.func).addUnaryRel fn.defined) := by
  unfold Skolemize.encode at hinfo
  simp only [bind, Except.bind] at hinfo
  split at hinfo
  · cases hinfo
  rename_i bv' henc
  cases hinfo
  have hheadFresh := Skolemize.encode_equationFresh (Δ := Δ) (x := x) (fn := fn) hf
  set Δext : Signature :=
    ((Δ.addBinaryRel fn.rel).addUnary (fn.func)).addUnaryRel
      (fn.defined) with hΔext_def
  have hΔx_wf : (Δext.declVar ⟨x, .value⟩).wf := by
    simpa [Δext, SpecFn.Sig.bothArg, SpecFn.Sig.both, SpecFn.Sig.func, SpecFn.Sig.rel] using
      hheadFresh.toSpecFnFresh.sigBothArg_wf (x := x) hΔ
  have hbody_x : bv.wfIn (Δext.declVar ⟨x, .value⟩) := by
    show bv.wfIn (SpecFn.Sig.bothArg Δ fn x)
    exact encodeDefVal_wfIn_bothArg hlaw hΔ hΓwf.func hheadFresh henc
  have hfun_mem : fn.func ∈ (Δext.declVar ⟨x, .value⟩).unary :=
    Signature.mem_remove_unary.mpr ⟨List.Mem.head _, fun heq => hf.argNe.2.2.1 heq.symm⟩
  have hrel_mem : fn.defined ∈ (Δext.declVar ⟨x, .value⟩).unaryRel :=
    Signature.mem_remove_unaryRel.mpr ⟨List.Mem.head _, fun heq => hf.argNe.2.2.2 heq.symm⟩
  intro ax hmem
  exact SpecFn.Axioms.all_wfIn (Δ := Δext) hΔx_wf hbody_x hfun_mem hrel_mem ax hmem


/-- The axioms remain valid under any choice of binary relation
interpretation for `fn`. The body and axiom shapes only mention the
solver-facing func-form symbols, never `fn` as a binary predicate, so updating
`fn`'s binary interpretation is irrelevant. -/
private theorem SpecFn.Axioms.all_eval_updateBinaryRel {primitives : PrimEncodings}
    (hlaw : primitives.Lawful)
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (henc : encodeDefVal primitives Γ Δ f fn x res e = .ok body)
    (hΓ : Γ.Agreement ρ)
    (hΓwf : Γ.wfIn Δ)
    (hΔ : Δ.wf) (hheadFresh : EquationFresh Δ fn x res)
    (hρdet : FunCtx.Functional Γ ρ ρ)
    (R : ValRel) :
    ∀ ax ∈ SpecFn.Axioms.all fn x body,
      ax.formula.eval ((SpecFn.Semantics.env primitives Γ Δ ρ f fn x res e body).updateBinaryRel
        .value .value fn.relName R) := by
  intro ax hmem
  have hbase := SpecFn.Axioms.all_eval hlaw henc hΓ hΓwf hΔ hheadFresh hρdet ax hmem
  set Δsmall : Signature :=
    (Δ.addUnary (fn.func)).addUnaryRel (fn.defined) with hΔsmall_def
  have hΔbig_wf : (Δsmall.declVar ⟨x, .value⟩).wf := by
    show (SpecFn.Sig.funcArg Δ fn x).wf
    exact hheadFresh.toSpecFnFresh.sigFuncArg_wf (x := x) hΔ
  have hbody_wf : body.wfIn (Δsmall.declVar ⟨x, .value⟩) := by
    show body.wfIn (SpecFn.Sig.funcArg Δ fn x)
    exact encodeDefVal_wfIn_funcArg hlaw hΔ hΓwf.func hheadFresh henc
  have hxNeFun : x ≠ fn.funcName := fun heq =>
    hheadFresh.toSpecFnFresh.argFresh_sigFunc (heq ▸ Signature.mem_allNames_of_unary
      (Δ := Δsmall) (u := fn.func) (List.Mem.head _))
  have hxNeDef : x ≠ fn.defName := fun heq =>
    hheadFresh.toSpecFnFresh.argFresh_sigFunc (heq ▸ Signature.mem_allNames_of_unaryRel
      (Δ := Δsmall) (u := fn.defined) (List.Mem.head _))
  have hfun_mem : fn.func ∈ (Δsmall.declVar ⟨x, .value⟩).unary :=
    Signature.mem_remove_unary.mpr ⟨List.Mem.head _, fun heq => hxNeFun heq.symm⟩
  have hrel_mem : fn.defined ∈ (Δsmall.declVar ⟨x, .value⟩).unaryRel :=
    Signature.mem_remove_unaryRel.mpr ⟨List.Mem.head _, fun heq => hxNeDef heq.symm⟩
  have hax_wf : ax.formula.wfIn Δsmall :=
    SpecFn.Axioms.all_wfIn (Δ := Δsmall) hΔbig_wf hbody_wf hfun_mem hrel_mem ax hmem
  have hrelFresh_small : fn.rel.name ∉ Δsmall.allNames :=
    Signature.not_mem_allNames_addUnaryRel
      (Signature.not_mem_allNames_addUnary hheadFresh.relFresh
        (show fn.relName ≠ (fn.func).name from (SpecFn.funcName_ne_relName fn).symm))
      (show fn.relName ≠ (fn.defined).name from (SpecFn.defName_ne_relName fn).symm)
  have hagree :
      Env.agreeOn Δsmall
        (SpecFn.Semantics.env primitives Γ Δ ρ f fn x res e body)
        ((SpecFn.Semantics.env primitives Γ Δ ρ f fn x res e body).updateBinaryRel
          .value .value fn.relName R) :=
    Env.agreeOn_update_fresh_binaryRel
      (b := fn.rel) hrelFresh_small
  exact (Formula.eval_env_agree hax_wf hagree).mp hbase

/-- Verifier-facing combined functionality: `SpecFn.Semantics.rel` is single-valued. -/
private theorem encode_functional {primitives : PrimEncodings}
    (hlaw : primitives.Lawful)
    {Γ : FunCtx} {Δ : Signature}
    {f fn x : String} {e : Typed.Expr}
    {res : String} {bv : DefVal} {axs : List Axiom}
    (hinfo : Skolemize.encode primitives Γ Δ f fn x e = .ok (res, bv, axs))
    (hΓwf : Γ.wfIn Δ)
    (hΔ : Δ.wf) (hf : SpecFnFresh Δ fn x)
    (ρ : Env) (hρdet : FunCtx.Functional Γ ρ ρ)
    (vin : Srt.value.denote) (y₁ y₂ : Srt.value.denote)
    (h₁ : SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e vin y₁)
    (h₂ : SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e vin y₂) :
    y₁ = y₂ := by
  unfold Skolemize.encode at hinfo
  simp only [bind, Except.bind] at hinfo
  split at hinfo
  · cases hinfo
  rename_i bv' henc
  cases hinfo
  have hheadFresh := Skolemize.encode_equationFresh (Δ := Δ) (x := x) (fn := fn) hf
  exact SpecFn.Semantics.rel_functional hlaw henc hΔ hΓwf hheadFresh hρdet
    vin y₁ y₂ h₁ h₂

/-- Agreement of the three symbols at the newly declared relation. -/
theorem encode_agreement {primitives : PrimEncodings}
    (hlaw : primitives.Lawful)
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f fn x : String} {e : Typed.Expr}
    {res : String} {bv : DefVal} {axs : List Axiom}
    (hinfo : Skolemize.encode primitives Γ Δ f fn x e = .ok (res, bv, axs))
    (hΓ : Γ.Agreement ρ)
    (hΓwf : Γ.wfIn Δ)
    (hΔ : Δ.wf) (hf : SpecFnFresh Δ fn x)
    (hρdet : FunCtx.Functional Γ ρ ρ)
    (vin vout : Srt.value.denote) :
    SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e vin vout ↔
      SpecFn.Semantics.defined primitives Γ Δ ρ f fn x res e bv vin ∧
        ValRel.toFunc (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e) vin = vout := by
  unfold Skolemize.encode at hinfo
  simp only [bind, Except.bind] at hinfo
  split at hinfo
  · cases hinfo
  rename_i bv' henc
  cases hinfo
  have hheadFresh := Skolemize.encode_equationFresh (Δ := Δ) (x := x) (fn := fn) hf
  exact SpecFn.Semantics.rel_agreement hlaw henc hΓ hΓwf hΔ hheadFresh hρdet vin vout

/-- Verifier-facing variant of `SpecFn.Axioms.all_eval_updateBinaryRel`: the SpecFn.Axioms.all emitted
by `Skolemize.encode` evaluate to true under any choice of binary-relation
interpretation for the freshly declared `fn` symbol. -/
theorem encode_eval_updateBinaryRel {primitives : PrimEncodings}
    (hlaw : primitives.Lawful)
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x : String} {e : Typed.Expr}
    {res : String} {bv : DefVal} {axs : List Axiom}
    (hinfo : Skolemize.encode primitives Γ Δ f fn x e = .ok (res, bv, axs))
    (hΓ : Γ.Agreement ρ)
    (hΓwf : Γ.wfIn Δ)
    (hΔ : Δ.wf) (hf : SpecFnFresh Δ fn x)
    (hρdet : FunCtx.Functional Γ ρ ρ)
    (R : ValRel) :
    ∀ ax ∈ axs,
      ax.formula.eval ((SpecFn.Semantics.env primitives Γ Δ ρ f fn x res e bv).updateBinaryRel
        .value .value fn.relName R) := by
  unfold Skolemize.encode at hinfo
  simp only [bind, Except.bind] at hinfo
  split at hinfo
  · cases hinfo
  rename_i bv' henc
  cases hinfo
  have hheadFresh := Skolemize.encode_equationFresh (Δ := Δ) (x := x) (fn := fn) hf
  exact SpecFn.Axioms.all_eval_updateBinaryRel hlaw henc hΓ hΓwf hΔ hheadFresh hρdet R

end Skolemize
end Verifier.RelationalEncoding
