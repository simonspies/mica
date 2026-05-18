-- SUMMARY: Solver-facing axioms and validity theorems for skolemized relational encoding.
import Mica.Verifier.RelationalEncoding.SkolemizeCompleteness


/-!
# Split Encoding Axioms

For each fn-œmarked recursive function, Skolemization exposes the
relational graph through two solver-facing symbols:

* `f_def(x)` says the function is defined on input `x`;
* `f_val(x)` is the value returned at `x` when it is defined.

If `body_def(x)` and `body_val(x)` are the definedness and value expressions
computed by the split body encoding, this file emits and proves valid three
axioms:

1. `body_def(x) -> f_def(x)` (`definedIntroAxiom`);
2. `f_def(x) -> f_val(x) = body_val(x)` (`valueAxiom`);
3. `f_def(x) -> body_def(x)` (`definedElimAxiom`).

Together, the two definedness implications make `f_def(x)` equivalent to the
body being defined, and the value axiom pins `f_val(x)` to the encoded body
value on that domain.

For a fibonacci-style definition

```text
fib n = if n <= 1 then n else fib (n - 1) + fib (n - 2)
```

the split body has a definedness condition like

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
def definedIntroAxiom (rel x : TinyML.Var) (body : DefVal) : Formula :=
  .forall_ x .value
    (.implies body.defined (SpecFn.isDefined rel (.var .value x)))

/-- If the function is defined on input `x`, its solver-facing value equals the
encoded body value. -/
def valueAxiom (rel x : TinyML.Var) (body : DefVal) : Formula :=
  .forall_ x .value
    (.implies
      (SpecFn.isDefined rel (.var .value x))
      (.eq .value (SpecFn.call rel (.var .value x)) body.value))

/-- Converse of `definedIntroAxiom`: if the function is defined on `x`, then the
encoded body is defined on `x`.  Experimental — exposing this lets the SMT
backend propagate definedness from a parent call into its recursive subterms. -/
def definedElimAxiom (rel x : TinyML.Var) (body : DefVal) : Formula :=
  .forall_ x .value
    (.implies (SpecFn.isDefined rel (.var .value x)) body.defined)

/-- The solver-facing axioms emitted for a relation-marked function. -/
def axioms (rel x : TinyML.Var) (body : DefVal) : List Formula :=
  [definedIntroAxiom rel x body, valueAxiom rel x body,
   definedElimAxiom rel x body]

theorem axioms_wfIn {Δ : Signature} {rel x : String} {body : DefVal}
    (hΔx : (Δ.declVar ⟨x, .value⟩).wf)
    (hbody : body.wfIn (Δ.declVar ⟨x, .value⟩))
    (hfun : SpecFn.func rel ∈ (Δ.declVar ⟨x, .value⟩).unary)
    (hrel : SpecFn.defined rel ∈ (Δ.declVar ⟨x, .value⟩).unaryRel) :
    ∀ ax ∈ axioms rel x body, ax.wfIn Δ := by
  intro ax hmem
  simp [axioms] at hmem
  rcases hmem with rfl | rfl | rfl
  · simp only [definedIntroAxiom, Formula.wfIn]
    exact ⟨hbody.2,
      SpecFn.isDefined_wfIn hrel hΔx
        (var_value_wfIn hΔx (Signature.var_mem_declVar Δ ⟨x, .value⟩))⟩
  · simp only [valueAxiom, Formula.wfIn]
    have hx : (Term.var .value x).wfIn (Δ.declVar ⟨x, .value⟩) :=
      var_value_wfIn hΔx (Signature.var_mem_declVar Δ ⟨x, .value⟩)
    exact ⟨SpecFn.isDefined_wfIn hrel hΔx hx,
      SpecFn.call_wfIn hfun hΔx hx, hbody.1⟩
  · simp only [definedElimAxiom, Formula.wfIn]
    exact ⟨SpecFn.isDefined_wfIn hrel hΔx
        (var_value_wfIn hΔx (Signature.var_mem_declVar Δ ⟨x, .value⟩)),
      hbody.2⟩


/-- The semantic relation for the current recursive body is exactly the graph
of the split definedness predicate and the epsilon-selected value function. -/
def GraphCompatible
    (Γ : FunCtx) (Δ : Signature) (ρ : Env)
    (f : TinyML.Var) (rel : String) (x res : TinyML.Var) (e : Typed.Expr)
    (body : DefVal) : Prop :=
  ∀ vin vout,
    semrel Γ Δ ρ f rel x res e vin vout ↔
      semdef Γ Δ ρ f rel x res e body vin ∧
        semFunc (semrel Γ Δ ρ f rel x res e) vin = vout


/-- The definedness-introduction axiom is valid under the semantic definedness
least fixpoint. This is the first solver-facing axiom and does not require the
eventual relation/graph equivalence. -/
theorem definedIntroAxiom_eval
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {rel : String} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (henc : encodeBody Γ Δ f rel x res e = .ok body) :
    (definedIntroAxiom rel x body).eval
      (defInterpEnv Γ Δ ρ f rel x res e body) := by
  simp only [definedIntroAxiom, Formula.eval]
  intro vin hbody
  have hsem :
      semdef Γ Δ ρ f rel x res e body vin := by
    exact (semdef_unfold_of_encode (ρ := ρ) (x := x) (res := res) henc vin).mpr hbody
  exact (definedCall_eval_defInterpEnv (Γ := Γ) (Δ := Δ) (ρ := ρ)
    (f := f) (fn := rel) (x := x) (res := res) (e := e) (body := body) vin).mpr hsem

/-- The semantic relation induced by the relational encoding agrees with the
graph induced by the split definedness fixpoint and epsilon-selected value
function. This is a theorem of the two encodings, not an external invariant:
tail compatibility handles old function symbols, freshness prevents the new
symbols from clobbering them, and the paired-encoding completeness/soundness proof handles the
recursive body. -/
theorem semrel_compatible
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {rel : String} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (henc : encodeBody Γ Δ f rel x res e = .ok body)
    (hΓ : Γ.splitCompatible ρ)
    (hΓrel : Γ.wfIn Δ) (hΓdef : Γ.defWfIn Δ)
    (hΔ : Δ.wf) (hheadFresh : HeadFresh Δ rel x res)
    (hρdet : Relation.BinaryRelDet Γ ρ ρ) :
    GraphCompatible Γ Δ ρ f rel x res e body := by
  intro vin vout
  constructor
  · intro hrel
    have hsplit :=
      semrel_complete henc hΓ hΓrel hΓdef hΔ hheadFresh hρdet
        vin vout hrel
    have hdefined : semDefined (semrel Γ Δ ρ f rel x res e) vin := ⟨vout, hrel⟩
    have hfun :
      semFunc (semrel Γ Δ ρ f rel x res e) vin = vout :=
      relation_semrel_functional_of_encodeBody henc hΔ hΓrel hΓdef hheadFresh hρdet vin
        (semFunc (semrel Γ Δ ρ f rel x res e) vin) vout
        (semFunc_spec hdefined) hrel
    exact ⟨hsplit.1, hfun⟩
  · intro hgraph
    rcases hgraph with ⟨hdef, hfun⟩
    let vbody :=
      body.value.eval
        ((defInterpEnv Γ Δ ρ f rel x res e body).updateConst .value x vin)
    have hrelBody :
        semrel Γ Δ ρ f rel x res e vin vbody :=
      semrel_sound henc hΓ hΓrel hΓdef hΔ hheadFresh vin vbody
        hdef rfl
    have hdefined : semDefined (semrel Γ Δ ρ f rel x res e) vin := ⟨vbody, hrelBody⟩
    have hchosen :
        vbody = semFunc (semrel Γ Δ ρ f rel x res e) vin :=
      relation_semrel_functional_of_encodeBody henc hΔ hΓrel hΓdef hheadFresh hρdet vin vbody
        (semFunc (semrel Γ Δ ρ f rel x res e) vin)
        hrelBody (semFunc_spec hdefined)
    exact semrel_sound henc hΓ hΓrel hΓdef hΔ hheadFresh vin vout
      hdef (hchosen.trans hfun)

/-- The value axiom is valid under the canonical split interpretation extracted
from the relational semantics. -/
theorem valueAxiom_eval
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {rel : String} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (henc : encodeBody Γ Δ f rel x res e = .ok body)
    (hΓ : Γ.splitCompatible ρ)
    (hΓrel : Γ.wfIn Δ) (hΓdef : Γ.defWfIn Δ)
    (hΔ : Δ.wf) (hheadFresh : HeadFresh Δ rel x res)
    (hρdet : Relation.BinaryRelDet Γ ρ ρ) :
    (valueAxiom rel x body).eval
      (defInterpEnv Γ Δ ρ f rel x res e body) := by
  simp only [valueAxiom, Formula.eval]
  intro vin hdef
  have hsem := (definedCall_eval_defInterpEnv (Γ := Γ) (Δ := Δ) (ρ := ρ)
    (f := f) (fn := rel) (x := x) (res := res) (e := e) (body := body) vin).mp hdef
  rw [valueCall_eval_defInterpEnv (Γ := Γ) (Δ := Δ) (ρ := ρ)
    (f := f) (fn := rel) (x := x) (res := res) (e := e) (body := body) vin]
  have hgraph := semrel_compatible henc hΓ hΓrel hΓdef hΔ hheadFresh hρdet
  have hrel :
      semrel Γ Δ ρ f rel x res e vin
        (semFunc (semrel Γ Δ ρ f rel x res e) vin) :=
    (hgraph vin (semFunc (semrel Γ Δ ρ f rel x res e) vin)).mpr ⟨hsem, rfl⟩
  exact (semrel_complete henc hΓ hΓrel hΓdef hΔ hheadFresh hρdet
    vin (semFunc (semrel Γ Δ ρ f rel x res e) vin) hrel).2.symm

/-- Semantic validity of the converse definedness axiom: under the least
fixpoint of `semdef`, the `semdef`/`defBody` unfolding goes both ways, so
`isDefined rel x` implies `body.defined` on `x`. -/
theorem definedElimAxiom_eval
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {rel : String} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (henc : encodeBody Γ Δ f rel x res e = .ok body) :
    (definedElimAxiom rel x body).eval
      (defInterpEnv Γ Δ ρ f rel x res e body) := by
  simp only [definedElimAxiom, Formula.eval]
  intro vin hdef
  have hsem : semdef Γ Δ ρ f rel x res e body vin :=
    (definedCall_eval_defInterpEnv (Γ := Γ) (Δ := Δ) (ρ := ρ)
      (f := f) (fn := rel) (x := x) (res := res) (e := e) (body := body) vin).mp hdef
  exact (semdef_unfold_of_encode (ρ := ρ) (x := x) (res := res) henc vin).mp hsem

/-- Semantic validity of the split axioms under the canonical split
interpretation. -/
theorem axioms_eval
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {rel : String} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (henc : encodeBody Γ Δ f rel x res e = .ok body)
    (hΓ : Γ.splitCompatible ρ)
    (hΓrel : Γ.wfIn Δ) (hΓdef : Γ.defWfIn Δ)
    (hΔ : Δ.wf) (hheadFresh : HeadFresh Δ rel x res)
    (hρdet : Relation.BinaryRelDet Γ ρ ρ) :
    ∀ ax ∈ axioms rel x body,
      ax.eval (defInterpEnv Γ Δ ρ f rel x res e body) := by
  intro ax hmem
  simp [axioms] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact definedIntroAxiom_eval henc
  · exact valueAxiom_eval henc hΓ hΓrel hΓdef hΔ hheadFresh hρdet
  · exact definedElimAxiom_eval henc

/-! ## Verifier-facing bundle

`bundle` is the top-level entry point for the verifier: given a relation-marked
function and its body, it returns the data needed to declare solver symbols
and assume axioms (the binary relation symbol, the value function, the
definedness predicate, a fresh pinned result variable, the encoded body, and
the list of axioms). Stage 2 emits two unary axioms (over the value and
definedness symbols) instead of stage 1's single binary defining axiom.

The lemmas below lift the corresponding `axioms_*` results to the `bundle`
level. -/

/-- Bundle of independent freshness premises sufficient to derive
`HeadFresh` once a fresh result variable is chosen. The verifier discharges
these per step. -/
structure InfoFresh (Δ : Signature) (rel arg : String) : Prop where
  relFresh : rel ∉ Δ.allNames
  funFresh : SpecFn.funcName rel ∉ Δ.allNames
  defFresh : SpecFn.defName rel ∉ Δ.allNames
  argFresh : arg ∉ Δ.allNames
  argNeRel : arg ≠ rel
  argNeFun : arg ≠ SpecFn.funcName rel
  argNeDef : arg ≠ SpecFn.defName rel

theorem freshName_avoid_props
    (Δ : Signature) (arg rel : String) :
    let res := Fresh.freshName
      (Δ.allNames ++ [arg, rel, SpecFn.funcName rel, SpecFn.defName rel]) "r"
    res ∉ Δ.allNames ∧ res ≠ arg ∧ res ≠ rel ∧
      res ≠ SpecFn.funcName rel ∧ res ≠ SpecFn.defName rel := by
  have hres := Fresh.freshName_not_in_avoid
    (Δ.allNames ++ [arg, rel, SpecFn.funcName rel, SpecFn.defName rel]) "r"
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; exact hres (List.mem_append_left _ h)
  · intro h; apply hres; rw [h]; simp
  · intro h; apply hres; rw [h]; simp
  · intro h; apply hres; rw [h]; simp
  · intro h; apply hres; rw [h]; simp

/-- Derive `HeadFresh` from independent freshness hypotheses on each of the
solver-facing names. -/
theorem headFresh_of_fresh
    {Δ : Signature} {rel x res : String}
    (hf : InfoFresh Δ rel x)
    (hresΔ : res ∉ Δ.allNames)
    (hresRel : res ≠ rel) (hresFun : res ≠ SpecFn.funcName rel)
    (hresDef : res ≠ SpecFn.defName rel) (hresx : res ≠ x) :
    HeadFresh Δ rel x res := by
  refine
    { relFresh := hf.relFresh
      funFresh := ?_
      defFresh := ?_
      argFresh := ?_
      resFresh := ?_ }
  · exact Signature.not_mem_allNames_addBinaryRel hf.funFresh (SpecFn.funcName_ne_fn rel)
  · exact Signature.not_mem_allNames_addUnary
      (Signature.not_mem_allNames_addBinaryRel hf.defFresh (SpecFn.defName_ne_fn rel))
      (SpecFn.defName_ne_funcName rel)
  · exact Signature.not_mem_allNames_addUnaryRel
      (Signature.not_mem_allNames_addUnary
        (Signature.not_mem_allNames_addBinaryRel hf.argFresh hf.argNeRel)
        hf.argNeFun)
      hf.argNeDef
  · exact Signature.not_mem_allNames_declVar
      (Signature.not_mem_allNames_addUnaryRel
        (Signature.not_mem_allNames_addUnary
          (Signature.not_mem_allNames_addBinaryRel hresΔ hresRel)
          hresFun)
        hresDef)
      hresx

/-- Verifier-facing helper bundle for the split (definedness/value) encoding.
Returns the binary relation symbol (declared but unconstrained at the SMT
level), the solver-facing value function, the definedness predicate, the
canonical pinned-result variable, the encoded body, and the list of
solver-emitted axioms. -/
def bundle
    (Γ : FunCtx) (Δ : Signature) (name rel arg : String) (body : Typed.Expr) :
    Except String
      (FOL.BinaryRel × FOL.Unary × FOL.UnaryRel × String × DefVal × List Formula) := do
  let res := Fresh.freshName
    (Δ.allNames ++ [arg, rel, SpecFn.funcName rel, SpecFn.defName rel]) "r"
  let bv ← encodeBody Γ Δ name rel arg res body
  pure (⟨rel, .value, .value⟩, SpecFn.func rel, SpecFn.defined rel, res, bv,
        axioms rel arg bv)

theorem bundle_headFresh
    {Δ : Signature} {arg rel : String}
    (hf : InfoFresh Δ rel arg) :
    HeadFresh Δ rel arg
      (Fresh.freshName
        (Δ.allNames ++ [arg, rel, SpecFn.funcName rel, SpecFn.defName rel]) "r") := by
  obtain ⟨hresΔ, hresArg, hresRel, hresFun, hresDef⟩ :=
    freshName_avoid_props Δ arg rel
  exact headFresh_of_fresh hf hresΔ hresRel hresFun hresDef hresArg

theorem bundle_wfIn
    {Γ : FunCtx} {Δ : Signature} {name rel arg : String} {body : Typed.Expr}
    {sym : FOL.BinaryRel} {fn : FOL.Unary} {drel : FOL.UnaryRel}
    {res : String} {bv : DefVal} {axs : List Formula}
    (hinfo : bundle Γ Δ name rel arg body
              = .ok (sym, fn, drel, res, bv, axs))
    (hΔ : Δ.wf) (hΓdef : Γ.defWfIn Δ)
    (hf : InfoFresh Δ rel arg) :
    sym = ⟨rel, .value, .value⟩ ∧ fn = SpecFn.func rel ∧ drel = SpecFn.defined rel ∧
      ∀ ax ∈ axs,
        ax.wfIn (((Δ.addBinaryRel sym).addUnary fn).addUnaryRel drel) := by
  unfold bundle at hinfo
  simp only [bind, Except.bind] at hinfo
  split at hinfo
  · cases hinfo
  rename_i bv' henc
  cases hinfo
  refine ⟨rfl, rfl, rfl, ?_⟩
  have hheadFresh := bundle_headFresh (Δ := Δ) (arg := arg) (rel := rel) hf
  set Δext : Signature :=
    ((Δ.addBinaryRel ⟨rel, .value, .value⟩).addUnary (SpecFn.func rel)).addUnaryRel
      (SpecFn.defined rel) with hΔext_def
  have hΔx_wf : (Δext.declVar ⟨arg, .value⟩).wf := by
    simpa [Δext, bodySig] using bodySig_wf_of_headFresh hΔ hheadFresh
  have hbody_x : bv.wfIn (Δext.declVar ⟨arg, .value⟩) := by
    show bv.wfIn (bodySig Δ rel arg)
    exact encode_wfIn (Γ := Relation.ctx Γ name rel)
      (Δ := bodySig Δ rel arg) body
      (bodySig_wf_of_headFresh hΔ hheadFresh)
      (ctx_defWfIn_bodySig_of_headFresh hΓdef hheadFresh)
      (encodeBody_def_bodySig henc)
  have hfun_mem : SpecFn.func rel ∈ (Δext.declVar ⟨arg, .value⟩).unary :=
    Signature.mem_remove_unary.mpr ⟨List.Mem.head _, fun heq => hf.argNeFun heq.symm⟩
  have hrel_mem : SpecFn.defined rel ∈ (Δext.declVar ⟨arg, .value⟩).unaryRel :=
    Signature.mem_remove_unaryRel.mpr ⟨List.Mem.head _, fun heq => hf.argNeDef heq.symm⟩
  intro ax hmem
  exact axioms_wfIn (Δ := Δext) hΔx_wf hbody_x hfun_mem hrel_mem ax hmem


/-- The split axioms remain valid under any choice of binary relation
interpretation for `rel`. The body and axiom shapes only mention the
solver-facing split symbols, never `rel` as a binary predicate, so updating
`rel`'s binary interpretation is irrelevant. -/
theorem axioms_eval_updateBinaryRel
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {rel : String} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (henc : encodeBody Γ Δ f rel x res e = .ok body)
    (hΓ : Γ.splitCompatible ρ)
    (hΓrel : Γ.wfIn Δ) (hΓdef : Γ.defWfIn Δ)
    (hΔ : Δ.wf) (hheadFresh : HeadFresh Δ rel x res)
    (hρdet : Relation.BinaryRelDet Γ ρ ρ)
    (R : ValRel) :
    ∀ ax ∈ axioms rel x body,
      ax.eval ((defInterpEnv Γ Δ ρ f rel x res e body).updateBinaryRel
        .value .value rel R) := by
  intro ax hmem
  have hbase := axioms_eval henc hΓ hΓrel hΓdef hΔ hheadFresh hρdet ax hmem
  set Δsmall : Signature :=
    (Δ.addUnary (SpecFn.func rel)).addUnaryRel (SpecFn.defined rel) with hΔsmall_def
  have hΔbig_wf : (Δsmall.declVar ⟨x, .value⟩).wf := by
    show (defvalBodySig Δ rel x).wf
    exact defvalBodySig_wf_of_headFresh hΔ hheadFresh
  have hbody_wf : body.wfIn (Δsmall.declVar ⟨x, .value⟩) := by
    show body.wfIn (defvalBodySig Δ rel x)
    exact encodeBody_wfIn_defvalBodySig hΔ hΓdef hheadFresh henc
  have hxNeFun : x ≠ SpecFn.funcName rel := fun heq =>
    var_fresh_splitBase_of_headFresh hheadFresh (heq ▸ Signature.mem_allNames_of_unary
      (Δ := Δsmall) (u := SpecFn.func rel) (List.Mem.head _))
  have hxNeDef : x ≠ SpecFn.defName rel := fun heq =>
    var_fresh_splitBase_of_headFresh hheadFresh (heq ▸ Signature.mem_allNames_of_unaryRel
      (Δ := Δsmall) (u := SpecFn.defined rel) (List.Mem.head _))
  have hfun_mem : SpecFn.func rel ∈ (Δsmall.declVar ⟨x, .value⟩).unary :=
    Signature.mem_remove_unary.mpr ⟨List.Mem.head _, fun heq => hxNeFun heq.symm⟩
  have hrel_mem : SpecFn.defined rel ∈ (Δsmall.declVar ⟨x, .value⟩).unaryRel :=
    Signature.mem_remove_unaryRel.mpr ⟨List.Mem.head _, fun heq => hxNeDef heq.symm⟩
  have hax_wf : ax.wfIn Δsmall :=
    axioms_wfIn (Δ := Δsmall) hΔbig_wf hbody_wf hfun_mem hrel_mem ax hmem
  have hrelFresh_small : (⟨rel, .value, .value⟩ : FOL.BinaryRel).name ∉ Δsmall.allNames :=
    Signature.not_mem_allNames_addUnaryRel
      (Signature.not_mem_allNames_addUnary hheadFresh.relFresh
        (show rel ≠ (SpecFn.func rel).name from (SpecFn.funcName_ne_fn rel).symm))
      (show rel ≠ (SpecFn.defined rel).name from (SpecFn.defName_ne_fn rel).symm)
  have hagree :
      Env.agreeOn Δsmall
        (defInterpEnv Γ Δ ρ f rel x res e body)
        ((defInterpEnv Γ Δ ρ f rel x res e body).updateBinaryRel
          .value .value rel R) :=
    Env.agreeOn_update_fresh_binaryRel
      (b := ⟨rel, .value, .value⟩) hrelFresh_small
  exact (Formula.eval_env_agree hax_wf hagree).mp hbase

/-- Verifier-facing combined functionality: `semrel` is single-valued. -/
theorem bundle_semrel_functional
    {Γ : FunCtx} {Δ : Signature}
    {name rel arg : String} {body : Typed.Expr}
    {sym : FOL.BinaryRel} {fn : FOL.Unary} {drel : FOL.UnaryRel}
    {res : String} {bv : DefVal} {axs : List Formula}
    (hinfo : bundle Γ Δ name rel arg body
              = .ok (sym, fn, drel, res, bv, axs))
    (hΓrel : Γ.wfIn Δ) (hΓdef : Γ.defWfIn Δ)
    (hΔ : Δ.wf) (hf : InfoFresh Δ rel arg)
    (ρ : Env) (hρdet : Relation.BinaryRelDet Γ ρ ρ)
    (vin : Srt.value.denote) (y₁ y₂ : Srt.value.denote)
    (h₁ : semrel Γ Δ ρ name rel arg res body vin y₁)
    (h₂ : semrel Γ Δ ρ name rel arg res body vin y₂) :
    y₁ = y₂ := by
  unfold bundle at hinfo
  simp only [bind, Except.bind] at hinfo
  split at hinfo
  · cases hinfo
  rename_i bv' henc
  cases hinfo
  have hheadFresh := bundle_headFresh (Δ := Δ) (arg := arg) (rel := rel) hf
  exact relation_semrel_functional_of_encodeBody henc hΔ hΓrel hΓdef hheadFresh hρdet vin y₁ y₂ h₁ h₂

/-- Verifier-facing semrel/split graph compatibility for the new relation. -/
theorem bundle_semrel_compatible
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {name rel arg : String} {body : Typed.Expr}
    {sym : FOL.BinaryRel} {fn : FOL.Unary} {drel : FOL.UnaryRel}
    {res : String} {bv : DefVal} {axs : List Formula}
    (hinfo : bundle Γ Δ name rel arg body
              = .ok (sym, fn, drel, res, bv, axs))
    (hΓ : Γ.splitCompatible ρ)
    (hΓrel : Γ.wfIn Δ) (hΓdef : Γ.defWfIn Δ)
    (hΔ : Δ.wf) (hf : InfoFresh Δ rel arg)
    (hρdet : Relation.BinaryRelDet Γ ρ ρ)
    (vin vout : Srt.value.denote) :
    semrel Γ Δ ρ name rel arg res body vin vout ↔
      semdef Γ Δ ρ name rel arg res body bv vin ∧
        semFunc (semrel Γ Δ ρ name rel arg res body) vin = vout := by
  unfold bundle at hinfo
  simp only [bind, Except.bind] at hinfo
  split at hinfo
  · cases hinfo
  rename_i bv' henc
  cases hinfo
  have hheadFresh := bundle_headFresh (Δ := Δ) (arg := arg) (rel := rel) hf
  exact semrel_compatible henc hΓ hΓrel hΓdef hΔ hheadFresh hρdet vin vout

/-- Verifier-facing variant of `axioms_eval_updateBinaryRel`: the axioms emitted
by `bundle` evaluate to true under any choice of binary-relation
interpretation for the freshly declared `rel` symbol. -/
theorem bundle_eval_updateBinaryRel
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {name rel arg : String} {body : Typed.Expr}
    {sym : FOL.BinaryRel} {fn : FOL.Unary} {drel : FOL.UnaryRel}
    {res : String} {bv : DefVal} {axs : List Formula}
    (hinfo : bundle Γ Δ name rel arg body
              = .ok (sym, fn, drel, res, bv, axs))
    (hΓ : Γ.splitCompatible ρ)
    (hΓrel : Γ.wfIn Δ) (hΓdef : Γ.defWfIn Δ)
    (hΔ : Δ.wf) (hf : InfoFresh Δ rel arg)
    (hρdet : Relation.BinaryRelDet Γ ρ ρ)
    (R : ValRel) :
    ∀ ax ∈ axs,
      ax.eval ((defInterpEnv Γ Δ ρ name rel arg res body bv).updateBinaryRel
        .value .value rel R) := by
  unfold bundle at hinfo
  simp only [bind, Except.bind] at hinfo
  split at hinfo
  · cases hinfo
  rename_i bv' henc
  cases hinfo
  have hheadFresh := bundle_headFresh (Δ := Δ) (arg := arg) (rel := rel) hf
  exact axioms_eval_updateBinaryRel henc hΓ hΓrel hΓdef hΔ hheadFresh hρdet R

end Skolemize
end Verifier.RelationalEncoding
