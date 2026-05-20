-- SUMMARY: Solver-facing axioms and validity theorems for skolemized relational encoding.
import Mica.Verifier.RelationalEncoding.SkolemizeCompleteness


/-!
# Split Encoding Axioms

For each relation-marked recursive function, Skolemization exposes the
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
def definedIntroAxiom (fn : SpecFn) (x : TinyML.Var) (body : DefVal) : Formula :=
  .forall_ x .value
    (.implies body.defined (fn.isDefined (.var .value x)))

/-- If the function is defined on input `x`, its solver-facing value equals the
encoded body value. -/
def valueAxiom (fn : SpecFn) (x : TinyML.Var) (body : DefVal) : Formula :=
  .forall_ x .value
    (.implies
      (fn.isDefined (.var .value x))
      (.eq .value (fn.call (.var .value x)) body.value))

/-- Converse of `definedIntroAxiom`: if the function is defined on `x`, then the
encoded body is defined on `x`.  Experimental — exposing this lets the SMT
backend propagate definedness from a parent call into its recursive subterms. -/
def definedElimAxiom (fn : SpecFn) (x : TinyML.Var) (body : DefVal) : Formula :=
  .forall_ x .value
    (.implies (fn.isDefined (.var .value x)) body.defined)

/-- The solver-facing axioms emitted for a relation-marked function. -/
def axioms (fn : SpecFn) (x : TinyML.Var) (body : DefVal) : List Formula :=
  [definedIntroAxiom fn x body, valueAxiom fn x body,
   definedElimAxiom fn x body]

theorem axioms_wfIn {Δ : Signature} {fn : SpecFn} {x : String} {body : DefVal}
    (hΔx : (Δ.declVar ⟨x, .value⟩).wf)
    (hbody : body.wfIn (Δ.declVar ⟨x, .value⟩))
    (hfun : fn.func ∈ (Δ.declVar ⟨x, .value⟩).unary)
    (hrel : fn.defined ∈ (Δ.declVar ⟨x, .value⟩).unaryRel) :
    ∀ ax ∈ axioms fn x body, ax.wfIn Δ := by
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
    (f : TinyML.Var) (fn : SpecFn) (x res : TinyML.Var) (e : Typed.Expr)
    (body : DefVal) : Prop :=
  ∀ vin vout,
    semrel Γ Δ ρ f fn x res e vin vout ↔
      semdef Γ Δ ρ f fn x res e body vin ∧
        semFunc (semrel Γ Δ ρ f fn x res e) vin = vout


/-- The definedness-introduction axiom is valid under the semantic definedness
least fixpoint. This is the first solver-facing axiom and does not require the
eventual relation/graph equivalence. -/
theorem definedIntroAxiom_eval
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (henc : encodeBody Γ Δ f fn x res e = .ok body) :
    (definedIntroAxiom fn x body).eval
      (defInterpEnv Γ Δ ρ f fn x res e body) := by
  simp only [definedIntroAxiom, Formula.eval]
  intro vin hbody
  have hsem :
      semdef Γ Δ ρ f fn x res e body vin := by
    exact (semdef_unfold_of_encode (ρ := ρ) (x := x) (res := res) henc vin).mpr hbody
  exact (definedCall_eval_defInterpEnv (Γ := Γ) (Δ := Δ) (ρ := ρ)
    (f := f) (fn := fn) (x := x) (res := res) (e := e) (body := body) vin).mpr hsem

/-- The semantic relation induced by the relational encoding agrees with the
graph induced by the split definedness fixpoint and epsilon-selected value
function. This is a theorem of the two encodings, not an external invariant:
tail compatibility handles old function symbols, freshness prevents the new
symbols from clobbering them, and the paired-encoding completeness/soundness proof handles the
recursive body. -/
theorem semrel_compatible
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (henc : encodeBody Γ Δ f fn x res e = .ok body)
    (hΓ : Γ.splitCompatible ρ)
    (hΓwf : Γ.wfIn Δ)
    (hΔ : Δ.wf) (hheadFresh : HeadFresh Δ fn x res)
    (hρdet : Relation.BinaryRelDet Γ ρ ρ) :
    GraphCompatible Γ Δ ρ f fn x res e body := by
  intro vin vout
  constructor
  · intro hrel
    have hsplit :=
      semrel_complete henc hΓ hΓwf hΔ hheadFresh hρdet
        vin vout hrel
    have hdefined : semDefined (semrel Γ Δ ρ f fn x res e) vin := ⟨vout, hrel⟩
    have hfun :
      semFunc (semrel Γ Δ ρ f fn x res e) vin = vout :=
      relation_semrel_functional_of_encodeBody henc hΔ hΓwf hheadFresh hρdet vin
        (semFunc (semrel Γ Δ ρ f fn x res e) vin) vout
        (semFunc_spec hdefined) hrel
    exact ⟨hsplit.1, hfun⟩
  · intro hgraph
    rcases hgraph with ⟨hdef, hfun⟩
    let vbody :=
      body.value.eval
        ((defInterpEnv Γ Δ ρ f fn x res e body).updateConst .value x vin)
    have hrelBody :
        semrel Γ Δ ρ f fn x res e vin vbody :=
      semrel_sound henc hΓ hΓwf hΔ hheadFresh vin vbody
        hdef rfl
    have hdefined : semDefined (semrel Γ Δ ρ f fn x res e) vin := ⟨vbody, hrelBody⟩
    have hchosen :
        vbody = semFunc (semrel Γ Δ ρ f fn x res e) vin :=
      relation_semrel_functional_of_encodeBody henc hΔ hΓwf hheadFresh hρdet vin vbody
        (semFunc (semrel Γ Δ ρ f fn x res e) vin)
        hrelBody (semFunc_spec hdefined)
    exact semrel_sound henc hΓ hΓwf hΔ hheadFresh vin vout
      hdef (hchosen.trans hfun)

/-- The value axiom is valid under the canonical split interpretation extracted
from the relational semantics. -/
theorem valueAxiom_eval
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (henc : encodeBody Γ Δ f fn x res e = .ok body)
    (hΓ : Γ.splitCompatible ρ)
    (hΓwf : Γ.wfIn Δ)
    (hΔ : Δ.wf) (hheadFresh : HeadFresh Δ fn x res)
    (hρdet : Relation.BinaryRelDet Γ ρ ρ) :
    (valueAxiom fn x body).eval
      (defInterpEnv Γ Δ ρ f fn x res e body) := by
  simp only [valueAxiom, Formula.eval]
  intro vin hdef
  have hsem := (definedCall_eval_defInterpEnv (Γ := Γ) (Δ := Δ) (ρ := ρ)
    (f := f) (fn := fn) (x := x) (res := res) (e := e) (body := body) vin).mp hdef
  rw [valueCall_eval_defInterpEnv (Γ := Γ) (Δ := Δ) (ρ := ρ)
    (f := f) (fn := fn) (x := x) (res := res) (e := e) (body := body) vin]
  have hgraph := semrel_compatible henc hΓ hΓwf hΔ hheadFresh hρdet
  have hrel :
      semrel Γ Δ ρ f fn x res e vin
        (semFunc (semrel Γ Δ ρ f fn x res e) vin) :=
    (hgraph vin (semFunc (semrel Γ Δ ρ f fn x res e) vin)).mpr ⟨hsem, rfl⟩
  exact (semrel_complete henc hΓ hΓwf hΔ hheadFresh hρdet
    vin (semFunc (semrel Γ Δ ρ f fn x res e) vin) hrel).2.symm

/-- Semantic validity of the converse definedness axiom: under the least
fixpoint of `semdef`, the `semdef`/`defBody` unfolding goes both ways, so
`isDefined fn x` implies `body.defined` on `x`. -/
theorem definedElimAxiom_eval
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (henc : encodeBody Γ Δ f fn x res e = .ok body) :
    (definedElimAxiom fn x body).eval
      (defInterpEnv Γ Δ ρ f fn x res e body) := by
  simp only [definedElimAxiom, Formula.eval]
  intro vin hdef
  have hsem : semdef Γ Δ ρ f fn x res e body vin :=
    (definedCall_eval_defInterpEnv (Γ := Γ) (Δ := Δ) (ρ := ρ)
      (f := f) (fn := fn) (x := x) (res := res) (e := e) (body := body) vin).mp hdef
  exact (semdef_unfold_of_encode (ρ := ρ) (x := x) (res := res) henc vin).mp hsem

/-- Semantic validity of the split axioms under the canonical split
interpretation. -/
theorem axioms_eval
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (henc : encodeBody Γ Δ f fn x res e = .ok body)
    (hΓ : Γ.splitCompatible ρ)
    (hΓwf : Γ.wfIn Δ)
    (hΔ : Δ.wf) (hheadFresh : HeadFresh Δ fn x res)
    (hρdet : Relation.BinaryRelDet Γ ρ ρ) :
    ∀ ax ∈ axioms fn x body,
      ax.eval (defInterpEnv Γ Δ ρ f fn x res e body) := by
  intro ax hmem
  simp [axioms] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact definedIntroAxiom_eval henc
  · exact valueAxiom_eval henc hΓ hΓwf hΔ hheadFresh hρdet
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
structure InfoFresh (Δ : Signature) (fn : SpecFn) (x : String) : Prop where
  relFresh : fn.relName ∉ Δ.allNames
  funFresh : fn.funcName ∉ Δ.allNames
  defFresh : fn.defName ∉ Δ.allNames
  argFresh : x ∉ Δ.allNames
  argNeRel : x ≠ fn.relName
  argNeFun : x ≠ fn.funcName
  argNeDef : x ≠ fn.defName

/-- Declaring `fn`'s three split symbols on top of a well-formed `Δ` keeps the
signature well-formed, since the symbols are fresh for `Δ` and pairwise distinct. -/
theorem InfoFresh.wf_addSplit {Δ : Signature} {fn : SpecFn} {x : String}
    (hf : InfoFresh Δ fn x) (hΔ : Δ.wf) :
    (((Δ.addBinaryRel fn.rel).addUnary fn.func).addUnaryRel fn.defined).wf :=
  have hfun_fresh : fn.func.name ∉ (Δ.addBinaryRel fn.rel).allNames :=
    Signature.not_mem_allNames_addBinaryRel hf.funFresh (SpecFn.funcName_ne_relName fn)
  have hdef_fresh : fn.defined.name ∉ ((Δ.addBinaryRel fn.rel).addUnary fn.func).allNames :=
    Signature.not_mem_allNames_addUnary
      (Signature.not_mem_allNames_addBinaryRel hf.defFresh (SpecFn.defName_ne_relName fn))
      (SpecFn.defName_ne_funcName fn)
  Signature.wf_addUnaryRel
    (Signature.wf_addUnary (Signature.wf_addBinaryRel hΔ hf.relFresh) hfun_fresh) hdef_fresh

theorem freshName_avoid_props
    (Δ : Signature) (x fn : SpecFn) :
    let res := Fresh.freshName
      (Δ.allNames ++ [x, fn.relName, fn.funcName, fn.defName]) "r"
    res ∉ Δ.allNames ∧ res ≠ x ∧ res ≠ fn.relName ∧
      res ≠ fn.funcName ∧ res ≠ fn.defName := by
  have hres := Fresh.freshName_not_in_avoid
    (Δ.allNames ++ [x, fn.relName, fn.funcName, fn.defName]) "r"
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; exact hres (List.mem_append_left _ h)
  · intro h; apply hres; rw [h]; simp
  · intro h; apply hres; rw [h]; simp
  · intro h; apply hres; rw [h]; simp
  · intro h; apply hres; rw [h]; simp

/-- Derive `HeadFresh` from independent freshness hypotheses on each of the
solver-facing names. -/
theorem headFresh_of_fresh
    {Δ : Signature} {fn : SpecFn} {x res : String}
    (hf : InfoFresh Δ fn x)
    (hresΔ : res ∉ Δ.allNames)
    (hresRel : res ≠ fn.relName) (hresFun : res ≠ fn.funcName)
    (hresDef : res ≠ fn.defName) (hresx : res ≠ x) :
    HeadFresh Δ fn x res := by
  refine
    { relFresh := hf.relFresh
      funFresh := ?_
      defFresh := ?_
      argFresh := ?_
      resFresh := ?_ }
  · exact Signature.not_mem_allNames_addBinaryRel hf.funFresh (SpecFn.funcName_ne_relName fn)
  · exact Signature.not_mem_allNames_addUnary
      (Signature.not_mem_allNames_addBinaryRel hf.defFresh (SpecFn.defName_ne_relName fn))
      (SpecFn.defName_ne_funcName fn)
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
The declared symbols (`fn.rel`, `fn.func`, `fn.defined`) are determined by `fn`,
so this returns only the data the encoder computes: the canonical pinned-result
variable, the encoded body, and the list of solver-emitted axioms. -/
def bundle
    (Γ : FunCtx) (Δ : Signature) (f : TinyML.Var) (fn : SpecFn) (x : String) (e : Typed.Expr) :
    Except String (String × DefVal × List Formula) := do
  let res := Fresh.freshName
    (Δ.allNames ++ [x, fn.relName, fn.funcName, fn.defName]) "r"
  let bv ← encodeBody Γ Δ f fn x res e
  pure (res, bv, axioms fn x bv)

theorem bundle_headFresh
    {Δ : Signature} {x fn : SpecFn}
    (hf : InfoFresh Δ fn x) :
    HeadFresh Δ fn x
      (Fresh.freshName
        (Δ.allNames ++ [x, fn.relName, fn.funcName, fn.defName]) "r") := by
  obtain ⟨hresΔ, hresArg, hresRel, hresFun, hresDef⟩ :=
    freshName_avoid_props Δ x fn
  exact headFresh_of_fresh hf hresΔ hresRel hresFun hresDef hresArg

theorem bundle_wfIn
    {Γ : FunCtx} {Δ : Signature} {f : TinyML.Var} {fn : SpecFn} {x : String} {e : Typed.Expr}
    {res : String} {bv : DefVal} {axs : List Formula}
    (hinfo : bundle Γ Δ f fn x e = .ok (res, bv, axs))
    (hΔ : Δ.wf) (hΓwf : Γ.wfIn Δ)
    (hf : InfoFresh Δ fn x) :
    ∀ ax ∈ axs,
      ax.wfIn (((Δ.addBinaryRel fn.rel).addUnary fn.func).addUnaryRel fn.defined) := by
  unfold bundle at hinfo
  simp only [bind, Except.bind] at hinfo
  split at hinfo
  · cases hinfo
  rename_i bv' henc
  cases hinfo
  have hheadFresh := bundle_headFresh (Δ := Δ) (x := x) (fn := fn) hf
  set Δext : Signature :=
    ((Δ.addBinaryRel fn.rel).addUnary (fn.func)).addUnaryRel
      (fn.defined) with hΔext_def
  have hΔx_wf : (Δext.declVar ⟨x, .value⟩).wf := by
    simpa [Δext, bodySig] using bodySig_wf_of_headFresh hΔ hheadFresh
  have hbody_x : bv.wfIn (Δext.declVar ⟨x, .value⟩) := by
    show bv.wfIn (bodySig Δ fn x)
    exact encode_wfIn (Γ := Relation.ctx Γ f fn)
      (Δ := bodySig Δ fn x) e
      (bodySig_wf_of_headFresh hΔ hheadFresh)
      (ctx_splitWfIn_bodySig_of_headFresh hΓwf.split hheadFresh)
      (encodeBody_def_bodySig henc)
  have hfun_mem : fn.func ∈ (Δext.declVar ⟨x, .value⟩).unary :=
    Signature.mem_remove_unary.mpr ⟨List.Mem.head _, fun heq => hf.argNeFun heq.symm⟩
  have hrel_mem : fn.defined ∈ (Δext.declVar ⟨x, .value⟩).unaryRel :=
    Signature.mem_remove_unaryRel.mpr ⟨List.Mem.head _, fun heq => hf.argNeDef heq.symm⟩
  intro ax hmem
  exact axioms_wfIn (Δ := Δext) hΔx_wf hbody_x hfun_mem hrel_mem ax hmem


/-- The split axioms remain valid under any choice of binary relation
interpretation for `fn`. The body and axiom shapes only mention the
solver-facing split symbols, never `fn` as a binary predicate, so updating
`fn`'s binary interpretation is irrelevant. -/
theorem axioms_eval_updateBinaryRel
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (henc : encodeBody Γ Δ f fn x res e = .ok body)
    (hΓ : Γ.splitCompatible ρ)
    (hΓwf : Γ.wfIn Δ)
    (hΔ : Δ.wf) (hheadFresh : HeadFresh Δ fn x res)
    (hρdet : Relation.BinaryRelDet Γ ρ ρ)
    (R : ValRel) :
    ∀ ax ∈ axioms fn x body,
      ax.eval ((defInterpEnv Γ Δ ρ f fn x res e body).updateBinaryRel
        .value .value fn.relName R) := by
  intro ax hmem
  have hbase := axioms_eval henc hΓ hΓwf hΔ hheadFresh hρdet ax hmem
  set Δsmall : Signature :=
    (Δ.addUnary (fn.func)).addUnaryRel (fn.defined) with hΔsmall_def
  have hΔbig_wf : (Δsmall.declVar ⟨x, .value⟩).wf := by
    show (defvalBodySig Δ fn x).wf
    exact defvalBodySig_wf_of_headFresh hΔ hheadFresh
  have hbody_wf : body.wfIn (Δsmall.declVar ⟨x, .value⟩) := by
    show body.wfIn (defvalBodySig Δ fn x)
    exact encodeBody_wfIn_defvalBodySig hΔ hΓwf.split hheadFresh henc
  have hxNeFun : x ≠ fn.funcName := fun heq =>
    var_fresh_splitBase_of_headFresh hheadFresh (heq ▸ Signature.mem_allNames_of_unary
      (Δ := Δsmall) (u := fn.func) (List.Mem.head _))
  have hxNeDef : x ≠ fn.defName := fun heq =>
    var_fresh_splitBase_of_headFresh hheadFresh (heq ▸ Signature.mem_allNames_of_unaryRel
      (Δ := Δsmall) (u := fn.defined) (List.Mem.head _))
  have hfun_mem : fn.func ∈ (Δsmall.declVar ⟨x, .value⟩).unary :=
    Signature.mem_remove_unary.mpr ⟨List.Mem.head _, fun heq => hxNeFun heq.symm⟩
  have hrel_mem : fn.defined ∈ (Δsmall.declVar ⟨x, .value⟩).unaryRel :=
    Signature.mem_remove_unaryRel.mpr ⟨List.Mem.head _, fun heq => hxNeDef heq.symm⟩
  have hax_wf : ax.wfIn Δsmall :=
    axioms_wfIn (Δ := Δsmall) hΔbig_wf hbody_wf hfun_mem hrel_mem ax hmem
  have hrelFresh_small : fn.rel.name ∉ Δsmall.allNames :=
    Signature.not_mem_allNames_addUnaryRel
      (Signature.not_mem_allNames_addUnary hheadFresh.relFresh
        (show fn.relName ≠ (fn.func).name from (SpecFn.funcName_ne_relName fn).symm))
      (show fn.relName ≠ (fn.defined).name from (SpecFn.defName_ne_relName fn).symm)
  have hagree :
      Env.agreeOn Δsmall
        (defInterpEnv Γ Δ ρ f fn x res e body)
        ((defInterpEnv Γ Δ ρ f fn x res e body).updateBinaryRel
          .value .value fn.relName R) :=
    Env.agreeOn_update_fresh_binaryRel
      (b := fn.rel) hrelFresh_small
  exact (Formula.eval_env_agree hax_wf hagree).mp hbase

/-- Verifier-facing combined functionality: `semrel` is single-valued. -/
theorem bundle_semrel_functional
    {Γ : FunCtx} {Δ : Signature}
    {f fn x : String} {e : Typed.Expr}
    {res : String} {bv : DefVal} {axs : List Formula}
    (hinfo : bundle Γ Δ f fn x e = .ok (res, bv, axs))
    (hΓwf : Γ.wfIn Δ)
    (hΔ : Δ.wf) (hf : InfoFresh Δ fn x)
    (ρ : Env) (hρdet : Relation.BinaryRelDet Γ ρ ρ)
    (vin : Srt.value.denote) (y₁ y₂ : Srt.value.denote)
    (h₁ : semrel Γ Δ ρ f fn x res e vin y₁)
    (h₂ : semrel Γ Δ ρ f fn x res e vin y₂) :
    y₁ = y₂ := by
  unfold bundle at hinfo
  simp only [bind, Except.bind] at hinfo
  split at hinfo
  · cases hinfo
  rename_i bv' henc
  cases hinfo
  have hheadFresh := bundle_headFresh (Δ := Δ) (x := x) (fn := fn) hf
  exact relation_semrel_functional_of_encodeBody henc hΔ hΓwf hheadFresh hρdet vin y₁ y₂ h₁ h₂

/-- Verifier-facing semrel/split graph compatibility for the new relation. -/
theorem bundle_semrel_compatible
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f fn x : String} {e : Typed.Expr}
    {res : String} {bv : DefVal} {axs : List Formula}
    (hinfo : bundle Γ Δ f fn x e = .ok (res, bv, axs))
    (hΓ : Γ.splitCompatible ρ)
    (hΓwf : Γ.wfIn Δ)
    (hΔ : Δ.wf) (hf : InfoFresh Δ fn x)
    (hρdet : Relation.BinaryRelDet Γ ρ ρ)
    (vin vout : Srt.value.denote) :
    semrel Γ Δ ρ f fn x res e vin vout ↔
      semdef Γ Δ ρ f fn x res e bv vin ∧
        semFunc (semrel Γ Δ ρ f fn x res e) vin = vout := by
  unfold bundle at hinfo
  simp only [bind, Except.bind] at hinfo
  split at hinfo
  · cases hinfo
  rename_i bv' henc
  cases hinfo
  have hheadFresh := bundle_headFresh (Δ := Δ) (x := x) (fn := fn) hf
  exact semrel_compatible henc hΓ hΓwf hΔ hheadFresh hρdet vin vout

/-- Verifier-facing variant of `axioms_eval_updateBinaryRel`: the axioms emitted
by `bundle` evaluate to true under any choice of binary-relation
interpretation for the freshly declared `fn` symbol. -/
theorem bundle_eval_updateBinaryRel
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x : String} {e : Typed.Expr}
    {res : String} {bv : DefVal} {axs : List Formula}
    (hinfo : bundle Γ Δ f fn x e = .ok (res, bv, axs))
    (hΓ : Γ.splitCompatible ρ)
    (hΓwf : Γ.wfIn Δ)
    (hΔ : Δ.wf) (hf : InfoFresh Δ fn x)
    (hρdet : Relation.BinaryRelDet Γ ρ ρ)
    (R : ValRel) :
    ∀ ax ∈ axs,
      ax.eval ((defInterpEnv Γ Δ ρ f fn x res e bv).updateBinaryRel
        .value .value fn.relName R) := by
  unfold bundle at hinfo
  simp only [bind, Except.bind] at hinfo
  split at hinfo
  · cases hinfo
  rename_i bv' henc
  cases hinfo
  have hheadFresh := bundle_headFresh (Δ := Δ) (x := x) (fn := fn) hf
  exact axioms_eval_updateBinaryRel henc hΓ hΓwf hΔ hheadFresh hρdet R

end Skolemize
end Verifier.RelationalEncoding
