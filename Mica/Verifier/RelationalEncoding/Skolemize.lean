-- SUMMARY: Skolemization: the definedness/value encoding, what it denotes, and its equivalence with the relational encoding.
import Mica.Verifier.RelationalEncoding.Relation
import Mica.FOL.Subst

namespace Verifier.RelationalEncoding
open Relation

namespace Skolemize

/-! ## The defined/value pair -/

/-- Solver-facing expression encoding: a value term plus the condition under
which that value is defined. -/
structure DefVal where
  value : Term .value
  defined : Formula
  deriving DecidableEq

namespace DefVal

/-- A defined/value encoding is well-formed when both its value term and its
definedness formula are well-formed. -/
def wfIn (m : DefVal) (Δ : Signature) : Prop :=
  m.value.wfIn Δ ∧ m.defined.wfIn Δ

theorem wfIn.mono {m : DefVal} {Δ Δ' : Signature}
    (h : m.wfIn Δ) (hsub : Δ.Subset Δ') (hΔ' : Δ'.wf) : m.wfIn Δ' :=
  ⟨Term.wfIn_mono _ h.1 hsub hΔ', Formula.wfIn_mono _ h.2 hsub hΔ'⟩

/-- The definedness component of a `DefVal` encoding is monotone in the
environment's uninterpreted predicates. -/
private def Mono (m : DefVal) : Prop :=
  Eval.Mono (fun ρ m => m.defined.eval ρ) m

/-- A call's definedness condition is monotone in the environment's
uninterpreted predicates. -/
private theorem isDefined_mono (fn : SpecFn) (arg : Term .value) {ρ ρ' : Env}
    (hle : Env.le ρ ρ') (hdef : (fn.isDefined arg).eval ρ) :
    (fn.isDefined arg).eval ρ' := by
  simp only [SpecFn.isDefined, Formula.eval, UnPred.eval] at hdef ⊢
  rw [← Term.eval_env_le hle arg]
  exact hle.2.2.2.2.1 .value (fn.defName) (arg.eval ρ) hdef

end DefVal
end Skolemize

open Skolemize

variable {primitives : PrimEncodings} {Γ : FunCtx} {Δ : Signature} {ρ : Env}
variable {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
variable {body : DefVal} {φ : Formula}
variable {D : Srt.value.denote → Prop} {F : Srt.value.denote → Srt.value.denote}

namespace Expr

/-! ## From the IR to a defined/value pair -/

/-- Translate the IR into a value term paired with its definedness condition.
A call substitutes its total value function for the result name — the
substitution `σ` records what every enclosing call bound — and conjoins the
local definedness obligation. -/
def toDefVal (σ : Subst) : Expr → DefVal
  | .ret v => { value := v.subst σ, defined := .true_ }
  | .call fn arg r c =>
      let arg' := arg.subst σ
      let inner := Expr.toDefVal (σ.update .value r (fn.call arg')) c
      { value := inner.value, defined := .and (fn.isDefined arg') inner.defined }
  | .ite cond t e =>
      let cond' := cond.subst σ
      let thenVal := Expr.toDefVal σ t
      let elseVal := Expr.toDefVal σ e
      { value := .ite cond' thenVal.value elseVal.value
        defined := Formula.iteBool cond' thenVal.defined elseVal.defined }

private theorem toDefVal_wfIn {Γ : FunCtx} {avoid : List String} {Δ Δσ : Signature} {c : Expr} {σ : Subst}
    (hc : Expr.WfIn Γ avoid Δ c) (hΓ : Γ.funcWfIn Δσ) (hΔσ : Δσ.wf)
    (hσ : σ.wfIn Δ.vars Δσ) (hsym : Δ.SymbolSubset Δσ) :
    (Expr.toDefVal σ c).wfIn Δσ := by
  induction hc generalizing σ with
  | ret hv => exact ⟨Term.subst_wfIn hv hσ (fun _ h => h) hsym hΔσ, trivial⟩
  | @call Δ f fn arg r c hmem harg _ hfresh _ ih =>
      have hsyms := hΓ f fn hmem
      have harg' : (arg.subst σ).wfIn Δσ := Term.subst_wfIn harg hσ (fun _ h => h) hsym hΔσ
      have hσ' : (σ.update .value r (fn.call (arg.subst σ))).wfIn
          (Δ.declVar ⟨r, .value⟩).vars Δσ := by
        rw [Signature.vars_declVar_of_not_in (v := ⟨r, .value⟩) hfresh]
        exact Subst.wfIn_update hσ (SpecFn.call_wfIn hsyms.1 hΔσ harg')
      have hinner := ih hσ' (Signature.SymbolSubset.declVar hsym _)
      exact ⟨hinner.1, SpecFn.isDefined_wfIn hsyms.2 hΔσ harg', hinner.2⟩
  | ite hcond _ _ iht ihe =>
      have hcond' := Term.subst_wfIn hcond hσ (fun _ h => h) hsym hΔσ
      have ht := iht hσ hsym
      have he := ihe hσ hsym
      exact ⟨⟨hcond', ht.1, he.1⟩, Formula.iteBool_wfIn hcond' ht.2 he.2⟩

/-- Well-formedness of a successfully encoded body read as a `DefVal`. The
traversal gate signature `Δgate` may differ from the signature `Δenc` the local
environment lives in: the body encodings gate on the outer signature while
encoding into a body signature. -/
theorem toDefVal_wfIn_of_encode {primitives : PrimEncodings} {Γ : FunCtx}
    {Δgate Δenc : Signature} {δ : VarEnv} {s : NameSupply} {c : Expr}
    (e : Typed.Expr) (hlaw : primitives.Lawful) (hsub : Δgate.Subset Δenc)
    (hΔ : Δenc.wf) (hΓ : Γ.funcWfIn Δenc) (hδ : δ.wfIn Δenc) (hcov : s.Covers Δenc)
    (henc : encode primitives Δgate Γ δ e s = .ok c) :
    (Expr.toDefVal .id c).wfIn Δenc :=
  toDefVal_wfIn (encode_wfIn hlaw e hsub hΔ hδ hcov henc) hΓ hΔ
    (Subst.id_wfIn (fun _ h => h) hΔ) (Signature.SymbolSubset.refl _)

/-- The definedness of a func-form encoding is monotone in the environment's
uninterpreted predicates. -/
private theorem toDefVal_mono (σ : Subst) (c : Expr) : DefVal.Mono (Expr.toDefVal σ c) := by
  induction c generalizing σ with
  | ret v => intro ρ ρ' _ hdef; simp [Expr.toDefVal, Formula.eval]
  | call fn arg r c ih =>
      intro ρ ρ' hle hdef
      simp only [Expr.toDefVal, Formula.eval] at hdef ⊢
      exact ⟨DefVal.isDefined_mono fn (arg.subst σ) hle hdef.1, ih _ hle hdef.2⟩
  | ite cond t e iht ihe =>
      intro ρ ρ' hle hdef
      simp only [Expr.toDefVal, Formula.iteBool, Formula.eval] at hdef ⊢
      refine ⟨fun hcond => iht σ hle (hdef.1 ?_), fun hcond => ihe σ hle (hdef.2 ?_)⟩ <;>
        rw [Term.eval_env_le hle] <;> exact hcond

end Expr

/-! ## Body encoding -/

/-- Encode a function body using the solver-facing defined/value presentation.
It translates the very IR expression that `encodeFormula` translates
relationally. -/
def encodeDefVal (primitives : PrimEncodings) (Γ : FunCtx) (Δ : Signature)
    (f : TinyML.Var) (fn : SpecFn) (x res : TinyML.Var) (e : Typed.Expr) :
    Except String DefVal :=
  Expr.toDefVal .id <$> encodeBody primitives Γ Δ f fn x res e

/-- Successful func-form body encodings are well-formed in the relation-free body
signature, so they do not depend on how the head relation is interpreted. -/
theorem encodeDefVal_wfIn_funcArg
    (hlaw : primitives.Lawful) (hΔ : Δ.wf) (hΓ : Γ.funcWfIn Δ)
    (hfresh : EquationFresh Δ fn x res)
    (henc : encodeDefVal primitives Γ Δ f fn x res e = .ok body) :
    body.wfIn (SpecFn.Sig.funcArg Δ fn x) := by
  obtain ⟨c, hc, rfl⟩ := Except.map_eq_ok henc
  have hΔbody := hfresh.toSpecFnFresh.sigFuncArg_wf (x := x) hΔ
  exact Expr.toDefVal_wfIn_of_encode e hlaw hfresh.toSpecFnFresh.subset_sigFuncArg hΔbody
    (FunCtx.recursive_funcWfIn_funcArg hΓ hfresh)
    (VarEnv.ofSignature_funcArg (Δ := Δ) (fn := fn) (x := x) ▸ VarEnv.ofSignature_wfIn hΔbody)
    hfresh.covers_sigFuncArg hc

theorem encodeDefVal_wfIn_bothArg
    (hlaw : primitives.Lawful) (hΔ : Δ.wf) (hΓ : Γ.funcWfIn Δ)
    (hfresh : EquationFresh Δ fn x res)
    (henc : encodeDefVal primitives Γ Δ f fn x res e = .ok body) :
    body.wfIn (SpecFn.Sig.bothArg Δ fn x) :=
  (encodeDefVal_wfIn_funcArg hlaw hΔ hΓ hfresh henc).mono SpecFn.Sig.funcArg_subset_bothArg
    (hfresh.toSpecFnFresh.sigBothArg_wf hΔ)

/-- A successful func-form body encoding exposes the shared IR expression behind
it: the func-form body is its `toDefVal` reading, the relational body encoding
is its `toFormula` reading, and it is well-formed in the body signature. -/
private theorem encodeDefVal_witness
    (hlaw : primitives.Lawful) (hΔ : Δ.wf) (hfresh : EquationFresh Δ fn x res)
    (henc : encodeDefVal primitives Γ Δ f fn x res e = .ok body) :
    ∃ c, body = Expr.toDefVal .id c ∧
      encodeFormula primitives Γ Δ f fn x res e = .ok (Expr.toFormula res c) ∧
      Expr.WfIn (FunCtx.recursive Γ f fn) (SpecFn.reserved fn x res) (SpecFn.Sig.bothArg Δ fn x) c := by
  obtain ⟨c, hc, rfl⟩ := Except.map_eq_ok henc
  have hΔrel := hfresh.toSpecFnFresh.sigRelArg_wf (x := x) hΔ
  refine ⟨c, rfl, by simp [encodeFormula, hc], ?_⟩
  exact ((encode_wfIn hlaw e hfresh.toSpecFnFresh.subset_sigRelArg hΔrel
      (VarEnv.ofSignature_wfIn hΔrel) hfresh.covers_sigRelArg hc).weaken
      SpecFn.reserved_subset_supply).mono SpecFn.Sig.relArg_subset_bothArg
      (hfresh.toSpecFnFresh.sigBothArg_wf hΔ)
      (SpecFn.names_of_subset_bothArgRes hfresh.sigBothArg_subset_sigBothArgRes hfresh.toSpecFnFresh.subset_sigRelArg)

namespace ValRel

/-! ## Relations as a definedness predicate and a value function -/

def toDef (R : ValRel) (x : Srt.value.denote) : Prop :=
  ∃ y, R x y

/-- The value function induced by a relation: choose an arbitrary related
output when one exists, and Lean's default epsilon value otherwise. -/
noncomputable def toFunc (R : ValRel) (x : Srt.value.denote) : Srt.value.denote :=
  Classical.epsilon (R x)

/-- The relation presented by a definedness predicate and a value function:
the value function's graph, restricted to the definedness domain. -/
private def ofDefFunc (D : Srt.value.denote → Prop) (F : Srt.value.denote → Srt.value.denote) :
    ValRel :=
  fun a b => D a ∧ F a = b

/-- If the relation is defined at `x`, `ValRel.toFunc` chooses a related output. -/
theorem toFunc_spec {R : ValRel} {x : Srt.value.denote}
    (h : ValRel.toDef R x) : R x (ValRel.toFunc R x) := by
  unfold ValRel.toDef ValRel.toFunc at *
  exact Classical.epsilon_spec h

/-- A candidate definedness predicate within the domain of `R`, paired with the
value function chosen from `R`, presents a sub-relation of `R`. -/
private theorem ofDefFunc_le {R : ValRel} {D : Srt.value.denote → Prop}
    (hdom : PredicateFix.le D (ValRel.toDef R)) :
    RelationFix.le (ofDefFunc D (ValRel.toFunc R)) R := by
  intro a b hab
  have hchosen : R a (ValRel.toFunc R a) := ValRel.toFunc_spec (hdom a hab.1)
  rw [hab.2] at hchosen
  exact hchosen

end ValRel

/-! ## Environments interpreting the head symbols -/

/-- The environment that interprets `fn`: its binary relation, its value
function, and its definedness predicate. The defined/value encoding never
mentions the relation, so its readings do not depend on `R`. -/
def _root_.SpecFn.Env.both (ρ : Env) (fn : SpecFn)
    (R : ValRel) (D : Srt.value.denote → Prop)
    (F : Srt.value.denote → Srt.value.denote) : Env :=
  ((ρ.updateBinaryRel .value .value fn.relName R).updateUnary .value .value (fn.funcName) F)
    |>.updateUnaryRel .value (fn.defName) D

/-- Interpreting the triple's three fresh names leaves `Δ`-agreement intact. -/
theorem _root_.SpecFn.Env.both_agreeOn {R : ValRel}
    (hrel : fn.relName ∉ Δ.allNames)
    (hfun : fn.funcName ∉ Δ.allNames)
    (hdef : fn.defName ∉ Δ.allNames) :
    Env.agreeOn Δ ρ (SpecFn.Env.both ρ fn R D F) :=
  Env.agreeOn_trans
    (Env.agreeOn_update_fresh_binaryRel (b := fn.rel) (f := R) hrel)
    (Env.agreeOn_trans
      (Env.agreeOn_update_fresh_unary (u := fn.func) (f := F) hfun)
      (Env.agreeOn_update_fresh_unaryRel (u := fn.defined) (f := D) hdef))

private theorem _root_.SpecFn.Env.both_evalDefined (fn : SpecFn) (ρ : Env) {R : ValRel}
    (v : Srt.value.denote) :
    SpecFn.evalDefined fn (SpecFn.Env.both ρ fn R D F) v ↔ D v := by
  simp [SpecFn.Env.both, SpecFn.evalDefined, SpecFn.defined, SpecFn.defName,
    Env.updateUnaryRel, Env.updateUnary, Env.updateBinaryRel]

private theorem _root_.SpecFn.Env.both_evalCall (fn : SpecFn) (ρ : Env) {R : ValRel}
    (v : Srt.value.denote) :
    SpecFn.evalCall fn (SpecFn.Env.both ρ fn R D F) v = F v := by
  simp [SpecFn.Env.both, SpecFn.evalCall, SpecFn.func, SpecFn.funcName,
    Env.updateUnaryRel, Env.updateUnary, Env.updateBinaryRel]

private theorem _root_.SpecFn.Env.both_evalRelates (fn : SpecFn) (ρ : Env) {R : ValRel}
    (a b : Srt.value.denote) :
    SpecFn.evalRelates fn (SpecFn.Env.both ρ fn R D F) a b ↔ R a b := by
  simp [SpecFn.Env.both, SpecFn.evalRelates, SpecFn.rel, SpecFn.relName,
    Env.updateUnaryRel, Env.updateUnary, Env.updateBinaryRel]

/-- With graph-shaped interpretations the three symbols agree: the relation
reads as the graph of the value function on the definedness domain. -/
theorem _root_.SpecFn.Env.both_agreement (fn : SpecFn) (ρ : Env) {R : ValRel}
    (hgraph : ∀ a b, R a b ↔ D a ∧ F a = b) (a b : Srt.value.denote) :
    SpecFn.evalRelates fn (SpecFn.Env.both ρ fn R D F) a b ↔
      SpecFn.evalDefined fn (SpecFn.Env.both ρ fn R D F) a ∧
        SpecFn.evalCall fn (SpecFn.Env.both ρ fn R D F) a = b := by
  simp only [SpecFn.Env.both_evalRelates, SpecFn.Env.both_evalDefined,
    SpecFn.Env.both_evalCall]
  exact hgraph a b

/-- Choosing the relation up front and overwriting it afterwards give the same
environment. -/
theorem _root_.SpecFn.Env.both_updateBinaryRel {R R' : ValRel} :
    (SpecFn.Env.both ρ fn R D F).updateBinaryRel .value .value fn.relName R' =
      SpecFn.Env.both ρ fn R' D F := by
  refine Env.ext rfl rfl rfl rfl rfl ?_
  funext τ₁ τ₂ name
  simp only [SpecFn.Env.both, Env.updateBinaryRel, Env.updateUnary, Env.updateUnaryRel]
  split <;> rfl

/-- The environment of a func-form candidate: the head relation is read as the
graph of the candidate, which keeps the three symbols in agreement while the
func-form body never consults the relation. -/
private def _root_.SpecFn.Env.graph (ρ : Env) (fn : SpecFn) (D : Srt.value.denote → Prop)
    (F : Srt.value.denote → Srt.value.denote) : Env :=
  SpecFn.Env.both ρ fn (ValRel.ofDefFunc D F) D F

/-- Environment for evaluating a func-form encoded body at input `vin`. -/
private def _root_.SpecFn.Env.graphArg (ρ : Env) (fn : SpecFn) (x : String)
    (D : Srt.value.denote → Prop)
    (F : Srt.value.denote → Srt.value.denote)
    (vin : Srt.value.denote) : Env :=
  (SpecFn.Env.graph ρ fn D F).updateConst .value x vin

/-- Increasing the candidate definedness predicate increases the corresponding
environments. -/
private theorem _root_.SpecFn.Env.graph_le {D D' : Srt.value.denote → Prop} (hDD' : PredicateFix.le D D') :
    Env.le (SpecFn.Env.graph ρ fn D F) (SpecFn.Env.graph ρ fn D' F) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro τ name a h
    simp only [SpecFn.Env.graph, SpecFn.Env.both, Env.updateUnaryRel] at h ⊢
    split at h
    · rename_i heq
      rcases heq with ⟨rfl, rfl⟩
      simpa only [Env.updateUnaryRel, dif_pos (And.intro rfl rfl)] using hDD' a h
    · rename_i hne
      simp only [dif_neg hne]
      exact h
  · intro τ₁ τ₂ name a b h
    simp only [SpecFn.Env.graph, SpecFn.Env.both, Env.updateUnaryRel, Env.updateUnary,
      Env.updateBinaryRel] at h ⊢
    split at h
    · rename_i heq
      rcases heq with ⟨rfl, rfl, rfl⟩
      simpa only [dif_pos (And.intro rfl (And.intro rfl rfl)), ValRel.ofDefFunc] using
        And.imp_left (hDD' a) h
    · rename_i hne
      simp only [dif_neg hne]
      exact h

/-- Extending a context in agreement with a fresh head preserves agreement: in
`SpecFn.Env.graph` the head relation is a graph by construction. -/
private theorem _root_.Verifier.RelationalEncoding.FunCtx.Agreement.cons
    (hΓ : FunCtx.Agreement Γ ρ) (hfresh : FunCtx.unused Γ fn) :
    FunCtx.Agreement ((f, fn) :: Γ) (SpecFn.Env.graph ρ fn D F) := by
  intro g fn' hmem a b
  cases hmem with
  | head => exact SpecFn.Env.both_agreement fn ρ (fun _ _ => Iff.rfl) a b
  | tail _ htail =>
      have hnames := hfresh g fn' htail
      simpa [SpecFn.evalRelates, SpecFn.evalDefined, SpecFn.evalCall,
        SpecFn.rel, SpecFn.defined, SpecFn.func,
        SpecFn.Env.graph, SpecFn.Env.both, Env.updateBinaryRel, Env.updateUnary, Env.updateUnaryRel,
        hnames.1, hnames.2.1, hnames.2.2] using hΓ g fn' htail a b

namespace Skolemize

/-! ## The func-form body operator -/

/-- The definedness a func-form body claims at `vin` under a recursive candidate. -/
def eval (ρ : Env) (fn : SpecFn) (x : String) (body : DefVal)
    (F : Srt.value.denote → Srt.value.denote) :
    (Srt.value.denote → Prop) → Srt.value.denote → Prop :=
  fun D vin => body.defined.eval (SpecFn.Env.graphArg ρ fn x D F vin)

/-- The value a func-form body computes at `vin` under a recursive candidate. -/
private def value (ρ : Env) (fn : SpecFn) (x : String) (body : DefVal)
    (F : Srt.value.denote → Srt.value.denote) (D : Srt.value.denote → Prop)
    (vin : Srt.value.denote) : Srt.value.denote :=
  body.value.eval (SpecFn.Env.graphArg ρ fn x D F vin)

/-- The definedness body operator is monotone whenever the encoded body has
monotone definedness. -/
private theorem eval_mono {x : String} (hbody : DefVal.Mono body) :
    PredicateFix.Mono (Skolemize.eval ρ fn x body F) := by
  intro D D' hDD' vin hdef
  exact hbody (Env.le.updateConst (SpecFn.Env.graph_le (ρ := ρ) (fn := fn)
    (D := D) (D' := D') (F := F) hDD') .value x vin) hdef

end Skolemize

/-- What the definedness predicate denotes: the least fixpoint of the encoded
definedness condition, read with the value function chosen from the relation. -/
noncomputable def _root_.SpecFn.Semantics.defined (primitives : PrimEncodings)
    (Γ : FunCtx) (Δ : Signature) (ρ : Env)
    (f : TinyML.Var) (fn : SpecFn) (x res : TinyML.Var) (e : Typed.Expr)
    (body : DefVal) : Srt.value.denote → Prop :=
  PredicateFix.lfp (Skolemize.eval ρ fn x body
    (ValRel.toFunc (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e)))

/-- The environment the three symbols denote, read off the relation. -/
noncomputable def _root_.SpecFn.Semantics.env (primitives : PrimEncodings)
    (Γ : FunCtx) (Δ : Signature) (ρ : Env)
    (f : TinyML.Var) (fn : SpecFn) (x res : TinyML.Var) (e : Typed.Expr)
    (body : DefVal) : Env :=
  SpecFn.Env.graph ρ fn (SpecFn.Semantics.defined primitives Γ Δ ρ f fn x res e body)
    (ValRel.toFunc (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e))

/-- Unfolding principle specialized to a successfully encoded `DefVal` body. -/
theorem _root_.SpecFn.Semantics.defined_unfold
    (henc : encodeDefVal primitives Γ Δ f fn x res e = .ok body)
    (vin : Srt.value.denote) :
    SpecFn.Semantics.defined primitives Γ Δ ρ f fn x res e body vin ↔
      Skolemize.eval ρ fn x body
        (ValRel.toFunc (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e))
        (SpecFn.Semantics.defined primitives Γ Δ ρ f fn x res e body) vin := by
  obtain ⟨c, _, rfl⟩ := Except.map_eq_ok henc
  exact PredicateFix.lfp_unfold (eval_mono (Expr.toDefVal_mono _ c)) vin

/-- Under the canonical interpretation, the definedness symbol denotes
`SpecFn.Semantics.defined`. -/
theorem _root_.SpecFn.Semantics.env_isDefined (vin : Srt.value.denote) :
    (fn.isDefined (.var .value x)).eval
      ((SpecFn.Semantics.env primitives Γ Δ ρ f fn x res e body).updateConst .value x vin)
      ↔ SpecFn.Semantics.defined primitives Γ Δ ρ f fn x res e body vin := by
  simp [SpecFn.isDefined, Formula.eval, UnPred.eval, Term.eval,
    Env.lookupConst_updateConst_same]
  unfold SpecFn.Semantics.env SpecFn.Env.graph SpecFn.Env.both
  simp [Env.updateConst_unaryRel, Env.updateUnaryRel]

/-- Under the canonical interpretation, the value symbol denotes the
chosen witness function of `SpecFn.Semantics.rel`. -/
theorem _root_.SpecFn.Semantics.env_call (vin : Srt.value.denote) :
    (fn.call (.var .value x)).eval
      ((SpecFn.Semantics.env primitives Γ Δ ρ f fn x res e body).updateConst .value x vin)
      =
    ValRel.toFunc (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e) vin := by
  simp only [SpecFn.call, Term.eval, UnOp.eval, Env.lookupConst_updateConst_same]
  rw [Env.updateConst_unary]
  change ((ρ.updateUnary .value .value (fn.funcName)
    (ValRel.toFunc (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e))).unary .value .value (fn.funcName) vin =
      ValRel.toFunc (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e) vin)
  simp [Env.updateUnary]

namespace Skolemize

/-! ## The two readings of the IR agree

Both encodings consume the same `Expr`, so their agreement is a three-case
induction on it. `Δ` grows with the names the calls bind, `ρrel` with the
witnesses the relational side picks for them, and `σ` with the value terms the
func-form side substituted; `SubstAgree` says the two accounts of those names
agree. -/

/-- The invariant the two encodings are compared under: the environment the
relational side reads and the one the func-form side reads after its substitution
give every term of `Δ` the same value. -/
private def SubstAgree (Δ : Signature) (ρrel ρdef : Env) (σ : Subst) : Prop :=
  Env.agreeOnTerms Δ ρrel (σ.eval ρdef)

private theorem substAgree_refl {ρ : Env} : SubstAgree Δ ρ ρ .id :=
  Env.agreeOnTerms_of_agreeOn Env.agreeOn_refl

/-- Reading a term of `Δ` on either side of `SubstAgree` gives the same value. -/
private theorem eval_substAgree {Δ Δσ : Signature} {ρrel ρdef : Env} {σ : Subst}
    {τ : Srt} {t : Term τ}
    (hagree : SubstAgree Δ ρrel ρdef σ) (ht : t.wfIn Δ)
    (hσ : σ.wfIn Δ.vars Δσ) (hΔσ : Δσ.wf) :
    Term.eval ρrel t = Term.eval ρdef (t.subst σ) := by
  rw [Term.eval_subst ht hσ hΔσ]
  exact Term.eval_agreeOnTerms ht hagree

/-- Binding a call's result extends the invariant: the relational side reads the
witness it chose, the func-form side the value term it substituted. -/
private theorem substAgree_bind {ρrel ρdef : Env} {σ : Subst} {r : String} {t : Term .value}
    (hagree : SubstAgree Δ ρrel ρdef σ) :
    SubstAgree (Δ.declVar ⟨r, .value⟩) (ρrel.updateConst .value r (Term.eval ρdef t))
      ρdef (σ.update .value r t) := by
  unfold SubstAgree
  rw [Subst.eval_update]
  exact Env.agreeOnTerms_declVar hagree

private theorem toDefVal_iff {Δbase : Signature} {res : String} {ρdef : Env}
    (hΓdef : Γ.funcWfIn Δbase) (hΔbase : Δbase.wf) :
    ∀ {avoid : List String} {Δ : Signature} {c : Expr} {σ : Subst} {ρrel : Env},
      Expr.WfIn Γ avoid Δ c → res ∈ avoid →
      Δbase.Subset Δ → Δ.SymbolSubset Δbase →
      σ.wfIn Δ.vars Δbase → Γ.Agreement ρrel →
      Env.agreeOn Δbase ρrel ρdef → SubstAgree Δ ρrel ρdef σ →
      ρrel.lookupConst .value res = ρdef.lookupConst .value res →
      ((Expr.toFormula res c).eval ρrel ↔
        (Expr.toDefVal σ c).defined.eval ρdef ∧
          (Expr.toDefVal σ c).value.eval ρdef = ρdef.lookupConst .value res) := by
  intro avoid Δ c σ ρrel hc hresAvoid
  induction hc generalizing σ ρrel with
  | @ret Δ v hv =>
      intro _ _ hσ _ _ hagree hres
      simp only [Expr.toFormula, Expr.toDefVal, Formula.eval, Term.eval, true_and]
      rw [eval_substAgree hagree hv hσ hΔbase, hres]
  | @call Δ f fn arg r c hmem harg hr hfresh _ ih =>
      intro hsubBase hsym hσ hΓc hagBase hagree hres
      have hfreshBase : r ∉ Δbase.allNames :=
        fun hm => hfresh (Signature.allNames_subset hsubBase r hm)
      have hres_ne : res ≠ r := fun heq => hr (heq ▸ hresAvoid)
      have hsyms := hΓdef f fn hmem
      have hargEval : Term.eval ρrel arg = Term.eval ρdef (arg.subst σ) :=
        eval_substAgree hagree harg hσ hΔbase
      have hunary : ρrel.unary .value .value fn.funcName =
          ρdef.unary .value .value fn.funcName := hagBase.2.2.1 fn.func hsyms.1
      have hunaryRel : ρrel.unaryRel .value fn.defName =
          ρdef.unaryRel .value fn.defName := hagBase.2.2.2.2.2.1 fn.defined hsyms.2
      have hdefIff : fn.evalDefined ρrel (Term.eval ρrel arg) ↔
          (fn.isDefined (arg.subst σ)).eval ρdef := by
        rw [show fn.evalDefined ρrel = fn.evalDefined ρdef from hunaryRel, hargEval]
        simp [SpecFn.isDefined, SpecFn.evalDefined, SpecFn.defined, Formula.eval, UnPred.eval]
      have hcallEq : fn.evalCall ρrel (Term.eval ρrel arg) =
          Term.eval ρdef (fn.call (arg.subst σ)) := by
        rw [show fn.evalCall ρrel = fn.evalCall ρdef from hunary, hargEval]
        simp [SpecFn.call, SpecFn.evalCall, SpecFn.func, Term.eval]
      have ih' := ih (hsubBase.trans (Signature.subset_declVar_of_fresh hfresh))
        (Signature.SymbolSubset.declVar hsym _)
        (by
          rw [Signature.vars_declVar_of_not_in (v := ⟨r, .value⟩) hfresh]
          exact Subst.wfIn_update hσ
            (SpecFn.call_wfIn hsyms.1 hΔbase
              (Term.subst_wfIn harg hσ (fun _ h => h) hsym hΔbase)))
        (FunCtx.Agreement.updateConst hΓc .value r _)
        (Env.agreeOn_trans
          (Env.agreeOn_symm
            (Env.agreeOn_update_fresh_const (c := ⟨r, .value⟩) hfreshBase)) hagBase)
        (substAgree_bind hagree)
        (by rw [Env.lookupConst_updateConst_ne hres_ne]; exact hres)
      simp only [Expr.toFormula, Expr.toDefVal, Formula.eval]
      constructor
      · rintro ⟨w, hcall, hrest⟩
        have hcall' : fn.evalRelates ρrel (Term.eval ρrel arg) w := by
          simpa [SpecFn.relates, SpecFn.evalRelates, SpecFn.rel, Formula.eval, BinPred.eval,
            Term.eval, Env.updateConst_binaryRel, Env.lookupConst_updateConst_same,
            Term.eval_update_fresh harg hfresh] using hcall
        obtain ⟨hdefRel, hcallRel⟩ := (hΓc f fn hmem _ w).mp hcall'
        have hw : w = Term.eval ρdef (fn.call (arg.subst σ)) := by
          rw [← hcallRel]; exact hcallEq
        subst hw
        obtain ⟨hrestDef, hrestVal⟩ := ih'.mp hrest
        exact ⟨⟨hdefIff.mp hdefRel, hrestDef⟩, hrestVal⟩
      · rintro ⟨⟨hdefCall, hdefRest⟩, hval⟩
        refine ⟨Term.eval ρdef (fn.call (arg.subst σ)), ?_, ih'.mpr ⟨hdefRest, hval⟩⟩
        have hedge := (hΓc f fn hmem (Term.eval ρrel arg)
          (Term.eval ρdef (fn.call (arg.subst σ)))).mpr ⟨hdefIff.mpr hdefCall, hcallEq⟩
        simpa [SpecFn.relates, Formula.eval, BinPred.eval, Term.eval,
          Env.updateConst_binaryRel, Env.lookupConst_updateConst_same,
          Term.eval_update_fresh harg hfresh] using hedge
  | @ite Δ cond t e hcond _ _ iht ihe =>
      intro hsubBase hsym hσ hΓc hagBase hagree hres
      have hcondEval : Term.eval ρrel cond = Term.eval ρdef (cond.subst σ) :=
        eval_substAgree hagree hcond hσ hΔbase
      have ht := iht hsubBase hsym hσ hΓc hagBase hagree hres
      have he := ihe hsubBase hsym hσ hΓc hagBase hagree hres
      simp only [Expr.toFormula, Expr.toDefVal, Formula.iteBool, Formula.eval, Term.eval,
        Const.denote]
      cases hcv : Term.eval ρrel cond with
      | false =>
          have hc2 : Term.eval ρdef (cond.subst σ) = false := by rw [← hcondEval]; exact hcv
          simp [hc2, he]
      | true =>
          have hc2 : Term.eval ρdef (cond.subst σ) = true := by rw [← hcondEval]; exact hcv
          simp [hc2, ht]

/-- Where the three symbols agree, the two readings of one body agree: the
relational formula holds at `vout` exactly when the func-form body is defined and
evaluates to `vout`. -/
private theorem body_eval_iff {ρboth : Env} {c : Expr}
    (hΓdef : Γ.funcWfIn Δ) (hΔ : Δ.wf) (hfresh : EquationFresh Δ fn x res)
    (hcWf : Expr.WfIn (FunCtx.recursive Γ f fn) (SpecFn.reserved fn x res) (SpecFn.Sig.bothArg Δ fn x) c)
    (hΓagree : (FunCtx.recursive Γ f fn).Agreement ρboth)
    (vin vout : Srt.value.denote) :
    (Expr.toFormula res c).eval
        ((ρboth.updateConst .value x vin).updateConst .value res vout) ↔
      ((Expr.toDefVal .id c).defined.eval
          ((ρboth.updateConst .value x vin).updateConst .value res vout) ∧
        (Expr.toDefVal .id c).value.eval
          ((ρboth.updateConst .value x vin).updateConst .value res vout) = vout) := by
  have hΔbody := hfresh.toSpecFnFresh.sigBothArg_wf (x := x) hΔ
  have h := toDefVal_iff (res := res) (FunCtx.recursive_funcWfIn_bothArg hΓdef hfresh) hΔbody
    hcWf (by simp [SpecFn.reserved]) (Signature.Subset.refl _) (Signature.SymbolSubset.refl _)
    (Subst.id_wfIn (fun _ h => h) hΔbody)
    (FunCtx.Agreement.updateConst
      (FunCtx.Agreement.updateConst hΓagree .value x vin) .value res vout)
    Env.agreeOn_refl substAgree_refl rfl
  simpa [Env.lookupConst_updateConst_same] using h

/-- The func-form body never mentions the result variable, so pinning `res` does not
change what it reads. -/
private theorem encodeDefVal_eval_updateConst_res
    (hlaw : primitives.Lawful) (hΔ : Δ.wf) (hΓ : Γ.funcWfIn Δ)
    (hfresh : EquationFresh Δ fn x res)
    (henc : encodeDefVal primitives Γ Δ f fn x res e = .ok body)
    (vin vout : Srt.value.denote) :
    (body.defined.eval ((SpecFn.Env.graphArg ρ fn x D F vin).updateConst .value res vout) ↔
        body.defined.eval (SpecFn.Env.graphArg ρ fn x D F vin)) ∧
      body.value.eval ((SpecFn.Env.graphArg ρ fn x D F vin).updateConst .value res vout) =
        body.value.eval (SpecFn.Env.graphArg ρ fn x D F vin) := by
  have hbody : body.wfIn (SpecFn.Sig.bothArg Δ fn x) := encodeDefVal_wfIn_bothArg hlaw hΔ hΓ hfresh henc
  have hag : Env.agreeOn (SpecFn.Sig.bothArg Δ fn x) (SpecFn.Env.graphArg ρ fn x D F vin)
      ((SpecFn.Env.graphArg ρ fn x D F vin).updateConst .value res vout) :=
    Env.agreeOn_update_fresh_const (c := ⟨res, .value⟩) hfresh.resFresh_sigBothArg
  exact ⟨(Formula.eval_env_agree hbody.2 hag).symm, (Term.eval_env_agree hbody.1 hag).symm⟩

/-- The relational run environment and the three-symbol environment pinned at `x` and
`res` agree on everything the relational body can read. -/
private theorem rel_agreeOn_both {R : ValRel}
    (hfresh : EquationFresh Δ fn x res) (vin vout : Srt.value.denote) :
    Env.agreeOn (SpecFn.Sig.relArgRes Δ fn x res)
      (SpecFn.Env.rel ρ fn x res R vin vout)
      (((SpecFn.Env.both ρ fn R D F).updateConst .value x vin).updateConst .value res vout) := by
  have hdefFresh : fn.defName ∉ (SpecFn.Sig.rel Δ fn).allNames :=
    Signature.not_mem_allNames_addBinaryRel hfresh.toSpecFnFresh.defFresh
      (SpecFn.defName_ne_relName fn)
  have hbase : Env.agreeOn (SpecFn.Sig.rel Δ fn)
      (ρ.updateBinaryRel .value .value fn.relName R) (SpecFn.Env.both ρ fn R D F) :=
    Env.agreeOn_trans
      (Env.agreeOn_update_fresh_unary (u := fn.func) (f := F)
        (Signature.not_mem_allNames_addBinaryRel hfresh.toSpecFnFresh.funcFresh
          (SpecFn.funcName_ne_relName fn)))
      (Env.agreeOn_update_fresh_unaryRel (u := fn.defined) (f := D) hdefFresh)
  exact Env.agreeOn_declVar (Env.agreeOn_declVar hbase)

/-- Relational body encodings are well-formed in the relational run signature. -/
private theorem relEncodeBody_wfIn
    (hlaw : primitives.Lawful) (hΓ : Γ.relWfIn Δ) (hΔ : Δ.wf)
    (hfresh : EquationFresh Δ fn x res)
    (henc : encodeFormula primitives Γ Δ f fn x res e = .ok φ) :
    φ.wfIn (SpecFn.Sig.relArgRes Δ fn x res) := by
  obtain ⟨c, hc, rfl⟩ := Except.map_eq_ok henc
  have hΔrel := hfresh.toSpecFnFresh.sigRelArg_wf (x := x) hΔ
  have hsig := hfresh.sigRelArgRes_wf hΔ
  have hcWf : Expr.WfIn (FunCtx.recursive Γ f fn) (SpecFn.reserved fn x res)
      (SpecFn.Sig.relArg Δ fn x) c :=
    (encode_wfIn hlaw e hfresh.toSpecFnFresh.subset_sigRelArg hΔrel
      (VarEnv.ofSignature_wfIn hΔrel) hfresh.covers_sigRelArg hc).weaken
      SpecFn.reserved_subset_supply
  exact Expr.toFormula_wfIn
    (hcWf.mono hfresh.sigRelArg_subset_sigRelArgRes hsig
      (SpecFn.names_of_subset_bothArgRes
        (Signature.Subset.declVar SpecFn.Sig.relArg_subset_bothArg ⟨res, .value⟩)
        hfresh.toSpecFnFresh.subset_sigRelArg))
    (FunCtx.recursive_relWfIn_relArgRes hΓ hfresh) hsig (Signature.var_mem_declVar _ ⟨res, .value⟩)

/-- Evaluating the relational body formula in the three-symbol environment is one
unfolding of the relational body. -/
private theorem rel_body_eval_iff {R : ValRel}
    (hlaw : primitives.Lawful) (hΓ : Γ.relWfIn Δ) (hΔ : Δ.wf)
    (hfresh : EquationFresh Δ fn x res)
    (henc : encodeFormula primitives Γ Δ f fn x res e = .ok φ)
    (vin vout : Srt.value.denote) :
    φ.eval (((SpecFn.Env.both ρ fn R D F).updateConst .value x vin).updateConst .value res vout) ↔
      Relation.eval φ ρ fn x res R vin vout := by
  have hφwf := relEncodeBody_wfIn hlaw hΓ hΔ hfresh henc
  unfold Relation.eval
  exact (Formula.eval_env_agree hφwf
    (rel_agreeOn_both (D := D) (F := F) hfresh vin vout)).symm

/-- Reading the relational body at the graph of a func-form candidate gives the
graph of the func-form body operator. This is the step both fixpoint directions
turn on. -/
private theorem relEval_ofDefFunc
    (hlaw : primitives.Lawful) (hΓ : Γ.Agreement ρ) (hΓwf : Γ.wfIn Δ) (hΔ : Δ.wf)
    (hfresh : EquationFresh Δ fn x res)
    (henc : encodeDefVal primitives Γ Δ f fn x res e = .ok body)
    (hrelEnc : encodeFormula primitives Γ Δ f fn x res e = .ok φ)
    (D : Srt.value.denote → Prop) (F : Srt.value.denote → Srt.value.denote) :
    Relation.eval φ ρ fn x res (ValRel.ofDefFunc D F) =
      ValRel.ofDefFunc (Skolemize.eval ρ fn x body F D) (Skolemize.value ρ fn x body F D) := by
  obtain ⟨c, rfl, hrelEnc', hcWf⟩ := encodeDefVal_witness hlaw hΔ hfresh henc
  obtain rfl : φ = Expr.toFormula res c := by
    injection hrelEnc'.symm.trans hrelEnc with heq
    exact heq.symm
  have hΓagree : (FunCtx.recursive Γ f fn).Agreement (SpecFn.Env.graph ρ fn D F) :=
    FunCtx.Agreement.cons hΓ (hfresh.toSpecFnFresh.unused hΓwf)
  funext vin vout
  have hres := encodeDefVal_eval_updateConst_res (ρ := ρ) (D := D) (F := F)
    hlaw hΔ hΓwf.func hfresh henc vin vout
  simp only [SpecFn.Env.graphArg] at hres
  exact propext
    (((rel_body_eval_iff (R := ValRel.ofDefFunc D F) (D := D) (F := F)
        hlaw hΓwf.rel hΔ hfresh hrelEnc' vin vout).symm).trans
      ((body_eval_iff hΓwf.func hΔ hfresh hcWf hΓagree vin vout).trans
        (and_congr hres.1 (by rw [hres.2]; exact Iff.rfl))))

end Skolemize

/-! ## Soundness: the func-form definedness and value imply a relational edge -/

/-- Func-form definedness plus the func-form body value gives a relational edge.
This is the converse half of the fixpoint equivalence. -/
theorem _root_.SpecFn.Semantics.rel_sound
    (hlaw : primitives.Lawful)
    (henc : encodeDefVal primitives Γ Δ f fn x res e = .ok body)
    (hΓ : Γ.Agreement ρ) (hΓwf : Γ.wfIn Δ)
    (hΔ : Δ.wf) (hfresh : EquationFresh Δ fn x res)
    (vin vout : Srt.value.denote) :
    SpecFn.Semantics.defined primitives Γ Δ ρ f fn x res e body vin →
      body.value.eval
        ((SpecFn.Semantics.env primitives Γ Δ ρ f fn x res e body).updateConst .value x vin) =
      vout →
      SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e vin vout := by
  intro hsem hval
  obtain ⟨c, rfl, hrelEnc, _⟩ := encodeDefVal_witness hlaw hΔ hfresh henc
  have hmono := Relation.eval_mono
    (ρ := ρ) (fn := fn) (x := x) (res := res) (Expr.toFormula_mono res c)
  have hpreR : RelationFix.le
      (Relation.eval (Expr.toFormula res c) ρ fn x res
        (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e))
      (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e) := by
    rw [show SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e =
        RelationFix.lfp (Relation.eval (Expr.toFormula res c) ρ fn x res)
      from by simp [SpecFn.Semantics.rel, Relation.fixpoint, hrelEnc]]
    exact RelationFix.lfp_prefixed hmono
  -- Reading the body at the graph of a func-form candidate contained in `R` turns
  -- a func-form definedness obligation into a relational edge.
  have hstep : ∀ (P : Srt.value.denote → Prop) (vin' : Srt.value.denote),
      RelationFix.le (ValRel.ofDefFunc P (ValRel.toFunc (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e)))
        (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e) →
      Skolemize.eval ρ fn x (Expr.toDefVal .id c)
        (ValRel.toFunc (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e)) P vin' →
      SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e vin'
        (Skolemize.value ρ fn x (Expr.toDefVal .id c)
          (ValRel.toFunc (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e)) P vin') := by
    intro P vin' hle hdefBody
    refine hpreR _ _ (hmono hle _ _ ?_)
    rw [relEval_ofDefFunc hlaw hΓ hΓwf hΔ hfresh henc hrelEnc P _]
    exact ⟨hdefBody, rfl⟩
  have hdomain : PredicateFix.le (SpecFn.Semantics.defined primitives Γ Δ ρ f fn x res e (Expr.toDefVal .id c))
      (ValRel.toDef (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e)) := by
    unfold SpecFn.Semantics.defined
    apply PredicateFix.lfp_le_of_prefixed
    intro vin' hdefBody
    exact ⟨_, hstep _ vin' (ValRel.ofDefFunc_le (fun _ h => h)) hdefBody⟩
  rw [← show Skolemize.value ρ fn x (Expr.toDefVal .id c)
        (ValRel.toFunc (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e))
        (SpecFn.Semantics.defined primitives Γ Δ ρ f fn x res e (Expr.toDefVal .id c)) vin = vout
      from by simpa [Skolemize.value, SpecFn.Env.graphArg, SpecFn.Semantics.env] using hval]
  exact hstep _ vin (ValRel.ofDefFunc_le hdomain) ((SpecFn.Semantics.defined_unfold henc vin).mp hsem)

theorem _root_.SpecFn.Semantics.rel_functional
    (hlaw : primitives.Lawful)
    (henc : encodeDefVal primitives Γ Δ f fn x res e = .ok body)
    (hΔ : Δ.wf) (hΓwf : Γ.wfIn Δ) (hfresh : EquationFresh Δ fn x res)
    (hρdet : FunCtx.Functional Γ ρ ρ)
    (vin y₁ y₂ : Srt.value.denote) :
    SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e vin y₁ →
      SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e vin y₂ →
      y₁ = y₂ := by
  obtain ⟨c, hc, rfl⟩ := Except.map_eq_ok henc
  exact SpecFn.Semantics.rel_functional_of_encodeBody (primitives := primitives) hlaw hc hΓwf.rel
    hfresh.toSpecFnFresh.relFresh hfresh.toSpecFnFresh.subset_sigRelArg
    (hfresh.toSpecFnFresh.sigRelArg_wf hΔ) hfresh.resFresh_sigRelArg hρdet vin y₁ y₂

/-- If the func-form body is defined at an input, then the body value is the one
chosen from the relation. This is what the completeness direction needs when it
builds the graph of the func-form interpretation inside the relational fixpoint. -/
private theorem Skolemize.toFunc_eq
    (hlaw : primitives.Lawful)
    (henc : encodeDefVal primitives Γ Δ f fn x res e = .ok body)
    (hΓ : Γ.Agreement ρ) (hΓwf : Γ.wfIn Δ)
    (hΔ : Δ.wf) (hfresh : EquationFresh Δ fn x res)
    (hρdet : FunCtx.Functional Γ ρ ρ)
    (vin vout : Srt.value.denote) :
    SpecFn.Semantics.defined primitives Γ Δ ρ f fn x res e body vin →
      body.value.eval
        ((SpecFn.Semantics.env primitives Γ Δ ρ f fn x res e body).updateConst .value x vin) =
      vout →
      ValRel.toFunc (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e) vin = vout := by
  intro hdefined hval
  have hrelBody := SpecFn.Semantics.rel_sound hlaw henc hΓ hΓwf hΔ hfresh vin vout hdefined hval
  exact SpecFn.Semantics.rel_functional hlaw henc hΔ hΓwf hfresh hρdet vin _ vout
    (ValRel.toFunc_spec ⟨vout, hrelBody⟩) hrelBody

/-! ## Completeness: a relational edge implies func-form definedness and value -/

/-- A relational edge through the body determines the func-form definedness
predicate and the value computed by the func-form body. This is one half of the
fixpoint equivalence. -/
theorem _root_.SpecFn.Semantics.rel_complete
    (hlaw : primitives.Lawful)
    (henc : encodeDefVal primitives Γ Δ f fn x res e = .ok body)
    (hΓ : Γ.Agreement ρ) (hΓwf : Γ.wfIn Δ)
    (hΔ : Δ.wf) (hfresh : EquationFresh Δ fn x res)
    (hρdet : FunCtx.Functional Γ ρ ρ)
    (vin vout : Srt.value.denote) :
    SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e vin vout →
      SpecFn.Semantics.defined primitives Γ Δ ρ f fn x res e body vin ∧
      body.value.eval
        ((SpecFn.Semantics.env primitives Γ Δ ρ f fn x res e body).updateConst .value x vin) =
      vout := by
  intro hrel
  obtain ⟨c, rfl, hrelEnc, _⟩ := encodeDefVal_witness hlaw hΔ hfresh henc
  set D := SpecFn.Semantics.defined primitives Γ Δ ρ f fn x res e (Expr.toDefVal .id c) with hD
  set F := ValRel.toFunc (SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e) with hF
  -- The graph of the func-form presentation is a prefixed point of the relational
  -- body, so it contains the relational fixpoint.
  have hpre : RelationFix.le
      (Relation.eval (Expr.toFormula res c) ρ fn x res (ValRel.ofDefFunc D F))
      (ValRel.ofDefFunc D F) := by
    intro vin' vout' hbody
    rw [relEval_ofDefFunc hlaw hΓ hΓwf hΔ hfresh henc hrelEnc D F] at hbody
    have hdefined : D vin' := (SpecFn.Semantics.defined_unfold henc vin').mpr hbody.1
    refine ⟨hdefined, ?_⟩
    rw [← hbody.2, hF]
    exact toFunc_eq hlaw henc hΓ hΓwf hΔ hfresh hρdet vin' _ hdefined
      (by simp [Skolemize.value, SpecFn.Env.graphArg, SpecFn.Semantics.env, hD])
  have hS : ValRel.ofDefFunc D F vin vout :=
    RelationFix.lfp_le_of_prefixed hpre vin vout
      (by rw [show RelationFix.lfp
            (Relation.eval (Expr.toFormula res c) ρ fn x res) =
          SpecFn.Semantics.rel primitives Γ Δ ρ f fn x res e
        from by simp [SpecFn.Semantics.rel, Relation.fixpoint, hrelEnc]]; exact hrel)
  refine ⟨hS.1, ?_⟩
  have hval : Skolemize.value ρ fn x (Expr.toDefVal .id c) F D vin = F vin := by
    rw [hF]
    exact (toFunc_eq hlaw henc hΓ hΓwf hΔ hfresh hρdet vin _ hS.1
      (by simp [Skolemize.value, SpecFn.Env.graphArg, SpecFn.Semantics.env, hD])).symm
  simpa [Skolemize.value, SpecFn.Env.graphArg, SpecFn.Semantics.env] using hval.trans hS.2

end Verifier.RelationalEncoding
