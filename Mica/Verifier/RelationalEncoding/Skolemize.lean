-- SUMMARY: Skolemization: the defined/value encoding, its semantics, and its equivalence with the relational encoding.
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
def Mono (m : DefVal) : Prop :=
  SemanticMono (fun m ρ => m.defined.eval ρ) m

/-- A call's definedness condition is monotone in the environment's
uninterpreted predicates. -/
theorem isDefined_mono (fn : SpecFn) (arg : Term .value) {ρ ρ' : Env}
    (hle : Env.le ρ ρ') (hdef : (fn.isDefined arg).eval ρ) :
    (fn.isDefined arg).eval ρ' := by
  simp only [SpecFn.isDefined, Formula.eval, UnPred.eval] at hdef ⊢
  rw [← Term.eval_env_le hle arg]
  exact hle.2.2.2.2.1 .value (fn.defName) (arg.eval ρ) hdef

end DefVal

/-! ## From the IR to a defined/value pair -/

/-- Translate the IR into a value term paired with its definedness condition.
A call substitutes its total value function for the result name — the
substitution `σ` records what every enclosing call bound — and conjoins the
local definedness obligation. -/
def ofExpr (σ : Subst) : Expr → DefVal
  | .ret v => { value := v.subst σ, defined := .true_ }
  | .call fn arg r c =>
      let arg' := arg.subst σ
      let inner := ofExpr (σ.update .value r (fn.call arg')) c
      { value := inner.value, defined := .and (fn.isDefined arg') inner.defined }
  | .ite cond t e =>
      let cond' := cond.subst σ
      let thenVal := ofExpr σ t
      let elseVal := ofExpr σ e
      { value := .ite cond' thenVal.value elseVal.value
        defined := Formula.iteBool cond' thenVal.defined elseVal.defined }

theorem ofExpr_wfIn {Γ : FunCtx} {avoid : List String} {Δ Δσ : Signature} {c : Expr} {σ : Subst}
    (hc : Expr.WfIn Γ avoid Δ c) (hΓ : Γ.splitWfIn Δσ) (hΔσ : Δσ.wf)
    (hσ : σ.wfIn Δ.vars Δσ) (hsym : Δ.SymbolSubset Δσ) :
    (ofExpr σ c).wfIn Δσ := by
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
theorem ofExpr_wfIn_of_encode {primitives : PrimEncodings} {Γ : FunCtx}
    {Δgate Δenc : Signature} {δ : VarEnv} {s : NameSupply} {c : Expr}
    (e : Typed.Expr) (hlaw : primitives.Lawful) (hsub : Δgate.Subset Δenc)
    (hΔ : Δenc.wf) (hΓ : Γ.splitWfIn Δenc) (hδ : δ.wfIn Δenc) (hcov : s.Covers Δenc)
    (henc : encode primitives Δgate Γ δ e s = .ok c) :
    (ofExpr .id c).wfIn Δenc :=
  ofExpr_wfIn (encode_wfIn hlaw e hsub hΔ hδ hcov henc) hΓ hΔ
    (Subst.id_wfIn (fun _ h => h) hΔ) (Signature.SymbolSubset.refl _)

/-- The definedness of a split encoding is monotone in the environment's
uninterpreted predicates. -/
theorem ofExpr_mono (σ : Subst) (c : Expr) : DefVal.Mono (ofExpr σ c) := by
  induction c generalizing σ with
  | ret v => intro ρ ρ' _ hdef; simp [ofExpr, Formula.eval]
  | call fn arg r c ih =>
      intro ρ ρ' hle hdef
      simp only [ofExpr, Formula.eval] at hdef ⊢
      exact ⟨DefVal.isDefined_mono fn (arg.subst σ) hle hdef.1, ih _ hle hdef.2⟩
  | ite cond t e iht ihe =>
      intro ρ ρ' hle hdef
      simp only [ofExpr, Formula.iteBool, Formula.eval] at hdef ⊢
      refine ⟨fun hcond => iht σ hle (hdef.1 ?_), fun hcond => ihe σ hle (hdef.2 ?_)⟩ <;>
        rw [Term.eval_env_le hle] <;> exact hcond

/-! ## Body encoding -/

variable {primitives : PrimEncodings} {Γ : FunCtx} {Δ : Signature} {ρ : Env}
variable {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
variable {body : DefVal} {φ : Formula}
variable {D : Srt.value.denote → Prop} {F : Srt.value.denote → Srt.value.denote}

/-- Encode a function body using the solver-facing defined/value presentation.
It translates the very IR expression that `Relation.relEncodeBody` translates
relationally. -/
def splitBody (primitives : PrimEncodings) (Γ : FunCtx) (Δ : Signature)
    (f : TinyML.Var) (fn : SpecFn) (x res : TinyML.Var) (e : Typed.Expr) :
    Except String DefVal :=
  ofExpr .id <$> Relation.encodeBody primitives Γ Δ f fn x res e

/-- Successful split body encodings are well-formed in the split-only body
signature, so they do not depend on how the head relation is interpreted. -/
theorem splitBody_wfIn_splitBodySig
    (hlaw : primitives.Lawful) (hΔ : Δ.wf) (hΓ : Γ.splitWfIn Δ)
    (hfresh : HeadFresh Δ fn x res)
    (henc : splitBody primitives Γ Δ f fn x res e = .ok body) :
    body.wfIn (splitBodySig Δ fn x) := by
  obtain ⟨c, hc, rfl⟩ := Except.map_eq_ok henc
  have hΔbody := hfresh.toInfoFresh.splitBodySig_wf (x := x) hΔ
  exact ofExpr_wfIn_of_encode e hlaw hfresh.toInfoFresh.subset_splitBodySig hΔbody
    (ctx_splitWfIn_splitBodySig hΓ hfresh)
    (varEnv_splitBodySig (Δ := Δ) (fn := fn) (x := x) ▸ VarEnv.ofSignature_wfIn hΔbody)
    hfresh.covers_splitBodySig hc

theorem splitBody_wfIn_bodySig
    (hlaw : primitives.Lawful) (hΔ : Δ.wf) (hΓ : Γ.splitWfIn Δ)
    (hfresh : HeadFresh Δ fn x res)
    (henc : splitBody primitives Γ Δ f fn x res e = .ok body) :
    body.wfIn (bodySig Δ fn x) :=
  (splitBody_wfIn_splitBodySig hlaw hΔ hΓ hfresh henc).mono splitBodySig_subset_bodySig
    (hfresh.toInfoFresh.bodySig_wf hΔ)

/-- A successful split body encoding exposes the shared IR expression behind
it: the split body is its split reading, the relational body encoding is its
relational reading, and it is well-formed in the body signature. -/
theorem splitBody_witness
    (hlaw : primitives.Lawful) (hΔ : Δ.wf) (hfresh : HeadFresh Δ fn x res)
    (henc : splitBody primitives Γ Δ f fn x res e = .ok body) :
    ∃ c, body = ofExpr .id c ∧
      Relation.relEncodeBody primitives Γ Δ f fn x res e = .ok (Relation.ofExpr res c) ∧
      Expr.WfIn (Relation.ctx Γ f fn) (bodyAvoid fn x res) (bodySig Δ fn x) c := by
  obtain ⟨c, hc, rfl⟩ := Except.map_eq_ok henc
  have hΔrel := hfresh.toInfoFresh.relBodySig_wf (x := x) hΔ
  refine ⟨c, rfl, by simp [Relation.relEncodeBody, hc], ?_⟩
  exact ((encode_wfIn hlaw e hfresh.toInfoFresh.subset_relBodySig hΔrel
      (VarEnv.ofSignature_wfIn hΔrel) hfresh.covers_relBodySig hc).weaken
      bodyAvoid_subset_relBodySupply).mono relBodySig_subset_bodySig
      (hfresh.toInfoFresh.bodySig_wf hΔ)
      (names_of_subset_sig hfresh.bodySig_subset_sig hfresh.toInfoFresh.subset_relBodySig)

/-- Relational body encodings are well-formed in the relational run signature. -/
theorem relEncodeBody_wfIn
    (hlaw : primitives.Lawful) (hΓ : Γ.relWfIn Δ) (hΔ : Δ.wf)
    (hfresh : HeadFresh Δ fn x res)
    (henc : Relation.relEncodeBody primitives Γ Δ f fn x res e = .ok φ) :
    φ.wfIn (Relation.sig Δ fn x res) := by
  obtain ⟨c, hc, rfl⟩ := Except.map_eq_ok henc
  have hΔrel := hfresh.toInfoFresh.relBodySig_wf (x := x) hΔ
  have hsig := hfresh.relSig_wf hΔ
  have hcWf : Expr.WfIn (Relation.ctx Γ f fn) (bodyAvoid fn x res)
      (Relation.bodySig Δ fn x) c :=
    (encode_wfIn hlaw e hfresh.toInfoFresh.subset_relBodySig hΔrel
      (VarEnv.ofSignature_wfIn hΔrel) hfresh.covers_relBodySig hc).weaken
      bodyAvoid_subset_relBodySupply
  exact Relation.ofExpr_wfIn
    (hcWf.mono hfresh.relBodySig_subset_relSig hsig
      (names_of_subset_sig
        (Signature.Subset.declVar relBodySig_subset_bodySig ⟨res, .value⟩)
        hfresh.toInfoFresh.subset_relBodySig))
    (ctx_relWfIn_relSig hΓ hfresh) hsig (Signature.var_mem_declVar _ ⟨res, .value⟩)

/-! ## Relations as a definedness predicate and a value function -/

def semDefined (R : ValRel) (x : Srt.value.denote) : Prop :=
  ∃ y, R x y

/-- The value function induced by a relation: choose an arbitrary related
output when one exists, and Lean's default epsilon value otherwise. -/
noncomputable def semFunc (R : ValRel) (x : Srt.value.denote) : Srt.value.denote :=
  Classical.epsilon (R x)

/-- If the relation is defined at `x`, `semFunc` chooses a related output. -/
theorem semFunc_spec {R : ValRel} {x : Srt.value.denote}
    (h : semDefined R x) : R x (semFunc R x) := by
  unfold semDefined semFunc at *
  exact Classical.epsilon_spec h

/-- The relation presented by a definedness predicate and a value function:
the value function's graph, restricted to the definedness domain. -/
def graph (D : Srt.value.denote → Prop) (F : Srt.value.denote → Srt.value.denote) : ValRel :=
  fun a b => D a ∧ F a = b

/-- A candidate definedness predicate within the domain of `R`, paired with the
value function chosen from `R`, presents a sub-relation of `R`. -/
theorem graph_le {R : ValRel} {D : Srt.value.denote → Prop}
    (hdom : PredicateFix.le D (semDefined R)) :
    RelationFix.le (graph D (semFunc R)) R := by
  intro a b hab
  have hchosen : R a (semFunc R a) := semFunc_spec (hdom a hab.1)
  rw [hab.2] at hchosen
  exact hchosen

/-! ## Environments interpreting the head symbols -/

/-- The environment that interprets `fn`: its binary relation, its value
function, and its definedness predicate. The defined/value encoding never
mentions the relation, so its readings do not depend on `R`. -/
def splitEnv (ρ : Env) (fn : SpecFn)
    (R : ValRel) (D : Srt.value.denote → Prop)
    (F : Srt.value.denote → Srt.value.denote) : Env :=
  ((ρ.updateBinaryRel .value .value fn.relName R).updateUnary .value .value (fn.funcName) F)
    |>.updateUnaryRel .value (fn.defName) D

/-- Interpreting the triple's three fresh names leaves `Δ`-agreement intact. -/
theorem splitEnv_agreeOn {R : ValRel}
    (hrel : fn.relName ∉ Δ.allNames)
    (hfun : fn.funcName ∉ Δ.allNames)
    (hdef : fn.defName ∉ Δ.allNames) :
    Env.agreeOn Δ ρ (splitEnv ρ fn R D F) :=
  Env.agreeOn_trans
    (Env.agreeOn_update_fresh_binaryRel (b := fn.rel) (f := R) hrel)
    (Env.agreeOn_trans
      (Env.agreeOn_update_fresh_unary (u := fn.func) (f := F) hfun)
      (Env.agreeOn_update_fresh_unaryRel (u := fn.defined) (f := D) hdef))

theorem splitEnv_evalDefined (fn : SpecFn) (ρ : Env) {R : ValRel}
    (v : Srt.value.denote) :
    SpecFn.evalDefined fn (splitEnv ρ fn R D F) v ↔ D v := by
  simp [splitEnv, SpecFn.evalDefined, SpecFn.defined, SpecFn.defName,
    Env.updateUnaryRel, Env.updateUnary, Env.updateBinaryRel]

theorem splitEnv_evalCall (fn : SpecFn) (ρ : Env) {R : ValRel}
    (v : Srt.value.denote) :
    SpecFn.evalCall fn (splitEnv ρ fn R D F) v = F v := by
  simp [splitEnv, SpecFn.evalCall, SpecFn.func, SpecFn.funcName,
    Env.updateUnaryRel, Env.updateUnary, Env.updateBinaryRel]

theorem splitEnv_evalRelates (fn : SpecFn) (ρ : Env) {R : ValRel}
    (a b : Srt.value.denote) :
    SpecFn.evalRelates fn (splitEnv ρ fn R D F) a b ↔ R a b := by
  simp [splitEnv, SpecFn.evalRelates, SpecFn.rel, SpecFn.relName,
    Env.updateUnaryRel, Env.updateUnary, Env.updateBinaryRel]

/-- With graph-shaped interpretations, the interpreted environment presents
the relation as the graph of the value function on the definedness domain. -/
theorem splitEnv_graph (fn : SpecFn) (ρ : Env) {R : ValRel}
    (hgraph : ∀ a b, R a b ↔ D a ∧ F a = b) (a b : Srt.value.denote) :
    SpecFn.evalRelates fn (splitEnv ρ fn R D F) a b ↔
      SpecFn.evalDefined fn (splitEnv ρ fn R D F) a ∧
        SpecFn.evalCall fn (splitEnv ρ fn R D F) a = b := by
  simp only [splitEnv_evalRelates, splitEnv_evalDefined, splitEnv_evalCall]
  exact hgraph a b

/-- Choosing the relation up front and overwriting it afterwards give the same
environment. -/
theorem splitEnv_updateBinaryRel {R R' : ValRel} :
    (splitEnv ρ fn R D F).updateBinaryRel .value .value fn.relName R' =
      splitEnv ρ fn R' D F := by
  refine Env.ext rfl rfl rfl rfl rfl ?_
  funext τ₁ τ₂ name
  simp only [splitEnv, Env.updateBinaryRel, Env.updateUnary, Env.updateUnaryRel]
  split <;> rfl

/-- The environment of a split candidate: the head relation is read as the
graph of the candidate, which keeps the environment compatible while the split
body never consults it. -/
def graphEnv (ρ : Env) (fn : SpecFn) (D : Srt.value.denote → Prop)
    (F : Srt.value.denote → Srt.value.denote) : Env :=
  splitEnv ρ fn (graph D F) D F

/-- Environment for evaluating a split encoded body at input `vin`. -/
def defEnv (ρ : Env) (fn : SpecFn) (x : String)
    (D : Srt.value.denote → Prop)
    (F : Srt.value.denote → Srt.value.denote)
    (vin : Srt.value.denote) : Env :=
  (graphEnv ρ fn D F).updateConst .value x vin

/-- Increasing the candidate definedness predicate increases the corresponding
environments. -/
theorem graphEnv_le {D D' : Srt.value.denote → Prop} (hDD' : PredicateFix.le D D') :
    Env.le (graphEnv ρ fn D F) (graphEnv ρ fn D' F) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro τ name a h
    simp only [graphEnv, splitEnv, Env.updateUnaryRel] at h ⊢
    split at h
    · rename_i heq
      rcases heq with ⟨rfl, rfl⟩
      simpa only [Env.updateUnaryRel, dif_pos (And.intro rfl rfl)] using hDD' a h
    · rename_i hne
      simp only [dif_neg hne]
      exact h
  · intro τ₁ τ₂ name a b h
    simp only [graphEnv, splitEnv, Env.updateUnaryRel, Env.updateUnary,
      Env.updateBinaryRel] at h ⊢
    split at h
    · rename_i heq
      rcases heq with ⟨rfl, rfl, rfl⟩
      simpa only [dif_pos (And.intro rfl (And.intro rfl rfl)), graph] using
        And.imp_left (hDD' a) h
    · rename_i hne
      simp only [dif_neg hne]
      exact h

/-- Extending a split-compatible context with a fresh head function preserves
split compatibility: in `graphEnv` the head relation is a graph by construction. -/
theorem splitCompatible_cons
    (hΓ : FunCtx.splitCompatible Γ ρ) (hfresh : FunCtx.freshFn Γ fn) :
    FunCtx.splitCompatible ((f, fn) :: Γ) (graphEnv ρ fn D F) := by
  intro g fn' hmem a b
  cases hmem with
  | head => exact splitEnv_graph fn ρ (fun _ _ => Iff.rfl) a b
  | tail _ htail =>
      have hnames := hfresh g fn' htail
      simpa [SpecFn.evalRelates, SpecFn.evalDefined, SpecFn.evalCall,
        SpecFn.rel, SpecFn.defined, SpecFn.func,
        graphEnv, splitEnv, Env.updateBinaryRel, Env.updateUnary, Env.updateUnaryRel,
        hnames.1, hnames.2.1, hnames.2.2] using hΓ g fn' htail a b

/-! ## The split body operator -/

/-- The definedness a split body claims at `vin` under a recursive candidate. -/
def defBody (ρ : Env) (fn : SpecFn) (x : String) (body : DefVal)
    (F : Srt.value.denote → Srt.value.denote) :
    (Srt.value.denote → Prop) → Srt.value.denote → Prop :=
  fun D vin => body.defined.eval (defEnv ρ fn x D F vin)

/-- The value a split body computes at `vin` under a recursive candidate. -/
def valBody (ρ : Env) (fn : SpecFn) (x : String) (body : DefVal)
    (F : Srt.value.denote → Srt.value.denote) (D : Srt.value.denote → Prop)
    (vin : Srt.value.denote) : Srt.value.denote :=
  body.value.eval (defEnv ρ fn x D F vin)

/-- The definedness body operator is monotone whenever the encoded body has
monotone definedness. -/
theorem defBody_mono {x : String} (hbody : DefVal.Mono body) :
    PredicateFix.Mono (defBody ρ fn x body F) := by
  intro D D' hDD' vin hdef
  exact hbody (Env.le.updateConst (graphEnv_le (ρ := ρ) (fn := fn)
    (D := D) (D' := D') (F := F) hDD') .value x vin) hdef

/-- Semantic definedness for the split presentation: the least fixpoint of the
encoded definedness condition, interpreted with the value function chosen from
the ground-truth relation. -/
noncomputable def semdef (primitives : PrimEncodings)
    (Γ : FunCtx) (Δ : Signature) (ρ : Env)
    (f : TinyML.Var) (fn : SpecFn) (x res : TinyML.Var) (e : Typed.Expr)
    (body : DefVal) : Srt.value.denote → Prop :=
  PredicateFix.lfp (defBody ρ fn x body
    (semFunc (semrel primitives Γ Δ ρ f fn x res e)))

/-- Canonical environment for the split presentation extracted from the
ground-truth relation. -/
noncomputable def defInterpEnv (primitives : PrimEncodings)
    (Γ : FunCtx) (Δ : Signature) (ρ : Env)
    (f : TinyML.Var) (fn : SpecFn) (x res : TinyML.Var) (e : Typed.Expr)
    (body : DefVal) : Env :=
  graphEnv ρ fn (semdef primitives Γ Δ ρ f fn x res e body)
    (semFunc (semrel primitives Γ Δ ρ f fn x res e))

/-- Unfolding principle specialized to a successfully encoded `DefVal` body. -/
theorem semdef_unfold
    (henc : splitBody primitives Γ Δ f fn x res e = .ok body)
    (vin : Srt.value.denote) :
    semdef primitives Γ Δ ρ f fn x res e body vin ↔
      defBody ρ fn x body
        (semFunc (semrel primitives Γ Δ ρ f fn x res e))
        (semdef primitives Γ Δ ρ f fn x res e body) vin := by
  obtain ⟨c, _, rfl⟩ := Except.map_eq_ok henc
  exact PredicateFix.lfp_unfold (defBody_mono (ofExpr_mono _ c)) vin

/-- Under the canonical split interpretation, the definedness symbol denotes
`semdef`. -/
theorem defInterpEnv_isDefined (vin : Srt.value.denote) :
    (fn.isDefined (.var .value x)).eval
      ((defInterpEnv primitives Γ Δ ρ f fn x res e body).updateConst .value x vin)
      ↔ semdef primitives Γ Δ ρ f fn x res e body vin := by
  simp [SpecFn.isDefined, Formula.eval, UnPred.eval, Term.eval,
    Env.lookupConst_updateConst_same]
  unfold defInterpEnv graphEnv splitEnv
  simp [Env.updateConst_unaryRel, Env.updateUnaryRel]

/-- Under the canonical split interpretation, the value symbol denotes the
chosen witness function of `semrel`. -/
theorem defInterpEnv_call (vin : Srt.value.denote) :
    (fn.call (.var .value x)).eval
      ((defInterpEnv primitives Γ Δ ρ f fn x res e body).updateConst .value x vin)
      =
    semFunc (semrel primitives Γ Δ ρ f fn x res e) vin := by
  simp only [SpecFn.call, Term.eval, UnOp.eval, Env.lookupConst_updateConst_same]
  rw [Env.updateConst_unary]
  change ((ρ.updateUnary .value .value (fn.funcName)
    (semFunc (semrel primitives Γ Δ ρ f fn x res e))).unary .value .value (fn.funcName) vin =
      semFunc (semrel primitives Γ Δ ρ f fn x res e) vin)
  simp [Env.updateUnary]

/-! ## The two readings of the IR agree

Both encodings consume the same `Expr`, so their agreement is a three-case
induction on it. `Δ` grows with the names the calls bind, `ρrel` with the
witnesses the relational side picks for them, and `σ` with the value terms the
split side substituted; `SubstAgree` says the two accounts of those names
agree. -/

/-- The invariant the two encodings are compared under: the environment the
relational side reads and the one the split side reads after its substitution
give every term of `Δ` the same value. -/
def SubstAgree (Δ : Signature) (ρrel ρdef : Env) (σ : Subst) : Prop :=
  Env.agreeOnTerms Δ ρrel (σ.eval ρdef)

theorem substAgree_refl {ρ : Env} : SubstAgree Δ ρ ρ .id :=
  Env.agreeOnTerms_of_agreeOn Env.agreeOn_refl

/-- Reading a term of `Δ` on either side of `SubstAgree` gives the same value. -/
theorem eval_substAgree {Δ Δσ : Signature} {ρrel ρdef : Env} {σ : Subst}
    {τ : Srt} {t : Term τ}
    (hagree : SubstAgree Δ ρrel ρdef σ) (ht : t.wfIn Δ)
    (hσ : σ.wfIn Δ.vars Δσ) (hΔσ : Δσ.wf) :
    Term.eval ρrel t = Term.eval ρdef (t.subst σ) := by
  rw [Term.eval_subst ht hσ hΔσ]
  exact Term.eval_agreeOnTerms ht hagree

/-- Binding a call's result extends the invariant: the relational side reads the
witness it chose, the split side the value term it substituted. -/
theorem substAgree_bind {ρrel ρdef : Env} {σ : Subst} {r : String} {t : Term .value}
    (hagree : SubstAgree Δ ρrel ρdef σ) :
    SubstAgree (Δ.declVar ⟨r, .value⟩) (ρrel.updateConst .value r (Term.eval ρdef t))
      ρdef (σ.update .value r t) := by
  unfold SubstAgree
  rw [Subst.eval_update]
  exact Env.agreeOnTerms_declVar hagree

theorem ofExpr_iff {Δbase : Signature} {res : String} {ρdef : Env}
    (hΓdef : Γ.splitWfIn Δbase) (hΔbase : Δbase.wf) :
    ∀ {avoid : List String} {Δ : Signature} {c : Expr} {σ : Subst} {ρrel : Env},
      Expr.WfIn Γ avoid Δ c → res ∈ avoid →
      Δbase.Subset Δ → Δ.SymbolSubset Δbase →
      σ.wfIn Δ.vars Δbase → Γ.splitCompatible ρrel →
      Env.agreeOn Δbase ρrel ρdef → SubstAgree Δ ρrel ρdef σ →
      ρrel.lookupConst .value res = ρdef.lookupConst .value res →
      ((Relation.ofExpr res c).eval ρrel ↔
        (ofExpr σ c).defined.eval ρdef ∧
          (ofExpr σ c).value.eval ρdef = ρdef.lookupConst .value res) := by
  intro avoid Δ c σ ρrel hc hresAvoid
  induction hc generalizing σ ρrel with
  | @ret Δ v hv =>
      intro _ _ hσ _ _ hagree hres
      simp only [Relation.ofExpr, ofExpr, Formula.eval, Term.eval, true_and]
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
        (FunCtx.splitCompatible_updateConst hΓc .value r _)
        (Env.agreeOn_trans
          (Env.agreeOn_symm
            (Env.agreeOn_update_fresh_const (c := ⟨r, .value⟩) hfreshBase)) hagBase)
        (substAgree_bind hagree)
        (by rw [Env.lookupConst_updateConst_ne hres_ne]; exact hres)
      simp only [Relation.ofExpr, ofExpr, Formula.eval]
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
      simp only [Relation.ofExpr, ofExpr, Formula.iteBool, Formula.eval, Term.eval,
        Const.denote]
      cases hcv : Term.eval ρrel cond with
      | false =>
          have hc2 : Term.eval ρdef (cond.subst σ) = false := by rw [← hcondEval]; exact hcv
          simp [hc2, he]
      | true =>
          have hc2 : Term.eval ρdef (cond.subst σ) = true := by rw [← hcondEval]; exact hcv
          simp [hc2, ht]

/-- At a split-compatible environment the two readings of one body agree: the
relational formula holds at `vout` exactly when the split body is defined and
evaluates to `vout`. -/
theorem body_eval_iff {ρsplit : Env} {c : Expr}
    (hΓdef : Γ.splitWfIn Δ) (hΔ : Δ.wf) (hfresh : HeadFresh Δ fn x res)
    (hcWf : Expr.WfIn (Relation.ctx Γ f fn) (bodyAvoid fn x res) (bodySig Δ fn x) c)
    (hΓsplit : (Relation.ctx Γ f fn).splitCompatible ρsplit)
    (vin vout : Srt.value.denote) :
    (Relation.ofExpr res c).eval
        ((ρsplit.updateConst .value x vin).updateConst .value res vout) ↔
      ((ofExpr .id c).defined.eval
          ((ρsplit.updateConst .value x vin).updateConst .value res vout) ∧
        (ofExpr .id c).value.eval
          ((ρsplit.updateConst .value x vin).updateConst .value res vout) = vout) := by
  have hΔbody := hfresh.toInfoFresh.bodySig_wf (x := x) hΔ
  have h := ofExpr_iff (res := res) (ctx_splitWfIn_bodySig hΓdef hfresh) hΔbody
    hcWf (by simp [bodyAvoid]) (Signature.Subset.refl _) (Signature.SymbolSubset.refl _)
    (Subst.id_wfIn (fun _ h => h) hΔbody)
    (FunCtx.splitCompatible_updateConst
      (FunCtx.splitCompatible_updateConst hΓsplit .value x vin) .value res vout)
    Env.agreeOn_refl substAgree_refl rfl
  simpa [Env.lookupConst_updateConst_same] using h

/-- The split body never mentions the result variable, so pinning `res` does not
change what it reads. -/
theorem splitBody_eval_updateConst_res
    (hlaw : primitives.Lawful) (hΔ : Δ.wf) (hΓ : Γ.splitWfIn Δ)
    (hfresh : HeadFresh Δ fn x res)
    (henc : splitBody primitives Γ Δ f fn x res e = .ok body)
    (vin vout : Srt.value.denote) :
    (body.defined.eval ((defEnv ρ fn x D F vin).updateConst .value res vout) ↔
        body.defined.eval (defEnv ρ fn x D F vin)) ∧
      body.value.eval ((defEnv ρ fn x D F vin).updateConst .value res vout) =
        body.value.eval (defEnv ρ fn x D F vin) := by
  have hbody : body.wfIn (bodySig Δ fn x) := splitBody_wfIn_bodySig hlaw hΔ hΓ hfresh henc
  have hag : Env.agreeOn (bodySig Δ fn x) (defEnv ρ fn x D F vin)
      ((defEnv ρ fn x D F vin).updateConst .value res vout) :=
    Env.agreeOn_update_fresh_const (c := ⟨res, .value⟩) hfresh.resFresh_bodySig
  exact ⟨(Formula.eval_env_agree hbody.2 hag).symm, (Term.eval_env_agree hbody.1 hag).symm⟩

/-- The relational run environment and the split environment pinned at `x` and
`res` agree on everything the relational body can read. -/
theorem relEnv_agreeOn_splitEnv {R : ValRel}
    (hfresh : HeadFresh Δ fn x res) (vin vout : Srt.value.denote) :
    Env.agreeOn (Relation.sig Δ fn x res)
      (Relation.relEnv ρ fn x res R vin vout)
      (((splitEnv ρ fn R D F).updateConst .value x vin).updateConst .value res vout) := by
  have hdefFresh : fn.defName ∉ (relBase Δ fn).allNames :=
    Signature.not_mem_allNames_addBinaryRel hfresh.toInfoFresh.defFresh
      (SpecFn.defName_ne_relName fn)
  have hbase : Env.agreeOn (relBase Δ fn)
      (ρ.updateBinaryRel .value .value fn.relName R) (splitEnv ρ fn R D F) :=
    Env.agreeOn_trans
      (Env.agreeOn_update_fresh_unary (u := fn.func) (f := F)
        (Signature.not_mem_allNames_addBinaryRel hfresh.toInfoFresh.funcFresh
          (SpecFn.funcName_ne_relName fn)))
      (Env.agreeOn_update_fresh_unaryRel (u := fn.defined) (f := D) hdefFresh)
  exact Env.agreeOn_declVar (Env.agreeOn_declVar hbase)

/-- Evaluating the relational body formula in the split environment is the
abstract semantic body operator. -/
theorem rel_body_eval_iff {R : ValRel}
    (hlaw : primitives.Lawful) (hΓ : Γ.relWfIn Δ) (hΔ : Δ.wf)
    (hfresh : HeadFresh Δ fn x res)
    (henc : relEncodeBody primitives Γ Δ f fn x res e = .ok φ)
    (vin vout : Srt.value.denote) :
    φ.eval (((splitEnv ρ fn R D F).updateConst .value x vin).updateConst .value res vout) ↔
      Relation.semanticBody Formula.sem ρ fn x res φ R vin vout := by
  have hφwf := relEncodeBody_wfIn hlaw hΓ hΔ hfresh henc
  unfold Relation.semanticBody Formula.sem
  exact (Formula.eval_env_agree hφwf
    (relEnv_agreeOn_splitEnv (D := D) (F := F) hfresh vin vout)).symm

/-- Reading the relational body at the graph of a split candidate gives the
graph of the split body operator. This is the step both fixpoint directions
turn on. -/
theorem semanticBody_graph
    (hlaw : primitives.Lawful) (hΓ : Γ.splitCompatible ρ) (hΓwf : Γ.wfIn Δ) (hΔ : Δ.wf)
    (hfresh : HeadFresh Δ fn x res)
    (henc : splitBody primitives Γ Δ f fn x res e = .ok body)
    (hrelEnc : relEncodeBody primitives Γ Δ f fn x res e = .ok φ)
    (D : Srt.value.denote → Prop) (F : Srt.value.denote → Srt.value.denote) :
    Relation.semanticBody Formula.sem ρ fn x res φ (graph D F) =
      graph (defBody ρ fn x body F D) (valBody ρ fn x body F D) := by
  obtain ⟨c, rfl, hrelEnc', hcWf⟩ := splitBody_witness hlaw hΔ hfresh henc
  obtain rfl : φ = Relation.ofExpr res c := by
    injection hrelEnc'.symm.trans hrelEnc with heq
    exact heq.symm
  have hΓsplit : (Relation.ctx Γ f fn).splitCompatible (graphEnv ρ fn D F) :=
    splitCompatible_cons hΓ (hfresh.toInfoFresh.freshFn hΓwf)
  funext vin vout
  have hres := splitBody_eval_updateConst_res (ρ := ρ) (D := D) (F := F)
    hlaw hΔ hΓwf.split hfresh henc vin vout
  simp only [defEnv] at hres
  exact propext
    (((rel_body_eval_iff (R := graph D F) (D := D) (F := F)
        hlaw hΓwf.rel hΔ hfresh hrelEnc' vin vout).symm).trans
      ((body_eval_iff hΓwf.split hΔ hfresh hcWf hΓsplit vin vout).trans
        (and_congr hres.1 (by rw [hres.2]; exact Iff.rfl))))

/-! ## Soundness: split definedness and value imply the relational encoding -/

/-- Split definedness plus the split body value gives a relational edge. This
is the converse half of the relation/split fixpoint equivalence. -/
theorem semrel_sound
    (hlaw : primitives.Lawful)
    (henc : splitBody primitives Γ Δ f fn x res e = .ok body)
    (hΓ : Γ.splitCompatible ρ) (hΓwf : Γ.wfIn Δ)
    (hΔ : Δ.wf) (hfresh : HeadFresh Δ fn x res)
    (vin vout : Srt.value.denote) :
    semdef primitives Γ Δ ρ f fn x res e body vin →
      body.value.eval
        ((defInterpEnv primitives Γ Δ ρ f fn x res e body).updateConst .value x vin) =
      vout →
      semrel primitives Γ Δ ρ f fn x res e vin vout := by
  intro hsem hval
  obtain ⟨c, rfl, hrelEnc, _⟩ := splitBody_witness hlaw hΔ hfresh henc
  have hmono := Relation.semanticBody_mono_of_semanticMono
    (ρ := ρ) (fn := fn) (x := x) (res := res) (Relation.ofExpr_mono res c)
  have hpreR : RelationFix.le
      (Relation.semanticBody Formula.sem ρ fn x res (Relation.ofExpr res c)
        (semrel primitives Γ Δ ρ f fn x res e))
      (semrel primitives Γ Δ ρ f fn x res e) := by
    rw [show semrel primitives Γ Δ ρ f fn x res e =
        RelationFix.lfp (Relation.semanticBody Formula.sem ρ fn x res (Relation.ofExpr res c))
      from by simp [Relation.semrel, Relation.semanticFixpoint, hrelEnc]]
    exact RelationFix.lfp_prefixed hmono
  -- Reading the body at the graph of a split candidate contained in `R` turns a
  -- split definedness obligation into a relational edge.
  have hstep : ∀ (P : Srt.value.denote → Prop) (vin' : Srt.value.denote),
      RelationFix.le (graph P (semFunc (semrel primitives Γ Δ ρ f fn x res e)))
        (semrel primitives Γ Δ ρ f fn x res e) →
      defBody ρ fn x (ofExpr .id c)
        (semFunc (semrel primitives Γ Δ ρ f fn x res e)) P vin' →
      semrel primitives Γ Δ ρ f fn x res e vin'
        (valBody ρ fn x (ofExpr .id c)
          (semFunc (semrel primitives Γ Δ ρ f fn x res e)) P vin') := by
    intro P vin' hle hdefBody
    refine hpreR _ _ (hmono hle _ _ ?_)
    rw [semanticBody_graph hlaw hΓ hΓwf hΔ hfresh henc hrelEnc P _]
    exact ⟨hdefBody, rfl⟩
  have hdomain : PredicateFix.le (semdef primitives Γ Δ ρ f fn x res e (ofExpr .id c))
      (semDefined (semrel primitives Γ Δ ρ f fn x res e)) := by
    unfold semdef
    apply PredicateFix.lfp_le_of_prefixed
    intro vin' hdefBody
    exact ⟨_, hstep _ vin' (graph_le (fun _ h => h)) hdefBody⟩
  rw [← show valBody ρ fn x (ofExpr .id c)
        (semFunc (semrel primitives Γ Δ ρ f fn x res e))
        (semdef primitives Γ Δ ρ f fn x res e (ofExpr .id c)) vin = vout
      from by simpa [valBody, defEnv, defInterpEnv] using hval]
  exact hstep _ vin (graph_le hdomain) ((semdef_unfold henc vin).mp hsem)

theorem semrel_functional
    (hlaw : primitives.Lawful)
    (henc : splitBody primitives Γ Δ f fn x res e = .ok body)
    (hΔ : Δ.wf) (hΓwf : Γ.wfIn Δ) (hfresh : HeadFresh Δ fn x res)
    (hρdet : Relation.BinaryRelDet Γ ρ ρ)
    (vin y₁ y₂ : Srt.value.denote) :
    semrel primitives Γ Δ ρ f fn x res e vin y₁ →
      semrel primitives Γ Δ ρ f fn x res e vin y₂ →
      y₁ = y₂ := by
  obtain ⟨c, hc, rfl⟩ := Except.map_eq_ok henc
  exact Relation.semrel_functional (primitives := primitives) hlaw hc hΓwf.rel
    hfresh.toInfoFresh.relFresh hfresh.toInfoFresh.subset_relBodySig
    (hfresh.toInfoFresh.relBodySig_wf hΔ) hfresh.resFresh_relBodySig hρdet vin y₁ y₂

/-- If the split body is defined at an input, then the body value is the
canonical value chosen from the relational semantics. This is what the
completeness direction needs when it builds the graph of the split
interpretation inside the relational fixpoint. -/
theorem semFunc_eq
    (hlaw : primitives.Lawful)
    (henc : splitBody primitives Γ Δ f fn x res e = .ok body)
    (hΓ : Γ.splitCompatible ρ) (hΓwf : Γ.wfIn Δ)
    (hΔ : Δ.wf) (hfresh : HeadFresh Δ fn x res)
    (hρdet : Relation.BinaryRelDet Γ ρ ρ)
    (vin vout : Srt.value.denote) :
    semdef primitives Γ Δ ρ f fn x res e body vin →
      body.value.eval
        ((defInterpEnv primitives Γ Δ ρ f fn x res e body).updateConst .value x vin) =
      vout →
      semFunc (semrel primitives Γ Δ ρ f fn x res e) vin = vout := by
  intro hdefined hval
  have hrelBody := semrel_sound hlaw henc hΓ hΓwf hΔ hfresh vin vout hdefined hval
  exact semrel_functional hlaw henc hΔ hΓwf hfresh hρdet vin _ vout
    (semFunc_spec ⟨vout, hrelBody⟩) hrelBody

/-! ## Completeness: the relational encoding implies split definedness and value -/

/-- A relational edge through the semantic body determines the split
definedness predicate and the value computed by the split body. This is one
half of the relation/split fixpoint equivalence. -/
theorem semrel_complete
    (hlaw : primitives.Lawful)
    (henc : splitBody primitives Γ Δ f fn x res e = .ok body)
    (hΓ : Γ.splitCompatible ρ) (hΓwf : Γ.wfIn Δ)
    (hΔ : Δ.wf) (hfresh : HeadFresh Δ fn x res)
    (hρdet : Relation.BinaryRelDet Γ ρ ρ)
    (vin vout : Srt.value.denote) :
    semrel primitives Γ Δ ρ f fn x res e vin vout →
      semdef primitives Γ Δ ρ f fn x res e body vin ∧
      body.value.eval
        ((defInterpEnv primitives Γ Δ ρ f fn x res e body).updateConst .value x vin) =
      vout := by
  intro hrel
  obtain ⟨c, rfl, hrelEnc, _⟩ := splitBody_witness hlaw hΔ hfresh henc
  set D := semdef primitives Γ Δ ρ f fn x res e (ofExpr .id c) with hD
  set F := semFunc (semrel primitives Γ Δ ρ f fn x res e) with hF
  -- The graph of the split presentation is a prefixed point of the relational
  -- body, so it contains the relational fixpoint.
  have hpre : RelationFix.le
      (Relation.semanticBody Formula.sem ρ fn x res (Relation.ofExpr res c) (graph D F))
      (graph D F) := by
    intro vin' vout' hbody
    rw [semanticBody_graph hlaw hΓ hΓwf hΔ hfresh henc hrelEnc D F] at hbody
    have hdefined : D vin' := (semdef_unfold henc vin').mpr hbody.1
    refine ⟨hdefined, ?_⟩
    rw [← hbody.2, hF]
    exact semFunc_eq hlaw henc hΓ hΓwf hΔ hfresh hρdet vin' _ hdefined
      (by simp [valBody, defEnv, defInterpEnv, hD])
  have hS : graph D F vin vout :=
    RelationFix.lfp_le_of_prefixed hpre vin vout
      (by rw [show RelationFix.lfp
            (Relation.semanticBody Formula.sem ρ fn x res (Relation.ofExpr res c)) =
          semrel primitives Γ Δ ρ f fn x res e
        from by simp [Relation.semrel, Relation.semanticFixpoint, hrelEnc]]; exact hrel)
  refine ⟨hS.1, ?_⟩
  have hval : valBody ρ fn x (ofExpr .id c) F D vin = F vin := by
    rw [hF]
    exact (semFunc_eq hlaw henc hΓ hΓwf hΔ hfresh hρdet vin _ hS.1
      (by simp [valBody, defEnv, defInterpEnv, hD])).symm
  simpa [valBody, defEnv, defInterpEnv] using hval.trans hS.2

end Skolemize
end Verifier.RelationalEncoding
