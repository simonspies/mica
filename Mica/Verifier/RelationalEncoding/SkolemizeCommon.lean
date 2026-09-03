-- SUMMARY: Shared split encoding, semantic infrastructure, and the agreement of the relational and defined/value readings.
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

/-- Defined/value encoding of a pure typed TinyML expression for SMT emission.
Calls are encoded using total value functions and separate definedness
predicates, so this encoding introduces no existential witnesses. -/
def split (primitives : PrimEncodings) (Γ : FunCtx) (Δ : Signature) (e : Typed.Expr) :
    Except String DefVal :=
  ofExpr .id <$> encode primitives Δ Γ (VarEnv.ofSignature Δ) e (NameSupply.ofSignature Δ)

/-! ## Well-formedness of `split` -/

namespace DefVal

/-- A defined/value encoding is well-formed when both its value term and its
definedness formula are well-formed. -/
def wfIn (m : DefVal) (Δ : Signature) : Prop :=
  m.value.wfIn Δ ∧ m.defined.wfIn Δ

end DefVal

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

/-- The invariant the two encodings are compared under: the environment the
relational side reads and the one the split side reads after its substitution
give every term of `Δ` the same value. -/
def SubstAgree (Δ : Signature) (ρrel ρdef : Env) (σ : Subst) : Prop :=
  Env.agreeOnTerms Δ ρrel (σ.eval ρdef)

theorem substAgree_refl {Δ : Signature} {ρ : Env} : SubstAgree Δ ρ ρ .id :=
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
theorem substAgree_bind {Δ : Signature} {ρrel ρdef : Env} {σ : Subst}
    {r : String} {t : Term .value}
    (hagree : SubstAgree Δ ρrel ρdef σ) :
    SubstAgree (Δ.declVar ⟨r, .value⟩) (ρrel.updateConst .value r (Term.eval ρdef t))
      ρdef (σ.update .value r t) := by
  unfold SubstAgree
  rw [Subst.eval_update]
  exact Env.agreeOnTerms_declVar hagree

/-- Well-formedness of a split encoding whose traversal gate signature `Δgate`
may differ from the signature `Δenc` the local environment lives in (the two
coincide for `split`, but the body encodings gate on the outer signature while
encoding into a body signature). -/
theorem split_wfIn_of_gate {primitives : PrimEncodings} {Γ : FunCtx}
    {Δgate Δenc : Signature} {δ : VarEnv} {s : NameSupply} {c : Expr}
    (e : Typed.Expr) (hlaw : primitives.Lawful) (hsub : Δgate.Subset Δenc)
    (hΔ : Δenc.wf) (hΓ : Γ.splitWfIn Δenc) (hδ : δ.wfIn Δenc) (hcov : s.Covers Δenc)
    (henc : encode primitives Δgate Γ δ e s = .ok c) :
    (ofExpr .id c).wfIn Δenc :=
  ofExpr_wfIn (encode_wfIn hlaw e hsub hΔ hδ hcov henc) hΓ hΔ
    (Subst.id_wfIn (fun _ h => h) hΔ) (Signature.SymbolSubset.refl _)

/-- Well-formedness of the solver-facing defined/value encoding. -/
theorem split_wfIn {primitives : PrimEncodings} {Γ : FunCtx} {Δ : Signature} (e : Typed.Expr)
    {m : DefVal} (hlaw : primitives.Lawful) (hΔ : Δ.wf) (hΓ : Γ.splitWfIn Δ)
    (henc : split primitives Γ Δ e = .ok m) : m.wfIn Δ := by
  obtain ⟨c, hc, rfl⟩ := Except.map_eq_ok henc
  exact split_wfIn_of_gate e hlaw (Signature.Subset.refl _) hΔ hΓ
    (VarEnv.ofSignature_wfIn hΔ) (NameSupply.ofSignature_covers Δ) hc

/-! ## Monotonicity of `split` definedness -/

namespace DefVal

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


/-! ## Body Encoding -/

/-- Encode a function body using the solver-facing defined/value presentation.
It translates the very IR expression that `Relation.relEncodeBody` translates
relationally. -/
def splitBody (primitives : PrimEncodings) (Γ : FunCtx) (Δ : Signature)
    (f : TinyML.Var) (fn : SpecFn) (x res : TinyML.Var) (e : Typed.Expr) :
    Except String DefVal :=
  ofExpr .id <$> Relation.encodeBody primitives Γ Δ f fn x res e

/-! ## Semantic Infrastructure -/
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

/-- The environment that interprets `fn`: its binary relation, its value
function, and its definedness predicate. The defined/value encoding never
mentions the relation, so its readings do not depend on `R`. -/
def splitEnv (ρ : Env) (fn : SpecFn)
    (R : ValRel) (D : Srt.value.denote → Prop)
    (F : Srt.value.denote → Srt.value.denote) : Env :=
  ((ρ.updateBinaryRel .value .value fn.relName R).updateUnary .value .value (fn.funcName) F)
    |>.updateUnaryRel .value (fn.defName) D

/-- Interpreting the triple's three fresh names leaves `Δ`-agreement intact. -/
theorem splitEnv_agreeOn {Δ : Signature} {fn : SpecFn} {ρ : Env}
    {R : Srt.value.denote → Srt.value.denote → Prop}
    {D : Srt.value.denote → Prop} {F : Srt.value.denote → Srt.value.denote}
    (hrel : fn.relName ∉ Δ.allNames)
    (hfun : fn.funcName ∉ Δ.allNames)
    (hdef : fn.defName ∉ Δ.allNames) :
    Env.agreeOn Δ ρ (splitEnv ρ fn R D F) :=
  Env.agreeOn_trans
    (Env.agreeOn_update_fresh_binaryRel (b := fn.rel) (f := R) hrel)
    (Env.agreeOn_trans
      (Env.agreeOn_update_fresh_unary (u := fn.func) (f := F) hfun)
      (Env.agreeOn_update_fresh_unaryRel (u := fn.defined) (f := D) hdef))

theorem splitEnv_evalDefined (fn : SpecFn) (ρ : Env)
    {R : Srt.value.denote → Srt.value.denote → Prop}
    {D : Srt.value.denote → Prop} {F : Srt.value.denote → Srt.value.denote}
    (v : Srt.value.denote) :
    SpecFn.evalDefined fn (splitEnv ρ fn R D F) v ↔ D v := by
  simp [splitEnv, SpecFn.evalDefined, SpecFn.defined, SpecFn.defName,
    Env.updateUnaryRel, Env.updateUnary, Env.updateBinaryRel]

theorem splitEnv_evalCall (fn : SpecFn) (ρ : Env)
    {R : Srt.value.denote → Srt.value.denote → Prop}
    {D : Srt.value.denote → Prop} {F : Srt.value.denote → Srt.value.denote}
    (v : Srt.value.denote) :
    SpecFn.evalCall fn (splitEnv ρ fn R D F) v = F v := by
  simp [splitEnv, SpecFn.evalCall, SpecFn.func, SpecFn.funcName,
    Env.updateUnaryRel, Env.updateUnary, Env.updateBinaryRel]

theorem splitEnv_evalRelates (fn : SpecFn) (ρ : Env)
    {R : Srt.value.denote → Srt.value.denote → Prop}
    {D : Srt.value.denote → Prop} {F : Srt.value.denote → Srt.value.denote}
    (a b : Srt.value.denote) :
    SpecFn.evalRelates fn (splitEnv ρ fn R D F) a b ↔ R a b := by
  simp [splitEnv, SpecFn.evalRelates, SpecFn.rel, SpecFn.relName,
    Env.updateUnaryRel, Env.updateUnary, Env.updateBinaryRel]

/-- With graph-shaped interpretations, the interpreted environment presents
the relation as the graph of the value function on the definedness domain. -/
theorem splitEnv_graph (fn : SpecFn) (ρ : Env)
    {R : Srt.value.denote → Srt.value.denote → Prop}
    {D : Srt.value.denote → Prop} {F : Srt.value.denote → Srt.value.denote}
    (hgraph : ∀ a b, R a b ↔ D a ∧ F a = b) (a b : Srt.value.denote) :
    SpecFn.evalRelates fn (splitEnv ρ fn R D F) a b ↔
      SpecFn.evalDefined fn (splitEnv ρ fn R D F) a ∧
        SpecFn.evalCall fn (splitEnv ρ fn R D F) a = b := by
  simp only [splitEnv_evalRelates, splitEnv_evalDefined, splitEnv_evalCall]
  exact hgraph a b

/-- Environment for evaluating a split encoded body at input `vin`, with
recursive calls interpreted by `D` and `F`. The relation is read as their
graph, which keeps the environment compatible; the body never consults it. -/
def defEnv (ρ : Env) (fn : SpecFn) (x : String)
    (D : Srt.value.denote → Prop)
    (F : Srt.value.denote → Srt.value.denote)
    (vin : Srt.value.denote) : Env :=
  (splitEnv ρ fn (graph D F) D F).updateConst .value x vin

/-- Increasing the candidate definedness predicate increases the corresponding
environments. -/
theorem splitEnv_le {ρ : Env} {fn : SpecFn}
    {D D' : Srt.value.denote → Prop}
    {F : Srt.value.denote → Srt.value.denote}
    (hDD' : PredicateFix.le D D') :
    Env.le (splitEnv ρ fn (graph D F) D F) (splitEnv ρ fn (graph D' F) D' F) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro τ name a h
    simp only [splitEnv, Env.updateUnaryRel] at h ⊢
    split at h
    · rename_i heq
      rcases heq with ⟨rfl, rfl⟩
      simpa only [Env.updateUnaryRel, dif_pos (And.intro rfl rfl)] using hDD' a h
    · rename_i hne
      simp only [dif_neg hne]
      exact h
  · intro τ₁ τ₂ name a b h
    simp only [splitEnv, Env.updateUnaryRel, Env.updateUnary, Env.updateBinaryRel] at h ⊢
    split at h
    · rename_i heq
      rcases heq with ⟨rfl, rfl, rfl⟩
      simpa only [dif_pos (And.intro rfl (And.intro rfl rfl)), graph] using
        And.imp_left (hDD' a) h
    · rename_i hne
      simp only [dif_neg hne]
      exact h

/-- Choosing the relation up front and overwriting it afterwards give the same
environment. -/
theorem splitEnv_updateBinaryRel {ρ : Env} {fn : SpecFn} {R R' : ValRel}
    {D : Srt.value.denote → Prop} {F : Srt.value.denote → Srt.value.denote} :
    (splitEnv ρ fn R D F).updateBinaryRel .value .value fn.relName R' =
      splitEnv ρ fn R' D F := by
  refine Env.ext rfl rfl rfl rfl rfl ?_
  funext τ₁ τ₂ name
  simp only [splitEnv, Env.updateBinaryRel, Env.updateUnary, Env.updateUnaryRel]
  split <;> rfl

/-- The unary body operator induced by the definedness component of a
`DefVal` body under a fixed recursive value function. -/
def defBody (ρ : Env) (fn : SpecFn) (x : String) (body : DefVal)
    (F : Srt.value.denote → Srt.value.denote) :
    (Srt.value.denote → Prop) → Srt.value.denote → Prop :=
  fun D vin => body.defined.eval (defEnv ρ fn x D F vin)

/-- The definedness body operator is monotone whenever the encoded body has
monotone definedness. -/
theorem defBody_mono {ρ : Env} {fn : SpecFn} {x : String} {body : DefVal}
    {F : Srt.value.denote → Srt.value.denote}
    (hbody : DefVal.Mono body) :
    PredicateFix.Mono (defBody ρ fn x body F) := by
  intro D D' hDD' vin hdef
  exact hbody (Env.le.updateConst (splitEnv_le (ρ := ρ) (fn := fn)
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
  let R := semrel primitives Γ Δ ρ f fn x res e
  let D := semdef primitives Γ Δ ρ f fn x res e body
  splitEnv ρ fn (graph D (semFunc R)) D (semFunc R)

/-- Unfolding principle specialized to a successfully encoded `DefVal` body. -/
theorem semdef_unfold_of_split {primitives : PrimEncodings}
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (henc : splitBody primitives Γ Δ f fn x res e = .ok body)
    (vin : Srt.value.denote) :
    semdef primitives Γ Δ ρ f fn x res e body vin ↔
      defBody ρ fn x body
        (semFunc (semrel primitives Γ Δ ρ f fn x res e))
        (semdef primitives Γ Δ ρ f fn x res e body) vin := by
  obtain ⟨c, _, rfl⟩ := Except.map_eq_ok henc
  exact PredicateFix.lfp_unfold (defBody_mono (ofExpr_mono _ c)) vin

/-- Under the canonical split interpretation, the definedness symbol denotes
`semdef`. -/
theorem definedCall_eval_defInterpEnv {primitives : PrimEncodings}
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (vin : Srt.value.denote) :
    (fn.isDefined (.var .value x)).eval
      ((defInterpEnv primitives Γ Δ ρ f fn x res e body).updateConst .value x vin)
      ↔ semdef primitives Γ Δ ρ f fn x res e body vin := by
  simp [SpecFn.isDefined, SpecFn.isDefined, Formula.eval, UnPred.eval, Term.eval,
    Env.lookupConst_updateConst_same]
  unfold defInterpEnv splitEnv
  simp [Env.updateConst_unaryRel, Env.updateUnaryRel]

/-- Under the canonical split interpretation, the value symbol denotes the
chosen witness function of `semrel`. -/
theorem valueCall_eval_defInterpEnv {primitives : PrimEncodings}
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (vin : Srt.value.denote) :
    (fn.call (.var .value x)).eval
      ((defInterpEnv primitives Γ Δ ρ f fn x res e body).updateConst .value x vin)
      =
    semFunc (semrel primitives Γ Δ ρ f fn x res e) vin := by
  simp only [SpecFn.call, SpecFn.call, Term.eval, UnOp.eval, Env.lookupConst_updateConst_same]
  rw [Env.updateConst_unary]
  change ((ρ.updateUnary .value .value (fn.funcName)
    (semFunc (semrel primitives Γ Δ ρ f fn x res e))).unary .value .value (fn.funcName) vin =
      semFunc (semrel primitives Γ Δ ρ f fn x res e) vin)
  simp [Env.updateUnary]


end Skolemize

/-! ## Split Compatibility -/
/-- A binary relational interpretation and the split defined/value symbols
agree for every relation-marked function in the context. -/
def FunCtx.splitCompatible (Γ : FunCtx) (ρ : Env) : Prop :=
  ∀ f fn, (f, fn) ∈ Γ →
    ∀ x y, fn.evalRelates ρ x y ↔ fn.evalDefined ρ x ∧ fn.evalCall ρ x = y

theorem FunCtx.splitCompatible_updateConst {Γ : FunCtx} {ρ : Env}
    (hΓ : Γ.splitCompatible ρ) (τ : Srt) (x : String) (v : τ.denote) :
    Γ.splitCompatible (ρ.updateConst τ x v) := by
  intro f fn hmem a b
  simpa [Env.updateConst_unary, Env.updateConst_unaryRel, Env.updateConst_binaryRel]
    using hΓ f fn hmem a b

/-- The newly introduced relation and split symbols do not collide with the
relation names already present in the tail function context. -/
def FunCtx.freshFn (Γ : FunCtx) (fn : SpecFn) : Prop :=
  ∀ g fn', (g, fn') ∈ Γ →
    fn'.relName ≠ fn.relName ∧ fn'.funcName ≠ fn.funcName ∧ fn'.defName ≠ fn.defName

namespace Skolemize

/-- Extending a split-compatible context with a fresh head function preserves
split compatibility, provided the head relation is the graph of the chosen
definedness predicate and value function. -/
theorem splitCompatible_cons_splitEnv
    {Γ : FunCtx} {ρ : Env} {f : TinyML.Var} {fn : SpecFn}
    {D : Srt.value.denote → Prop} {F : Srt.value.denote → Srt.value.denote}
    (hΓ : FunCtx.splitCompatible Γ ρ) (hfresh : FunCtx.freshFn Γ fn) :
    FunCtx.splitCompatible ((f, fn) :: Γ) (splitEnv ρ fn (graph D F) D F) := by
  intro g fn' hmem x y
  cases hmem with
  | head => exact splitEnv_graph fn ρ (fun _ _ => Iff.rfl) x y
  | tail _ htail =>
      have hnames := hfresh g fn' htail
      simpa [SpecFn.evalRelates, SpecFn.evalDefined, SpecFn.evalCall,
        SpecFn.rel, SpecFn.defined, SpecFn.func,
        splitEnv, Env.updateBinaryRel, Env.updateUnary, Env.updateUnaryRel,
        hnames.1, hnames.2.1, hnames.2.2] using hΓ g fn' htail x y

/-! ### Body-signature transport helpers -/

/-- The body signatures declare the same value variables, so they induce the
same encoder environment. -/
theorem varEnv_defvalBodySig {Δ : Signature} {fn : SpecFn} {x : TinyML.Var} :
    VarEnv.ofSignature (Relation.bodySig Δ fn x) =
      VarEnv.ofSignature (defvalBodySig Δ fn x) := by
  simp [VarEnv.ofSignature, Relation.bodySig, defvalBodySig, Signature.declVar,
    Signature.addBinaryRel, Signature.addUnary, Signature.addUnaryRel,
    Signature.remove, Signature.addVar]

theorem varEnv_bodySig {Δ : Signature} {fn : SpecFn} {x : TinyML.Var} :
    VarEnv.ofSignature (Relation.bodySig Δ fn x) = VarEnv.ofSignature (bodySig Δ fn x) := by
  simp [VarEnv.ofSignature, Relation.bodySig, bodySig, Signature.declVar,
    Signature.addBinaryRel, Signature.addUnary, Signature.addUnaryRel,
    Signature.remove, Signature.addVar]

/-! ### Freshness and signature infrastructure -/

/-- Freshness assumptions for the common Skolemization signature, in the exact
order in which `sig` introduces the head relation symbols and bound variables. -/
structure HeadFresh (Δ : Signature) (fn : SpecFn) (x res : String) : Prop where
  relFresh : fn.relName ∉ Δ.allNames
  funFresh :
    fn.funcName ∉ (Δ.addBinaryRel fn.rel).allNames
  defFresh :
    fn.defName ∉
    ((Δ.addBinaryRel fn.rel).addUnary fn.func).allNames
  argFresh :
    x ∉
    (((Δ.addBinaryRel fn.rel).addUnary fn.func).addUnaryRel
      (fn.defined)).allNames
  resFresh :
    res ∉
    ((((Δ.addBinaryRel fn.rel).addUnary fn.func).addUnaryRel
      (fn.defined)).declVar ⟨x, .value⟩).allNames

/-! ### Subset lemmas -/

theorem relBase_subset_bodyBase {Δ : Signature} {fn : SpecFn} :
    (Δ.addBinaryRel fn.rel).Subset
      (((Δ.addBinaryRel fn.rel).addUnary fn.func).addUnaryRel
        (fn.defined)) :=
  (Signature.Subset.subset_addUnary _ fn.func).trans
    (Signature.Subset.subset_addUnaryRel _ (fn.defined))

theorem subset_bodySig_of_headFresh {Δ : Signature} {fn : SpecFn} {x res : String}
    (hfresh : HeadFresh Δ fn x res) :
    Δ.Subset (bodySig Δ fn x) := by
  unfold bodySig
  exact
    (((Signature.Subset.subset_addBinaryRel Δ fn.rel).trans
      (Signature.Subset.subset_addUnary _ fn.func)).trans
      (Signature.Subset.subset_addUnaryRel _ (fn.defined))).trans
      (Signature.subset_declVar_of_fresh (Δ :=
        (((Δ.addBinaryRel fn.rel).addUnary fn.func).addUnaryRel
          (fn.defined))) (v := ⟨x, .value⟩) hfresh.argFresh)

theorem subset_relBodySig_of_headFresh {Δ : Signature} {fn : SpecFn} {x res : String}
    (hfresh : HeadFresh Δ fn x res) :
    Δ.Subset (Relation.bodySig Δ fn x) := by
  unfold Relation.bodySig
  exact (Signature.Subset.subset_addBinaryRel Δ fn.rel).trans
    (Signature.subset_declVar_of_fresh (Δ := Δ.addBinaryRel fn.rel)
      (v := ⟨x, .value⟩) (by
        intro h
        exact hfresh.argFresh (Signature.allNames_subset
          (relBase_subset_bodyBase (Δ := Δ) (fn := fn)) _ h)))

theorem splitBase_subset_bodyBase {Δ : Signature} {fn : SpecFn} :
    ((Δ.addUnary fn.func).addUnaryRel (fn.defined)).Subset
      (((Δ.addBinaryRel fn.rel).addUnary fn.func).addUnaryRel
        (fn.defined)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha => List.mem_cons_of_mem _ ha⟩ <;>
    intro a ha <;>
    simpa [Signature.addUnary, Signature.addUnaryRel, Signature.addBinaryRel] using ha

theorem relBodySig_subset_bodySig {Δ : Signature} {fn : SpecFn} {x : String} :
    (Relation.bodySig Δ fn x).Subset (bodySig Δ fn x) := by
  unfold Relation.bodySig bodySig
  exact Signature.Subset.declVar relBase_subset_bodyBase ⟨x, .value⟩

theorem defvalBodySig_subset_bodySig {Δ : Signature} {fn : SpecFn} {x : String} :
    (defvalBodySig Δ fn x).Subset (bodySig Δ fn x) := by
  unfold defvalBodySig bodySig
  exact Signature.Subset.declVar splitBase_subset_bodyBase ⟨x, .value⟩

theorem subset_defvalBodySig_of_headFresh {Δ : Signature} {fn : SpecFn} {x res : String}
    (hfresh : HeadFresh Δ fn x res) :
    Δ.Subset (defvalBodySig Δ fn x) := by
  unfold defvalBodySig
  exact ((Signature.Subset.subset_addUnary Δ fn.func).trans
    (Signature.Subset.subset_addUnaryRel _ (fn.defined))).trans
    (Signature.subset_declVar_of_fresh (Δ :=
      ((Δ.addUnary fn.func).addUnaryRel (fn.defined)))
      (v := ⟨x, .value⟩) (by
        intro h
        exact hfresh.argFresh (Signature.allNames_subset
          (splitBase_subset_bodyBase (Δ := Δ) (fn := fn)) _ h)))

theorem bodySig_subset_sig_of_headFresh {Δ : Signature} {fn : SpecFn} {x res : String}
    (hfresh : HeadFresh Δ fn x res) :
    (bodySig Δ fn x).Subset (sig Δ fn x res) := by
  unfold sig
  exact Signature.subset_declVar_of_fresh (Δ := bodySig Δ fn x) (v := ⟨res, .value⟩)
    (by simpa [bodySig] using hfresh.resFresh)

theorem relBodySig_subset_relSig_of_headFresh {Δ : Signature} {fn : SpecFn} {x res : String}
    (hfresh : HeadFresh Δ fn x res) :
    (Relation.bodySig Δ fn x).Subset (Relation.sig Δ fn x res) := by
  unfold Relation.sig
  exact Signature.subset_declVar_of_fresh (Δ := Relation.bodySig Δ fn x) (v := ⟨res, .value⟩)
    (by
      intro h
      exact hfresh.resFresh (Signature.allNames_subset
        (relBodySig_subset_bodySig (Δ := Δ) (fn := fn) (x := x)) _ h))

/-! ### Well-formedness lemmas -/

theorem bodySig_wf_of_headFresh {Δ : Signature} {fn : SpecFn} {x res : String}
    (hΔ : Δ.wf) (hfresh : HeadFresh Δ fn x res) :
    (bodySig Δ fn x).wf := by
  unfold bodySig
  have hrel :
      (Δ.addBinaryRel fn.rel).wf :=
    Signature.wf_addBinaryRel hΔ hfresh.relFresh
  have hfun :
      ((Δ.addBinaryRel fn.rel).addUnary fn.func).wf :=
    Signature.wf_addUnary hrel hfresh.funFresh
  have hdef :
      (((Δ.addBinaryRel fn.rel).addUnary fn.func).addUnaryRel
        (fn.defined)).wf :=
    Signature.wf_addUnaryRel hfun hfresh.defFresh
  exact Signature.wf_declVar hdef

theorem relBodySig_wf_of_headFresh {Δ : Signature} {fn : SpecFn} {x res : String}
    (hΔ : Δ.wf) (hfresh : HeadFresh Δ fn x res) :
    (Relation.bodySig Δ fn x).wf := by
  unfold Relation.bodySig
  exact Signature.wf_declVar (Signature.wf_addBinaryRel hΔ hfresh.relFresh)

theorem var_fresh_splitBase_of_headFresh
    {Δ : Signature} {fn : SpecFn} {x res : String}
    (hfresh : HeadFresh Δ fn x res) :
    x ∉ ((Δ.addUnary fn.func).addUnaryRel (fn.defined)).allNames := by
  intro h
  exact hfresh.argFresh (Signature.allNames_subset
    (splitBase_subset_bodyBase (Δ := Δ) (fn := fn)) _ h)

/-- The split-only body signature is well-formed under the existing head
freshness assumptions. -/
theorem defvalBodySig_wf_of_headFresh {Δ : Signature} {fn : SpecFn} {x res : String}
    (hΔ : Δ.wf) (hfresh : HeadFresh Δ fn x res) :
    (defvalBodySig Δ fn x).wf := by
  unfold defvalBodySig
  exact Signature.wf_declVar
    (Signature.wf_addUnaryRel
      (Signature.wf_addUnary hΔ (fun h =>
        hfresh.funFresh (Signature.allNames_subset
          (Signature.Subset.subset_addBinaryRel Δ fn.rel) _ h)))
      (fun h =>
        hfresh.defFresh (Signature.allNames_subset
          (by
            constructor <;> intro a ha
            · simpa [Signature.addUnary, Signature.addBinaryRel] using ha
            · simpa [Signature.addUnary, Signature.addBinaryRel] using ha
            · simpa [Signature.addUnary, Signature.addBinaryRel] using ha
            · simpa [Signature.addUnary, Signature.addBinaryRel] using ha
            · simpa [Signature.addUnary, Signature.addBinaryRel] using ha
            · simpa [Signature.addUnary, Signature.addBinaryRel] using ha
            · exact List.mem_cons_of_mem _ ha) _ h)))

theorem sig_wf_of_headFresh {Δ : Signature} {fn : SpecFn} {x res : String}
    (hΔ : Δ.wf) (hfresh : HeadFresh Δ fn x res) :
    (sig Δ fn x res).wf := by
  unfold sig
  exact Signature.wf_declVar (bodySig_wf_of_headFresh hΔ hfresh)

/-! ### Freshness derivations -/

theorem freshFn_of_headFresh {Γ : FunCtx} {Δ : Signature} {fn : SpecFn} {x res : String}
    (hΓ : Γ.wfIn Δ) (hfresh : HeadFresh Δ fn x res) :
    FunCtx.freshFn Γ fn := by
  intro g fn' hmem
  have hrel'_mem : fn'.relName ∈ Δ.allNames :=
    Signature.mem_allNames_of_binaryRel (hΓ.rel g fn' hmem)
  have hfun_mem : (fn').funcName ∈ Δ.allNames :=
    Signature.mem_allNames_of_unary (hΓ.split g fn' hmem).1
  have hdef_mem : (fn').defName ∈ Δ.allNames :=
    Signature.mem_allNames_of_unaryRel (hΓ.split g fn' hmem).2
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact hfresh.relFresh (h ▸ hrel'_mem)
  · intro h
    exact hfresh.funFresh (h ▸ Signature.allNames_subset
      (Signature.Subset.subset_addBinaryRel Δ fn.rel) _ hfun_mem)
  · intro h
    exact hfresh.defFresh (h ▸ Signature.allNames_subset
      ((Signature.Subset.subset_addBinaryRel Δ fn.rel).trans
        (Signature.Subset.subset_addUnary _ fn.func)) _ hdef_mem)


theorem ctx_relWfIn_relSig_of_headFresh
    {Γ : FunCtx} {Δ : Signature} {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var}
    (hΓfn : Γ.relWfIn Δ) (hfresh : HeadFresh Δ fn x res) :
    (Relation.ctx Γ f fn).relWfIn (Relation.sig Δ fn x res) := by
  intro g fn' hmem
  cases hmem with
  | head =>
      have hxFresh :
          x ∉ (Δ.addBinaryRel fn.rel).allNames := by
        intro h
        exact hfresh.argFresh (Signature.allNames_subset
          (relBase_subset_bodyBase (Δ := Δ) (fn := fn)) _ h)
      exact (relBodySig_subset_relSig_of_headFresh hfresh).binaryRel _
        (by
          unfold Relation.bodySig
          exact (Signature.subset_declVar_of_fresh
            (Δ := Δ.addBinaryRel fn.rel)
            (v := ⟨x, .value⟩) hxFresh).binaryRel _
            (List.Mem.head _))
  | tail _ htail =>
      exact ((subset_relBodySig_of_headFresh hfresh).trans
        (relBodySig_subset_relSig_of_headFresh hfresh)).binaryRel _ (hΓfn g fn' htail)

theorem ctx_splitWfIn_bodySig_of_headFresh
    {Γ : FunCtx} {Δ : Signature} {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var}
    (hΓdef : Γ.splitWfIn Δ) (hfresh : HeadFresh Δ fn x res) :
    (Relation.ctx Γ f fn).splitWfIn (bodySig Δ fn x) := by
  intro g fn' hmem
  cases hmem with
  | head =>
      unfold bodySig
      refine ⟨?_, ?_⟩
      · exact Signature.Subset.unary
          ((Signature.Subset.subset_addUnaryRel _ (fn.defined)).trans
            (Signature.subset_declVar_of_fresh (Δ :=
              (((Δ.addBinaryRel fn.rel).addUnary fn.func).addUnaryRel
                (fn.defined))) (v := ⟨x, .value⟩) hfresh.argFresh))
          fn.func (List.Mem.head _)
      · exact Signature.Subset.unaryRel
          (Signature.subset_declVar_of_fresh (Δ :=
            (((Δ.addBinaryRel fn.rel).addUnary fn.func).addUnaryRel
              (fn.defined))) (v := ⟨x, .value⟩) hfresh.argFresh)
          (fn.defined) (List.Mem.head _)
  | tail _ htail =>
      exact FunCtx.splitWfIn_mono hΓdef (subset_bodySig_of_headFresh hfresh) g fn' htail

theorem ctx_splitWfIn_defvalBodySig_of_headFresh
    {Γ : FunCtx} {Δ : Signature} {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var}
    (hΓdef : Γ.splitWfIn Δ) (hfresh : HeadFresh Δ fn x res) :
    (Relation.ctx Γ f fn).splitWfIn (defvalBodySig Δ fn x) := by
  intro g fn' hmem
  cases hmem with
  | head =>
      unfold defvalBodySig
      refine ⟨?_, ?_⟩
      · exact Signature.Subset.unary
          ((Signature.Subset.subset_addUnaryRel _ (fn.defined)).trans
            (Signature.subset_declVar_of_fresh (Δ :=
              ((Δ.addUnary fn.func).addUnaryRel (fn.defined)))
              (v := ⟨x, .value⟩) (var_fresh_splitBase_of_headFresh hfresh)))
          fn.func (List.Mem.head _)
      · exact Signature.Subset.unaryRel
          (Signature.subset_declVar_of_fresh (Δ :=
            ((Δ.addUnary fn.func).addUnaryRel (fn.defined)))
            (v := ⟨x, .value⟩) (var_fresh_splitBase_of_headFresh hfresh))
          (fn.defined) (List.Mem.head _)
  | tail _ htail =>
      exact FunCtx.splitWfIn_mono hΓdef (subset_defvalBodySig_of_headFresh hfresh)
        g fn' htail


/-- The body supply covers every signature the body encodings run in. -/
theorem relBodySupply_covers_of_subset {Δ Δ' : Signature} {fn : SpecFn} {x res : TinyML.Var}
    (hsub : Δ'.Subset (sig Δ fn x res)) : (relBodySupply Δ fn x res).Covers Δ' :=
  fun n hn => relBodySupply_covers_sig Δ fn x res n (Signature.allNames_subset hsub n hn)

/-- Every name of a signature the body encodings run in is either a name the
encoding starts from or one it must not bind. This is the side condition of
`Expr.WfIn.mono` between two such signatures. -/
theorem names_of_subset_sig {Δ Δbase Δ' : Signature} {fn : SpecFn} {x res : TinyML.Var}
    (hsub : Δ'.Subset (sig Δ fn x res)) (hbase : Δ.Subset Δbase) :
    ∀ n ∈ Δ'.allNames, n ∈ Δbase.allNames ∨ n ∈ bodyAvoid fn x res :=
  fun n hn => (List.mem_append.mp (relBodySupply_covers_of_subset hsub n hn)).imp
    (Signature.allNames_subset hbase n) id

/-- Successful split body encodings are well-formed in the split-only body
signature. -/
theorem splitBody_wfIn_defvalBodySig {primitives : PrimEncodings}
    {Γ : FunCtx} {Δ : Signature}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal}
    (hlaw : primitives.Lawful)
    (hΔ : Δ.wf) (hΓdef : Γ.splitWfIn Δ)
    (hheadFresh : HeadFresh Δ fn x res)
    (henc : splitBody primitives Γ Δ f fn x res e = .ok body) :
    body.wfIn (defvalBodySig Δ fn x) := by
  obtain ⟨c, hc, rfl⟩ := Except.map_eq_ok henc
  refine split_wfIn_of_gate e hlaw
    (subset_defvalBodySig_of_headFresh hheadFresh)
    (defvalBodySig_wf_of_headFresh hΔ hheadFresh)
    (ctx_splitWfIn_defvalBodySig_of_headFresh hΓdef hheadFresh)
    (varEnv_defvalBodySig (Δ := Δ) (fn := fn) (x := x) ▸
      VarEnv.ofSignature_wfIn (defvalBodySig_wf_of_headFresh hΔ hheadFresh))
    (relBodySupply_covers_of_subset
      (defvalBodySig_subset_bodySig.trans (bodySig_subset_sig_of_headFresh hheadFresh)))
    hc

/-- Successful split body encodings are well-formed in the full body
signature. -/
theorem splitBody_wfIn_bodySig {primitives : PrimEncodings}
    {Γ : FunCtx} {Δ : Signature}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal}
    (hlaw : primitives.Lawful)
    (hΔ : Δ.wf) (hΓdef : Γ.splitWfIn Δ)
    (hheadFresh : HeadFresh Δ fn x res)
    (henc : splitBody primitives Γ Δ f fn x res e = .ok body) :
    body.wfIn (bodySig Δ fn x) := by
  obtain ⟨c, hc, rfl⟩ := Except.map_eq_ok henc
  refine split_wfIn_of_gate e hlaw
    (subset_bodySig_of_headFresh hheadFresh)
    (bodySig_wf_of_headFresh hΔ hheadFresh)
    (ctx_splitWfIn_bodySig_of_headFresh hΓdef hheadFresh)
    (varEnv_bodySig (Δ := Δ) (fn := fn) (x := x) ▸
      VarEnv.ofSignature_wfIn (bodySig_wf_of_headFresh hΔ hheadFresh))
    (relBodySupply_covers_of_subset (bodySig_subset_sig_of_headFresh hheadFresh))
    hc


/-- The split body never mentions the result variable, so pinning `res` does not
change what it reads. -/
theorem defval_eval_updateConst_res {primitives : PrimEncodings}
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} {D : Srt.value.denote → Prop}
    {F : Srt.value.denote → Srt.value.denote}
    (hlaw : primitives.Lawful) (hΔ : Δ.wf) (hΓdef : Γ.splitWfIn Δ)
    (hheadFresh : HeadFresh Δ fn x res)
    (henc : splitBody primitives Γ Δ f fn x res e = .ok body)
    (vin vout : Srt.value.denote) :
    (body.defined.eval ((defEnv ρ fn x D F vin).updateConst .value res vout) ↔
        body.defined.eval (defEnv ρ fn x D F vin)) ∧
      body.value.eval ((defEnv ρ fn x D F vin).updateConst .value res vout) =
        body.value.eval (defEnv ρ fn x D F vin) := by
  have hbody : body.wfIn (bodySig Δ fn x) :=
    splitBody_wfIn_bodySig hlaw hΔ hΓdef hheadFresh henc
  have hag : Env.agreeOn (bodySig Δ fn x) (defEnv ρ fn x D F vin)
      ((defEnv ρ fn x D F vin).updateConst .value res vout) :=
    Env.agreeOn_update_fresh_const (c := ⟨res, .value⟩)
      (by simpa [bodySig] using hheadFresh.resFresh)
  exact ⟨(Formula.eval_env_agree hbody.2 hag).symm, (Term.eval_env_agree hbody.1 hag).symm⟩

theorem relEnv_splitEnv_agreeOn_relSig
    {Δ : Signature} {ρ : Env} {fn : SpecFn} {x res : String}
    {R : ValRel} {D : Srt.value.denote → Prop}
    {F : Srt.value.denote → Srt.value.denote}
    (hfresh : HeadFresh Δ fn x res) (vin vout : Srt.value.denote) :
    Env.agreeOn (Relation.sig Δ fn x res)
      (Relation.relEnv ρ fn x res R vin vout)
      (((splitEnv ρ fn R D F).updateConst .value x vin).updateConst .value res vout) := by
  let ρbin := ρ.updateBinaryRel .value .value fn.relName R
  let ρfun := ρbin.updateUnary .value .value (fn.funcName) F
  have hbase :
      Env.agreeOn (Δ.addBinaryRel fn.rel) ρbin
        (splitEnv ρ fn R D F) := by
    have hfun : Env.agreeOn (Δ.addBinaryRel fn.rel) ρbin ρfun := by
      simpa [ρbin, ρfun] using
        (Env.agreeOn_update_fresh_unary (ρ := ρbin) (u := fn.func)
          (f := F) (Δ := Δ.addBinaryRel fn.rel) hfresh.funFresh)
    have hdef :
        Env.agreeOn (Δ.addBinaryRel fn.rel) ρfun
          (splitEnv ρ fn R D F) := by
      have hdefFresh : fn.defName ∉ (Δ.addBinaryRel fn.rel).allNames := by
        intro h
        exact hfresh.defFresh (Signature.allNames_subset
          (Signature.Subset.subset_addUnary _ fn.func) _ h)
      simpa [splitEnv, ρbin, ρfun] using
        (Env.agreeOn_update_fresh_unaryRel (ρ := ρfun) (u := fn.defined)
          (f := D) (Δ := Δ.addBinaryRel fn.rel) hdefFresh)
    exact Env.agreeOn_trans hfun hdef
  simpa [Relation.relEnv, Relation.sig, Relation.bodySig] using
    (Env.agreeOn_declVar
      (Env.agreeOn_declVar hbase : Env.agreeOn
        ((Δ.addBinaryRel fn.rel).declVar ⟨x, .value⟩)
        ((ρ.updateBinaryRel .value .value fn.relName R).updateConst .value x vin)
        ((splitEnv ρ fn R D F).updateConst .value x vin)) :
      Env.agreeOn
        (((Δ.addBinaryRel fn.rel).declVar ⟨x, .value⟩).declVar
          ⟨res, .value⟩)
        (((ρ.updateBinaryRel .value .value fn.relName R).updateConst .value x vin).updateConst
          .value res vout)
        (((splitEnv ρ fn R D F).updateConst .value x vin).updateConst .value res vout))

theorem relEncodeBody_wfIn_relSig {primitives : PrimEncodings}
    {Γ : FunCtx} {Δ : Signature}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {φ : Formula}
    (hlaw : primitives.Lawful)
    (hΓfn : Γ.relWfIn Δ) (hΔ : Δ.wf) (hheadFresh : HeadFresh Δ fn x res)
    (hrelEnc : Relation.relEncodeBody primitives Γ Δ f fn x res e = .ok φ) :
    φ.wfIn (Relation.sig Δ fn x res) := by
  obtain ⟨c, hc, rfl⟩ := Except.map_eq_ok hrelEnc
  have hΔrelBody : (Relation.bodySig Δ fn x).wf := relBodySig_wf_of_headFresh hΔ hheadFresh
  have hsigWf : (Relation.sig Δ fn x res).wf := Signature.wf_declVar hΔrelBody
  have hcovRel : (relBodySupply Δ fn x res).Covers (Relation.bodySig Δ fn x) :=
    relBodySupply_covers_of_subset
      (relBodySig_subset_bodySig.trans (bodySig_subset_sig_of_headFresh hheadFresh))
  have hcWf : Expr.WfIn (Relation.ctx Γ f fn) (bodyAvoid fn x res)
      (Relation.bodySig Δ fn x) c :=
    (encode_wfIn hlaw e (subset_relBodySig_of_headFresh hheadFresh) hΔrelBody
      (VarEnv.ofSignature_wfIn hΔrelBody) hcovRel hc).weaken bodyAvoid_subset_relBodySupply
  exact Relation.ofExpr_wfIn
    (hcWf.mono (relBodySig_subset_relSig_of_headFresh hheadFresh) hsigWf
      (names_of_subset_sig
        (Signature.Subset.declVar relBodySig_subset_bodySig ⟨res, .value⟩)
        (subset_relBodySig_of_headFresh hheadFresh)))
    (ctx_relWfIn_relSig_of_headFresh hΓfn hheadFresh) hsigWf
    (Signature.var_mem_declVar _ ⟨res, .value⟩)


/-- A successful split body encoding exposes the shared IR expression behind
it: the split body is its split reading, the relational body encoding is its
relational reading, and it is well-formed in the body signature. -/
theorem splitBody_witness {primitives : PrimEncodings} {Γ : FunCtx} {Δ : Signature}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr} {body : DefVal}
    (hlaw : primitives.Lawful) (hΔ : Δ.wf) (hheadFresh : HeadFresh Δ fn x res)
    (henc : splitBody primitives Γ Δ f fn x res e = .ok body) :
    ∃ c, body = ofExpr .id c ∧
      Relation.relEncodeBody primitives Γ Δ f fn x res e = .ok (Relation.ofExpr res c) ∧
      Expr.WfIn (Relation.ctx Γ f fn) (bodyAvoid fn x res) (bodySig Δ fn x) c := by
  obtain ⟨c, hc, rfl⟩ := Except.map_eq_ok henc
  have hΔrelBody : (Relation.bodySig Δ fn x).wf := relBodySig_wf_of_headFresh hΔ hheadFresh
  refine ⟨c, rfl, by simp [Relation.relEncodeBody, hc], ?_⟩
  exact ((encode_wfIn hlaw e (subset_relBodySig_of_headFresh hheadFresh) hΔrelBody
      (VarEnv.ofSignature_wfIn hΔrelBody)
      (relBodySupply_covers_of_subset
        (relBodySig_subset_bodySig.trans (bodySig_subset_sig_of_headFresh hheadFresh)))
      hc).weaken bodyAvoid_subset_relBodySupply).mono relBodySig_subset_bodySig
      (bodySig_wf_of_headFresh hΔ hheadFresh)
      (names_of_subset_sig (bodySig_subset_sig_of_headFresh hheadFresh)
        (subset_relBodySig_of_headFresh hheadFresh))

/-! ## The two readings of the IR agree

Both encodings consume the same `Expr`, so their agreement is a three-case
induction on it. `Δ` grows with the names the calls bind, `ρrel` with the
witnesses the relational side picks for them, and `σ` with the value terms the
split side substituted; `SubstAgree` says the two accounts of those names
agree. -/
theorem ofExpr_iff {Γ : FunCtx} {Δbase : Signature} {res : String} {ρdef : Env}
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
theorem body_eval_iff {Γ : FunCtx} {Δ : Signature} {ρsplit : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {c : Expr}
    (hΓdef : Γ.splitWfIn Δ) (hΔ : Δ.wf) (hheadFresh : HeadFresh Δ fn x res)
    (hcWf : Expr.WfIn (Relation.ctx Γ f fn) (bodyAvoid fn x res) (bodySig Δ fn x) c)
    (hΓsplit : (Relation.ctx Γ f fn).splitCompatible ρsplit)
    (vin vout : Srt.value.denote) :
    (Relation.ofExpr res c).eval
        ((ρsplit.updateConst .value x vin).updateConst .value res vout) ↔
      ((ofExpr .id c).defined.eval
          ((ρsplit.updateConst .value x vin).updateConst .value res vout) ∧
        (ofExpr .id c).value.eval
          ((ρsplit.updateConst .value x vin).updateConst .value res vout) = vout) := by
  have hΔbody : (bodySig Δ fn x).wf := bodySig_wf_of_headFresh hΔ hheadFresh
  have h := ofExpr_iff (res := res)
    (ctx_splitWfIn_bodySig_of_headFresh hΓdef hheadFresh) hΔbody
    hcWf (by simp [bodyAvoid]) (Signature.Subset.refl _) (Signature.SymbolSubset.refl _)
    (Subst.id_wfIn (fun _ h => h) hΔbody)
    (FunCtx.splitCompatible_updateConst
      (FunCtx.splitCompatible_updateConst hΓsplit .value x vin) .value res vout)
    Env.agreeOn_refl substAgree_refl rfl
  simpa [Env.lookupConst_updateConst_same] using h

/-- Evaluating the relational body formula in the combined `splitEnv` is
equivalent to the abstract semantic body operator. -/
theorem rel_body_eval_iff {primitives : PrimEncodings}
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {φ : Formula} {R : ValRel}
    {D : Srt.value.denote → Prop} {F : Srt.value.denote → Srt.value.denote}
    (hlaw : primitives.Lawful)
    (hΓrel : Γ.relWfIn Δ) (hΔ : Δ.wf) (hheadFresh : HeadFresh Δ fn x res)
    (hrelEnc : relEncodeBody primitives Γ Δ f fn x res e = .ok φ)
    (vin vout : Srt.value.denote) :
    φ.eval (((splitEnv ρ fn R D F).updateConst .value x vin).updateConst
        .value res vout) ↔
      Relation.semanticBody Formula.sem ρ fn x res φ R vin vout := by
  have hφwf : φ.wfIn (Relation.sig Δ fn x res) :=
    relEncodeBody_wfIn_relSig hlaw hΓrel hΔ hheadFresh hrelEnc
  have hag :=
    relEnv_splitEnv_agreeOn_relSig (Δ := Δ) (ρ := ρ) (fn := fn)
      (x := x) (res := res) (R := R) (D := D) (F := F) hheadFresh vin vout
  unfold Relation.semanticBody Formula.sem
  exact (Formula.eval_env_agree hφwf hag).symm

end Skolemize
end Verifier.RelationalEncoding