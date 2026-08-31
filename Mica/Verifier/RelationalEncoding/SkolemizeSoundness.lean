-- SUMMARY: Soundness of Skolemization: split definedness/value implies the relational encoding.
import Mica.Verifier.RelationalEncoding.SkolemizeCommon

namespace Verifier.RelationalEncoding
open Relation

namespace Skolemize

/-! ## Soundness on the intermediate language

Both encodings consume the same `Expr`, so transferring information from the
split defined/value encoding to the relational one is a three-case induction on
it. `Δ` grows with the names the calls bind, `ρrel` with the witnesses the
relational side picks for them, and `σ` with the value terms the split side
substituted; `SubstAgree` says the two accounts of those names agree. -/
theorem ofExpr_sound {Γ : FunCtx} {Δbase : Signature} {res : String} {ρdef : Env}
    (hΓdef : Γ.splitWfIn Δbase) (hΔbase : Δbase.wf) :
    ∀ {Δ : Signature} {s : NameSupply} {c : Expr} {σ : Subst} {ρrel : Env},
      Expr.WfIn Γ Δ s c →
      Δbase.Subset Δ → Δ.SymbolSubset Δbase → s.Covers Δ → res ∈ s.avoid →
      σ.wfIn Δ.vars Δbase → Γ.splitSound ρrel →
      Env.agreeOn Δbase ρrel ρdef → SubstAgree Δ ρrel ρdef σ →
      ρrel.lookupConst .value res = ρdef.lookupConst .value res →
      (ofExpr σ c).defined.eval ρdef →
      (ofExpr σ c).value.eval ρdef = ρdef.lookupConst .value res →
      (Relation.ofExpr res c).eval ρrel := by
  intro Δ s c σ ρrel hc
  induction hc generalizing σ ρrel with
  | @ret Δ s v hv =>
      intro _ _ _ _ hσ _ _ hagree hres _ hval
      simp only [ofExpr] at hval
      simp only [Relation.ofExpr, Formula.eval, Term.eval]
      rw [eval_substAgree hagree hv hσ hΔbase, hval, hres]
  | @call Δ s f fn arg r c hmem harg hr _ ih =>
      intro hsubBase hsym hcov hresAvoid hσ hΓs hagBase hagree hres hdef hval
      simp only [ofExpr, Formula.eval] at hdef hval
      obtain ⟨hdefCall, hdefRest⟩ := hdef
      have hfresh : r ∉ Δ.allNames := fun hm => hr (hcov r hm)
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
      have hedge : fn.evalRelates ρrel (Term.eval ρrel arg)
          (Term.eval ρdef (fn.call (arg.subst σ))) := by
        refine hΓs f fn hmem _ _ ⟨?_, ?_⟩
        · show fn.evalDefined ρrel (Term.eval ρrel arg)
          rw [show fn.evalDefined ρrel = fn.evalDefined ρdef from hunaryRel, hargEval]
          simpa using hdefCall
        · show fn.evalCall ρrel (Term.eval ρrel arg) = _
          rw [show fn.evalCall ρrel = fn.evalCall ρdef from hunary, hargEval]
          simp [SpecFn.call, SpecFn.evalCall, SpecFn.func, Term.eval]
      simp only [Relation.ofExpr, Formula.eval]
      refine ⟨Term.eval ρdef (fn.call (arg.subst σ)), ?_, ?_⟩
      · simpa [SpecFn.relates, Formula.eval, BinPred.eval, Term.eval,
          Env.updateConst_binaryRel, Env.lookupConst_updateConst_same,
          Term.eval_update_fresh harg hfresh] using hedge
      · refine ih (hsubBase.trans (Signature.subset_declVar_of_fresh hfresh))
          (Signature.SymbolSubset.declVar hsym _)
          (NameSupply.Covers.declVar hcov r .value)
          (by simp [NameSupply.reserve, hresAvoid])
          ?_
          (FunCtx.splitSound_updateConst hΓs .value r _)
          ?_ (substAgree_bind hagree) ?_ hdefRest hval
        · rw [Signature.vars_declVar_of_not_in (v := ⟨r, .value⟩) hfresh]
          exact Subst.wfIn_update hσ
            (SpecFn.call_wfIn hsyms.1 hΔbase
              (Term.subst_wfIn harg hσ (fun _ h => h) hsym hΔbase))
        · exact Env.agreeOn_trans
            (Env.agreeOn_symm
              (Env.agreeOn_update_fresh_const (c := ⟨r, .value⟩) hfreshBase)) hagBase
        · rw [Env.lookupConst_updateConst_ne hres_ne]; exact hres
  | @ite Δ s cond t e hcond _ _ iht ihe =>
      intro hsubBase hsym hcov hresAvoid hσ hΓs hagBase hagree hres hdef hval
      simp only [ofExpr, Formula.iteBool, Formula.eval, Term.eval,
        Const.denote] at hdef hval
      simp only [Relation.ofExpr, Formula.iteBool, Formula.eval, Term.eval, Const.denote]
      have hcondEval : Term.eval ρrel cond = Term.eval ρdef (cond.subst σ) :=
        eval_substAgree hagree hcond hσ hΔbase
      constructor
      · intro hc
        have hc2 : Term.eval ρdef (cond.subst σ) = true := by rw [← hcondEval]; exact hc
        exact iht hsubBase hsym hcov hresAvoid hσ hΓs hagBase hagree hres
          (hdef.1 hc2) (by simpa [hc2] using hval)
      · intro hc
        have hc2 : Term.eval ρdef (cond.subst σ) = false := by rw [← hcondEval]; exact hc
        exact ihe hsubBase hsym hcov hresAvoid hσ hΓs hagBase hagree hres
          (hdef.2 hc2) (by simpa [hc2] using hval)

/-! ## Transport between split and combined environments -/

theorem defval_eval_transport_to_relSplit_domain {primitives : PrimEncodings}
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} {R : ValRel}
    {P : Srt.value.denote → Prop} {F : Srt.value.denote → Srt.value.denote}
    (hlaw : primitives.Lawful)
    (henc : splitBody primitives Γ Δ f fn x res e = .ok body)
    (hΓdef : Γ.splitWfIn Δ) (hΔ : Δ.wf) (hheadFresh : HeadFresh Δ fn x res)
    (vin : Srt.value.denote)
    (hdefBody : defBody ρ fn x body F P vin) :
    let vbody := body.value.eval (defEnv ρ fn x P F vin)
    body.defined.eval (((relSplitEnv ρ fn R P F).updateConst .value x vin).updateConst .value res vbody) ∧
      body.value.eval (((relSplitEnv ρ fn R P F).updateConst .value x vin).updateConst .value res vbody) =
        vbody := by
  let vbody := body.value.eval (defEnv ρ fn x P F vin)
  have hbody : body.wfIn (defvalBodySig Δ fn x) :=
    splitBody_wfIn_defvalBodySig hlaw hΔ hΓdef hheadFresh henc
  have hag : Env.agreeOn (defvalBodySig Δ fn x)
      (defEnv ρ fn x P F vin)
      (((relSplitEnv ρ fn R P F).updateConst .value x vin).updateConst .value res vbody) :=
    splitEnv_relSplitEnv_agreeOn_defvalBodySig (R := R) (D := P) (F := F)
      hheadFresh vin vbody
  exact ⟨(Formula.eval_env_agree hbody.2 hag).mp hdefBody,
    (Term.eval_env_agree hbody.1 hag).symm⟩

/-- Split definedness plus the split body value gives a relational edge. This
is the converse half of the relation/split fixpoint equivalence. -/
theorem semrel_sound {primitives : PrimEncodings}
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (hlaw : primitives.Lawful)
    (henc : splitBody primitives Γ Δ f fn x res e = .ok body)
    (hΓ : Γ.splitCompatible ρ)
    (hΓwf : Γ.wfIn Δ)
    (hΔ : Δ.wf) (hheadFresh : HeadFresh Δ fn x res)
    (vin vout : Srt.value.denote) :
    semdef primitives Γ Δ ρ f fn x res e body vin →
      body.value.eval
        ((defInterpEnv primitives Γ Δ ρ f fn x res e body).updateConst .value x vin) =
      vout →
      semrel primitives Γ Δ ρ f fn x res e vin vout := by
  intro hsem hval
  obtain ⟨c, hc, rfl⟩ := Except.map_eq_ok henc
  have hΔbody : (bodySig Δ fn x).wf := bodySig_wf_of_headFresh hΔ hheadFresh
  have hΔrelBody : (Relation.bodySig Δ fn x).wf := relBodySig_wf_of_headFresh hΔ hheadFresh
  have hcovBody : (relBodySupply Δ fn x res).Covers (bodySig Δ fn x) :=
    relBodySupply_covers_of_subset (bodySig_subset_sig_of_headFresh hheadFresh)
  have hresAvoid : res ∈ (relBodySupply Δ fn x res).avoid := by simp [relBodySupply]
  have hcWf : Expr.WfIn (Relation.ctx Γ f fn) (bodySig Δ fn x) (relBodySupply Δ fn x res) c :=
    (encodeWith_wfIn hlaw e (subset_relBodySig_of_headFresh hheadFresh) hΔrelBody
      (VarEnv.ofSignature_wfIn hΔrelBody)
      (relBodySupply_covers_of_subset
        (relBodySig_subset_bodySig.trans (bodySig_subset_sig_of_headFresh hheadFresh)))
      ret_wfCont hc).mono relBodySig_subset_bodySig hΔbody
  set φ := Relation.ofExpr res c with hφ_def
  have hrelEnc : Relation.relEncodeBody primitives Γ Δ f fn x res e = .ok φ := by
    simp [Relation.relEncodeBody, hc, hφ_def]
  let R : ValRel := semrel primitives Γ Δ ρ f fn x res e
  let F : Srt.value.denote → Srt.value.denote := semFunc R
  let D : Srt.value.denote → Prop := semdef primitives Γ Δ ρ f fn x res e (ofExpr .id c)
  have hrel_eq :
      R = RelationFix.lfp (Relation.semanticBody Formula.sem ρ fn x res φ) := by
    simp [R, Relation.semrel, Relation.semanticFixpoint, hrelEnc]
  have hpreR :
      RelationFix.le (Relation.semanticBody Formula.sem ρ fn x res φ R) R := by
    rw [hrel_eq]
    exact RelationFix.lfp_prefixed
      (Relation.semanticBody_mono_of_semanticMono (Relation.ofExpr_mono res c))
  have hφ_of_split
      {ρsplit : Env} {vin' vout' : Srt.value.denote}
      (hΓsplit : (Relation.ctx Γ f fn).splitSound ρsplit)
      (hsplit :
        (ofExpr .id c).defined.eval
            ((ρsplit.updateConst .value x vin').updateConst .value res vout') ∧
          (ofExpr .id c).value.eval
            ((ρsplit.updateConst .value x vin').updateConst .value res vout') = vout') :
      φ.eval ((ρsplit.updateConst .value x vin').updateConst .value res vout') := by
    refine ofExpr_sound (ctx_splitWfIn_bodySig_of_headFresh hΓwf.split hheadFresh) hΔbody
      hcWf (Signature.Subset.refl _) (Signature.SymbolSubset.refl _) hcovBody hresAvoid
      (Subst.id_wfIn (fun _ h => h) hΔbody)
      (FunCtx.splitSound_updateConst
        (FunCtx.splitSound_updateConst hΓsplit .value x vin') .value res vout')
      Env.agreeOn_refl substAgree_refl rfl hsplit.1 ?_
    simpa [Env.lookupConst_updateConst_same] using hsplit.2
  have hdomain :
      PredicateFix.le D (semDefined R) := by
    unfold D semdef
    apply PredicateFix.lfp_le_of_prefixed
    intro vin hdefBody
    let P : Srt.value.denote → Prop := semDefined R
    let vbody := (ofExpr .id c).value.eval (defEnv ρ fn x P F vin)
    let ρP := relSplitEnv ρ fn R P F
    have hΓP : (Relation.ctx Γ f fn).splitSound ρP := by
      exact splitSound_cons_relSplitEnv
        (FunCtx.splitSound_of_compatible hΓ)
        (freshFn_of_headFresh hΓwf hheadFresh)
        (by
          intro a b hsplit
          have hcall : R a (F a) := semFunc_spec hsplit.1
          simpa [hsplit.2] using hcall)
    have hsplitP :
        (ofExpr .id c).defined.eval ((ρP.updateConst .value x vin).updateConst .value res vbody) ∧
          (ofExpr .id c).value.eval ((ρP.updateConst .value x vin).updateConst .value res vbody) =
            vbody :=
      defval_eval_transport_to_relSplit_domain (R := R) (P := P)
        hlaw henc hΓwf.split hΔ hheadFresh vin hdefBody
    have hφP :
        φ.eval ((ρP.updateConst .value x vin).updateConst .value res vbody) :=
      hφ_of_split hΓP hsplitP
    have hbodyR : Relation.semanticBody Formula.sem ρ fn x res φ R vin vbody :=
      (rel_body_eval_iff (D := P) (F := F) hlaw hΓwf.rel hΔ hheadFresh hrelEnc vin vbody).mp hφP
    exact ⟨vbody, hpreR vin vbody hbodyR⟩
  have hdefBody :
      defBody ρ fn x (ofExpr .id c) F D vin := by
    simpa [D, F] using
      (semdef_unfold_of_split (ρ := ρ) (x := x) (res := res) henc vin).mp hsem
  let ρD := relSplitEnv ρ fn R D F
  have hΓD : (Relation.ctx Γ f fn).splitSound ρD := by
    exact splitSound_cons_relSplitEnv
      (FunCtx.splitSound_of_compatible hΓ)
      (freshFn_of_headFresh hΓwf hheadFresh)
      (by
        intro a b hsplit
        have hcall : R a (F a) := semFunc_spec (hdomain a hsplit.1)
        simpa [hsplit.2] using hcall)
  have hsplitD :
      (ofExpr .id c).defined.eval ((ρD.updateConst .value x vin).updateConst .value res vout) ∧
        (ofExpr .id c).value.eval ((ρD.updateConst .value x vin).updateConst .value res vout) =
          vout := by
    have hvalEq : (ofExpr .id c).value.eval (defEnv ρ fn x D F vin) = vout := by
      simpa [D, F, R, defInterpEnv, defEnv] using hval
    rw [← hvalEq]
    exact defval_eval_transport_to_relSplit_domain (R := R) (P := D)
      hlaw henc hΓwf.split hΔ hheadFresh vin hdefBody
  have hφD :
      φ.eval ((ρD.updateConst .value x vin).updateConst .value res vout) :=
    hφ_of_split hΓD hsplitD
  have hbodyR : Relation.semanticBody Formula.sem ρ fn x res φ R vin vout :=
    (rel_body_eval_iff (D := D) (F := F) hlaw hΓwf.rel hΔ hheadFresh hrelEnc vin vout).mp hφD
  exact hpreR vin vout hbodyR

theorem relation_semrel_functional_of_encodeBody {primitives : PrimEncodings}
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (hlaw : primitives.Lawful)
    (henc : splitBody primitives Γ Δ f fn x res e = .ok body)
    (hΔ : Δ.wf) (hΓwf : Γ.wfIn Δ)
    (hheadFresh : HeadFresh Δ fn x res)
    (hρdet : Relation.BinaryRelDet Γ ρ ρ)
    (vin y₁ y₂ : Srt.value.denote) :
    semrel primitives Γ Δ ρ f fn x res e vin y₁ →
      semrel primitives Γ Δ ρ f fn x res e vin y₂ →
      y₁ = y₂ := by
  obtain ⟨c, hc, rfl⟩ := Except.map_eq_ok henc
  have hresFreshR : res ∉ (Relation.bodySig Δ fn x).allNames := by
    intro hres
    exact hheadFresh.resFresh (Signature.allNames_subset
      (relBodySig_subset_bodySig (Δ := Δ) (fn := fn) (x := x)) _ hres)
  exact Relation.semrel_functional (primitives := primitives) hlaw hc hΓwf.rel
    hheadFresh.relFresh
    (subset_relBodySig_of_headFresh hheadFresh)
    (relBodySig_wf_of_headFresh hΔ hheadFresh)
    hresFreshR hρdet vin y₁ y₂

/-- If the split body is defined at an input, then the body value is the
canonical value chosen from the relational semantics. This is the exact
soundness fact needed by the completeness direction when it builds the graph
of the split interpretation inside the relational fixpoint. -/
theorem semFunc_eq_of_semdef_value {primitives : PrimEncodings}
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (hlaw : primitives.Lawful)
    (henc : splitBody primitives Γ Δ f fn x res e = .ok body)
    (hΓ : Γ.splitCompatible ρ)
    (hΓwf : Γ.wfIn Δ)
    (hΔ : Δ.wf) (hheadFresh : HeadFresh Δ fn x res)
    (hρdet : Relation.BinaryRelDet Γ ρ ρ)
    (vin vout : Srt.value.denote) :
    semdef primitives Γ Δ ρ f fn x res e body vin →
      body.value.eval
        ((defInterpEnv primitives Γ Δ ρ f fn x res e body).updateConst .value x vin) =
      vout →
      semFunc (semrel primitives Γ Δ ρ f fn x res e) vin = vout := by
  intro hdefined hval
  let R : ValRel := semrel primitives Γ Δ ρ f fn x res e
  have hrelBody : R vin vout := by
    simpa [R] using
      semrel_sound hlaw henc hΓ hΓwf hΔ hheadFresh vin vout hdefined hval
  have hdefinedR : semDefined R vin := ⟨vout, hrelBody⟩
  have hchosen : R vin (semFunc R vin) := semFunc_spec hdefinedR
  exact relation_semrel_functional_of_encodeBody hlaw henc hΔ hΓwf hheadFresh hρdet vin
      (semFunc R vin) vout (by simpa [R] using hchosen) (by simpa [R] using hrelBody)

end Skolemize
end Verifier.RelationalEncoding
