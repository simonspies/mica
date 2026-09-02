-- SUMMARY: Completeness of Skolemization: relational encoding implies split definedness/value.
import Mica.Verifier.RelationalEncoding.SkolemizeSoundness

namespace Verifier.RelationalEncoding
open Relation

namespace Skolemize

/-! ## Completeness on the intermediate language

The opposite direction of `ofExpr_sound`, on the same three cases: the
relational formula supplies a witness for each call, `Γ.splitComplete` turns it
into the split definedness and value facts, and the witness is forced to be the
term the split encoding substituted. -/
theorem ofExpr_complete {Γ : FunCtx} {Δbase : Signature} {res : String} {ρdef : Env}
    (hΓdef : Γ.splitWfIn Δbase) (hΔbase : Δbase.wf) :
    ∀ {avoid : List String} {Δ : Signature} {c : Expr} {σ : Subst} {ρrel : Env},
      Expr.WfIn Γ avoid Δ c → res ∈ avoid →
      Δbase.Subset Δ → Δ.SymbolSubset Δbase →
      σ.wfIn Δ.vars Δbase → Γ.splitComplete ρrel →
      Env.agreeOn Δbase ρrel ρdef → SubstAgree Δ ρrel ρdef σ →
      ρrel.lookupConst .value res = ρdef.lookupConst .value res →
      (Relation.ofExpr res c).eval ρrel →
      (ofExpr σ c).defined.eval ρdef ∧
        (ofExpr σ c).value.eval ρdef = ρdef.lookupConst .value res := by
  intro avoid Δ c σ ρrel hc hresAvoid
  induction hc generalizing σ ρrel with
  | @ret Δ v hv =>
      intro _ _ hσ _ _ hagree hres hφ
      simp only [Relation.ofExpr, Formula.eval, Term.eval] at hφ
      refine ⟨trivial, ?_⟩
      simp only [ofExpr]
      rw [← eval_substAgree hagree hv hσ hΔbase, hφ, hres]
  | @call Δ f fn arg r c hmem harg hr hfresh _ ih =>
      intro hsubBase hsym hσ hΓc hagBase hagree hres hφ
      simp only [Relation.ofExpr, Formula.eval] at hφ
      obtain ⟨w, hcall, hrest⟩ := hφ
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
      have hcall' : fn.evalRelates ρrel (Term.eval ρrel arg) w := by
        simpa [SpecFn.relates, SpecFn.evalRelates, SpecFn.rel, Formula.eval, BinPred.eval,
          Term.eval, Env.updateConst_binaryRel, Env.lookupConst_updateConst_same,
          Term.eval_update_fresh harg hfresh] using hcall
      obtain ⟨hdefRel, hcallRel⟩ := hΓc f fn hmem _ w hcall'
      have hdefDef : (fn.isDefined (arg.subst σ)).eval ρdef := by
        rw [show fn.evalDefined ρrel = fn.evalDefined ρdef from hunaryRel, hargEval] at hdefRel
        simpa using hdefRel
      have hw : w = Term.eval ρdef (fn.call (arg.subst σ)) := by
        rw [← hcallRel, show fn.evalCall ρrel = fn.evalCall ρdef from hunary, hargEval]
        simp [SpecFn.call, SpecFn.evalCall, SpecFn.func, Term.eval]
      subst hw
      have hrec := ih (hsubBase.trans (Signature.subset_declVar_of_fresh hfresh))
        (Signature.SymbolSubset.declVar hsym _)
        (by
          rw [Signature.vars_declVar_of_not_in (v := ⟨r, .value⟩) hfresh]
          exact Subst.wfIn_update hσ
            (SpecFn.call_wfIn hsyms.1 hΔbase
              (Term.subst_wfIn harg hσ (fun _ h => h) hsym hΔbase)))
        (FunCtx.splitComplete_updateConst hΓc .value r _)
        (Env.agreeOn_trans
          (Env.agreeOn_symm
            (Env.agreeOn_update_fresh_const (c := ⟨r, .value⟩) hfreshBase)) hagBase)
        (substAgree_bind hagree)
        (by rw [Env.lookupConst_updateConst_ne hres_ne]; exact hres)
        hrest
      exact ⟨⟨hdefDef, hrec.1⟩, hrec.2⟩
  | @ite Δ cond t e hcond _ _ iht ihe =>
      intro hsubBase hsym hσ hΓc hagBase hagree hres hφ
      simp only [Relation.ofExpr, Formula.iteBool, Formula.eval, Term.eval,
        Const.denote] at hφ
      have hcondEval : Term.eval ρrel cond = Term.eval ρdef (cond.subst σ) :=
        eval_substAgree hagree hcond hσ hΔbase
      by_cases hc1 : Term.eval ρrel cond = true
      · have hc2 : Term.eval ρdef (cond.subst σ) = true := by rw [← hcondEval]; exact hc1
        have hrec := iht hsubBase hsym hσ hΓc hagBase hagree hres (hφ.1 hc1)
        simp [ofExpr, Formula.iteBool, Formula.eval, Term.eval, Const.denote,
          hc2, hrec.1, hrec.2]
      · have hc1' : Term.eval ρrel cond = false := by
          cases h : Term.eval ρrel cond <;> simp_all
        have hc2 : Term.eval ρdef (cond.subst σ) = false := by rw [← hcondEval]; exact hc1'
        have hrec := ihe hsubBase hsym hσ hΓc hagBase hagree hres (hφ.2 hc1')
        simp [ofExpr, Formula.iteBool, Formula.eval, Term.eval, Const.denote,
          hc2, hrec.1, hrec.2]

/-! ## Transport between split and combined environments -/

theorem defval_eval_transport_from_relSplit_final {primitives : PrimEncodings}
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} {R : ValRel}
    {D : Srt.value.denote → Prop} {F : Srt.value.denote → Srt.value.denote}
    (hlaw : primitives.Lawful)
    (henc : splitBody primitives Γ Δ f fn x res e = .ok body)
    (hΓdef : Γ.splitWfIn Δ) (hΔ : Δ.wf) (hheadFresh : HeadFresh Δ fn x res)
    (vin vout : Srt.value.denote) :
    body.defined.eval (((relSplitEnv ρ fn R D F).updateConst .value x vin).updateConst .value res vout) ∧
        body.value.eval (((relSplitEnv ρ fn R D F).updateConst .value x vin).updateConst .value res vout) =
          vout →
      body.defined.eval ((splitEnv ρ fn D F).updateConst .value x vin) ∧
        body.value.eval ((splitEnv ρ fn D F).updateConst .value x vin) =
          vout := by
  intro hsplit
  have hbody : body.wfIn (defvalBodySig Δ fn x) :=
    splitBody_wfIn_defvalBodySig hlaw hΔ hΓdef hheadFresh henc
  have hag := splitEnv_relSplitEnv_agreeOn_defvalBodySig
    (ρ := ρ) (R := R) (D := D) (F := F) hheadFresh vin vout
  exact ⟨(Formula.eval_env_agree hbody.2 hag).mpr hsplit.1,
    (Term.eval_env_agree hbody.1 hag).trans hsplit.2⟩

/-- A relational edge through the semantic body determines the split
definedness predicate and the value computed by the split body. This is one
half of the relation/split fixpoint equivalence. -/
theorem semrel_complete {primitives : PrimEncodings}
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (hlaw : primitives.Lawful)
    (henc : splitBody primitives Γ Δ f fn x res e = .ok body)
    (hΓ : Γ.splitCompatible ρ)
    (hΓwf : Γ.wfIn Δ)
    (hΔ : Δ.wf) (hheadFresh : HeadFresh Δ fn x res)
    (hρdet : Relation.BinaryRelDet Γ ρ ρ)
    (vin vout : Srt.value.denote) :
    semrel primitives Γ Δ ρ f fn x res e vin vout →
      semdef primitives Γ Δ ρ f fn x res e body vin ∧
      body.value.eval
        ((defInterpEnv primitives Γ Δ ρ f fn x res e body).updateConst .value x vin) =
      vout := by
  intro hrel
  obtain ⟨c, rfl, hrelEnc, hcWf⟩ := splitBody_witness hlaw hΔ hheadFresh henc
  have hΔbody : (bodySig Δ fn x).wf := bodySig_wf_of_headFresh hΔ hheadFresh
  set φ := Relation.ofExpr res c
  let R : ValRel := semrel primitives Γ Δ ρ f fn x res e
  let D : Srt.value.denote → Prop := semdef primitives Γ Δ ρ f fn x res e (ofExpr .id c)
  let F : Srt.value.denote → Srt.value.denote := semFunc R
  let S : ValRel := fun x y => D x ∧ F x = y
  have hrel_eq :
      R = RelationFix.lfp (Relation.semanticBody Formula.sem ρ fn x res φ) := by
    simp [R, Relation.semrel, Relation.semanticFixpoint, hrelEnc]
  have hpre :
      RelationFix.le (Relation.semanticBody Formula.sem ρ fn x res φ S) S := by
    intro vin vout hbody
    let ρS := relSplitEnv ρ fn S D F
    have hΓS : (Relation.ctx Γ f fn).splitComplete ρS :=
      splitComplete_cons_relSplitEnv
        (FunCtx.splitComplete_of_compatible hΓ)
        (freshFn_of_headFresh hΓwf hheadFresh)
        (fun _ _ h => h)
    have hbodyρS :
        φ.eval ((ρS.updateConst .value x vin).updateConst .value res vout) := by
      simpa [ρS] using
        (rel_body_eval_iff (D := D) (F := F) hlaw hΓwf.rel hΔ hheadFresh hrelEnc vin vout).mpr hbody
    have hsplitρS :
        (ofExpr .id c).defined.eval
            ((ρS.updateConst .value x vin).updateConst .value res vout) ∧
          (ofExpr .id c).value.eval
            ((ρS.updateConst .value x vin).updateConst .value res vout) = vout := by
      have hrec :=
        ofExpr_complete (ctx_splitWfIn_bodySig_of_headFresh hΓwf.split hheadFresh) hΔbody
          hcWf (by simp [bodyAvoid]) (Signature.Subset.refl _)
          (Signature.SymbolSubset.refl _)
          (Subst.id_wfIn (fun _ h => h) hΔbody)
          (FunCtx.splitComplete_updateConst
            (FunCtx.splitComplete_updateConst hΓS .value x vin) .value res vout)
          Env.agreeOn_refl substAgree_refl rfl hbodyρS
      simpa [Env.lookupConst_updateConst_same] using hrec
    have hsplit :
        (ofExpr .id c).defined.eval ((splitEnv ρ fn D F).updateConst .value x vin) ∧
          (ofExpr .id c).value.eval ((splitEnv ρ fn D F).updateConst .value x vin) =
            vout := by
      exact defval_eval_transport_from_relSplit_final hlaw henc hΓwf.split hΔ hheadFresh
        vin vout hsplitρS
    have hdefined : D vin := by
      exact (semdef_unfold_of_split (ρ := ρ) (x := x) (res := res) henc vin).mpr
        (by simpa [D, F, defBody, defEnv] using hsplit.1)
    have hfun : F vin = vout := by
      simpa [D, F, R, defInterpEnv] using
        semFunc_eq_of_semdef_value hlaw henc hΓ hΓwf hΔ hheadFresh hρdet
          vin vout (by simpa [D] using hdefined)
          (by simpa [D, F, R, defInterpEnv] using hsplit.2)
    exact ⟨hdefined, hfun⟩
  have hlfp :
      RelationFix.lfp (Relation.semanticBody Formula.sem ρ fn x res φ) vin vout := by
    simpa [R, hrel_eq] using hrel
  have hS : S vin vout := RelationFix.lfp_le_of_prefixed hpre vin vout hlfp
  have hdefined : D vin := hS.1
  let vbody :=
    (ofExpr .id c).value.eval
      ((defInterpEnv primitives Γ Δ ρ f fn x res e (ofExpr .id c)).updateConst .value x vin)
  have hbody_eq_fun : vbody = F vin := by
    have hfun : F vin = vbody := by
      simpa [D, F, R, defInterpEnv, vbody] using
        semFunc_eq_of_semdef_value hlaw henc hΓ hΓwf hΔ hheadFresh hρdet
          vin vbody (by simpa [D] using hdefined) rfl
    exact hfun.symm
  exact ⟨by simpa [D] using hdefined, by simpa [vbody] using hbody_eq_fun.trans hS.2⟩

end Skolemize
end Verifier.RelationalEncoding
