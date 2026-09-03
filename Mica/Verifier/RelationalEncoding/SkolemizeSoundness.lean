-- SUMMARY: Soundness of Skolemization: split definedness/value implies the relational encoding.
import Mica.Verifier.RelationalEncoding.SkolemizeCommon

namespace Verifier.RelationalEncoding
open Relation

namespace Skolemize

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
  obtain ⟨c, rfl, hrelEnc, hcWf⟩ := splitBody_witness hlaw hΔ hheadFresh henc
  set φ := Relation.ofExpr res c
  let R : ValRel := semrel primitives Γ Δ ρ f fn x res e
  let F : Srt.value.denote → Srt.value.denote := semFunc R
  let D : Srt.value.denote → Prop := semdef primitives Γ Δ ρ f fn x res e (ofExpr .id c)
  have hmonoBody : RelationFix.Mono (Relation.semanticBody Formula.sem ρ fn x res φ) :=
    Relation.semanticBody_mono_of_semanticMono (Relation.ofExpr_mono res c)
  have hrel_eq :
      R = RelationFix.lfp (Relation.semanticBody Formula.sem ρ fn x res φ) := by
    simp [R, Relation.semrel, Relation.semanticFixpoint, hrelEnc]
  have hpreR :
      RelationFix.le (Relation.semanticBody Formula.sem ρ fn x res φ R) R := by
    rw [hrel_eq]
    exact RelationFix.lfp_prefixed hmonoBody
  -- Reading the body at the graph of a split candidate contained in `R` turns a
  -- split definedness obligation into a relational edge.
  have hstep : ∀ (P : Srt.value.denote → Prop) (vin' : Srt.value.denote),
      RelationFix.le (graph P F) R → defBody ρ fn x (ofExpr .id c) F P vin' →
      R vin' ((ofExpr .id c).value.eval (defEnv ρ fn x P F vin')) := by
    intro P vin' hle hdefBody
    let vbody := (ofExpr .id c).value.eval (defEnv ρ fn x P F vin')
    let ρP := relSplitEnv ρ fn (graph P F) P F
    have hΓP : (Relation.ctx Γ f fn).splitCompatible ρP :=
      splitCompatible_cons_relSplitEnv hΓ (freshFn_of_headFresh hΓwf hheadFresh)
    have hsplitP :
        (ofExpr .id c).defined.eval
            ((ρP.updateConst .value x vin').updateConst .value res vbody) ∧
          (ofExpr .id c).value.eval
            ((ρP.updateConst .value x vin').updateConst .value res vbody) = vbody :=
      defval_eval_transport_to_relSplit_domain (R := graph P F) (P := P)
        hlaw henc hΓwf.split hΔ hheadFresh vin' hdefBody
    have hbodyGraph :
        Relation.semanticBody Formula.sem ρ fn x res φ (graph P F) vin' vbody :=
      (rel_body_eval_iff (D := P) (F := F) hlaw hΓwf.rel hΔ hheadFresh hrelEnc
        vin' vbody).mp
        ((body_eval_iff hΓwf.split hΔ hheadFresh hcWf hΓP vin' vbody).mpr hsplitP)
    exact hpreR vin' vbody (hmonoBody hle vin' vbody hbodyGraph)
  have hdomain : PredicateFix.le D (semDefined R) := by
    unfold D semdef
    apply PredicateFix.lfp_le_of_prefixed
    intro vin' hdefBody
    exact ⟨_, hstep (semDefined R) vin' (graph_le (fun _ h => h)) hdefBody⟩
  have hdefBody : defBody ρ fn x (ofExpr .id c) F D vin := by
    simpa [D, F] using
      (semdef_unfold_of_split (ρ := ρ) (x := x) (res := res) henc vin).mp hsem
  have hvalEq : (ofExpr .id c).value.eval (defEnv ρ fn x D F vin) = vout := by
    simpa [D, F, R, defInterpEnv, defEnv] using hval
  rw [← hvalEq]
  exact hstep D vin (graph_le hdomain) hdefBody

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
