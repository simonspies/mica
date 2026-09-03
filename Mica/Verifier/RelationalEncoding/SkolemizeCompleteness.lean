-- SUMMARY: Completeness of Skolemization: relational encoding implies split definedness/value.
import Mica.Verifier.RelationalEncoding.SkolemizeSoundness

namespace Verifier.RelationalEncoding
open Relation

namespace Skolemize

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
  set φ := Relation.ofExpr res c
  let R : ValRel := semrel primitives Γ Δ ρ f fn x res e
  let D : Srt.value.denote → Prop := semdef primitives Γ Δ ρ f fn x res e (ofExpr .id c)
  let F : Srt.value.denote → Srt.value.denote := semFunc R
  have hrel_eq :
      R = RelationFix.lfp (Relation.semanticBody Formula.sem ρ fn x res φ) := by
    simp [R, Relation.semrel, Relation.semanticFixpoint, hrelEnc]
  -- The graph of the split presentation is a prefixed point of the relational
  -- body, so it contains the relational fixpoint.
  have hpre :
      RelationFix.le (Relation.semanticBody Formula.sem ρ fn x res φ (graph D F))
        (graph D F) := by
    intro vin vout hbody
    let ρS := splitEnv ρ fn (graph D F) D F
    have hΓS : (Relation.ctx Γ f fn).splitCompatible ρS :=
      splitCompatible_cons_splitEnv hΓ (freshFn_of_headFresh hΓwf hheadFresh)
    have hbodyρS :
        φ.eval ((ρS.updateConst .value x vin).updateConst .value res vout) := by
      simpa [ρS] using
        (rel_body_eval_iff (D := D) (F := F) hlaw hΓwf.rel hΔ hheadFresh hrelEnc
          vin vout).mpr hbody
    have hres := defval_eval_updateConst_res (ρ := ρ) (D := D) (F := F)
      hlaw hΔ hΓwf.split hheadFresh henc vin vout
    have hsplit :
        (ofExpr .id c).defined.eval (defEnv ρ fn x D F vin) ∧
          (ofExpr .id c).value.eval (defEnv ρ fn x D F vin) = vout :=
      have hpinned := (body_eval_iff hΓwf.split hΔ hheadFresh hcWf hΓS vin vout).mp hbodyρS
      ⟨hres.1.mp hpinned.1, hres.2.symm.trans hpinned.2⟩
    have hdefined : D vin :=
      (semdef_unfold_of_split (ρ := ρ) (x := x) (res := res) henc vin).mpr
        (by simpa [D, F, defBody, defEnv] using hsplit.1)
    have hfun : F vin = vout := by
      simpa [D, F, R, defInterpEnv] using
        semFunc_eq_of_semdef_value hlaw henc hΓ hΓwf hΔ hheadFresh hρdet
          vin vout (by simpa [D] using hdefined)
          (by simpa [D, F, R, defInterpEnv] using hsplit.2)
    exact ⟨hdefined, hfun⟩
  have hS : graph D F vin vout :=
    RelationFix.lfp_le_of_prefixed hpre vin vout (by simpa [R, hrel_eq] using hrel)
  have hdefined : D vin := hS.1
  let vbody :=
    (ofExpr .id c).value.eval
      ((defInterpEnv primitives Γ Δ ρ f fn x res e (ofExpr .id c)).updateConst .value x vin)
  have hbody_eq_fun : vbody = F vin :=
    (by
      simpa [D, F, R, defInterpEnv, vbody] using
        semFunc_eq_of_semdef_value hlaw henc hΓ hΓwf hΔ hheadFresh hρdet
          vin vbody (by simpa [D] using hdefined) rfl : F vin = vbody).symm
  exact ⟨by simpa [D] using hdefined, by simpa [vbody] using hbody_eq_fun.trans hS.2⟩

end Skolemize
end Verifier.RelationalEncoding
