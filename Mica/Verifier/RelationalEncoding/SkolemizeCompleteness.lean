-- SUMMARY: Completeness of Skolemization: relational encoding implies split definedness/value.
import Mica.Verifier.RelationalEncoding.SkolemizeSoundness

namespace Verifier.RelationalEncoding
open Relation

namespace Skolemize

/-! ## The completeness binary relation

`CompleteBinary Γ P res` is the relation fed to the generic
`encodeWith_bind_binary` to transfer information *from* the relational
encoding *to* the split defined/value encoding — the opposite direction of
`SoundBinary`. As with soundness, `ρ₁` interprets the relational carrier and
`ρ₂` the `DefVal` carrier, and the continuation contract is handled
generically by `EncoderContSpec`. -/
def CompleteBinary (Γ : FunCtx) (P : Env → Srt.value.denote → Prop) (res : String) :
    Signature → Signature → Env → Env → Rel → Except String DefVal → Prop :=
  fun Δ₁ Δ₂ ρ₁ ρ₂ m d =>
    ∀ (Δ : Signature) (s : NameSupply) (φ : Formula) (body : DefVal),
      Δ₂.Subset Δ₁ → Δ₂.wf → Γ.splitWfIn Δ₂ →
      Δ₁.Subset Δ → Δ.wf → s.Covers Δ →
      (⟨res, .value⟩ : Var) ∈ Δ.vars →
      m s = .ok φ →
      d = .ok body →
      body.wfIn Δ₂ →
      Γ.splitComplete ρ₁ →
      Env.agreeOn Δ₂ ρ₁ ρ₂ →
      ρ₁.lookupConst .value res = ρ₂.lookupConst .value res →
      φ.eval ρ₁ →
      body.defined.eval ρ₂ ∧ P ρ₂ (body.value.eval ρ₂)

/-- Completeness binary case for conditionals. The relational formula selects
a branch, and the corresponding branch binary reconstructs the split
definedness/value facts. -/
theorem CompleteBinary.ite
    {Γ : FunCtx} {P : Env → Srt.value.denote → Prop} {res : String}
    {Δ₁ Δ₂ : Signature} {ρ₁ ρ₂ : Env}
    {c₁ c₂ : Term .bool} {t₁ e₁ : Rel} {t₂ e₂ : Except String DefVal}
    (hceval : Term.eval ρ₁ c₁ = Term.eval ρ₂ c₂)
    (ht : CompleteBinary Γ P res Δ₁ Δ₂ ρ₁ ρ₂ t₁ t₂)
    (he : CompleteBinary Γ P res Δ₁ Δ₂ ρ₁ ρ₂ e₁ e₂) :
  CompleteBinary Γ P res Δ₁ Δ₂ ρ₁ ρ₂
      (Relation.encoderOps.ite c₁ t₁ e₁) (encoderOps.ite c₂ t₂ e₂) := by
  intro Δ s φ body hsub21 hΔ₂ hΓdef hsub1 hΔ hcov hres hrun hd hbody hΓc hag hres_eq hφ
  obtain ⟨dt, de, ht₂, he₂, rfl⟩ := encoderOps_ite_ok hd
  obtain ⟨φt, φe, ht₁, he₁, rfl⟩ := relation_encoderOps_ite_ok hrun
  have hdtwf : dt.wfIn Δ₂ := DefVal.wfIn_of_ite_then hbody
  have hdewf : de.wfIn Δ₂ := DefVal.wfIn_of_ite_else hbody
  simp only [Formula.iteBool, Formula.eval, Term.eval, Const.denote] at hφ
  by_cases hc1 : c₁.eval ρ₁ = true
  · have hc2 : c₂.eval ρ₂ = true := by rw [← hceval]; exact hc1
    have hres' := ht Δ s φt dt hsub21 hΔ₂ hΓdef hsub1 hΔ hcov hres ht₁ ht₂
      hdtwf hΓc hag hres_eq (hφ.1 hc1)
    simp [DefVal.ite, Formula.iteBool, Formula.eval, Term.eval, Const.denote,
      hc2, hres'.1, hres'.2]
  · have hc1' : c₁.eval ρ₁ = false := by
      cases h : c₁.eval ρ₁ <;> simp_all
    have hc2 : c₂.eval ρ₂ = false := by rw [← hceval]; exact hc1'
    have hres' := he Δ s φe de hsub21 hΔ₂ hΓdef hsub1 hΔ hcov hres he₁ he₂
      hdewf hΓc hag hres_eq (hφ.2 hc1')
    simp [DefVal.ite, Formula.iteBool, Formula.eval, Term.eval, Const.denote,
      hc2, hres'.1, hres'.2]

/-- Completeness binary case for calls. A relational call edge is converted
back into split definedness/value facts using `Γ.splitComplete`, then the
continuation binary handles the fresh result variable. -/
theorem CompleteBinary.call
    {Γ : FunCtx} {P : Env → Srt.value.denote → Prop} {res : String}
    {Δ₁ Δ₂ : Signature} {ρ₁ ρ₂ : Env}
    {f : TinyML.Var} {fn : SpecFn} {arg₁ arg₂ : Term .value}
    {k₁ : Term .value → Rel} {k₂ : Term .value → Except String DefVal}
    (hmem : (f, fn) ∈ Γ)
    (harg₁ : arg₁.wfIn Δ₁) (harg₂ : arg₂.wfIn Δ₂)
    (hargeval : Term.eval ρ₁ arg₁ = Term.eval ρ₂ arg₂)
    (hk : EncoderContSpec (CompleteBinary Γ P res) Δ₁ Δ₂ ρ₁ ρ₂ k₁ k₂) :
    CompleteBinary Γ P res Δ₁ Δ₂ ρ₁ ρ₂
      (Relation.encoderOps.call fn arg₁ k₁) (encoderOps.call fn arg₂ k₂) := by
  intro Δ s φ body hsub21 hΔ₂ hΓdef hsub1 hΔ hcov hres hrun hd hbody hΓc hag hres_eq hφ
  -- DefVal side: d = encoderOps.call fn arg₂ k₂ = DefVal.bind (DefVal.call fn arg₂) k₂
  simp only [encoderOps] at hd
  obtain ⟨n, hkn, hbodyeq⟩ := DefVal.bind_ok hd
  simp only [DefVal.call] at hkn
  subst hbodyeq
  obtain ⟨hnval_wf, hisdef_wf, hndef_wf⟩ := hbody
  have hnwf : n.wfIn Δ₂ := ⟨hnval_wf, hndef_wf⟩
  have hfun_mem : fn.func ∈ Δ₂.unary := (hΓdef f fn hmem).1
  have hdef_mem : fn.defined ∈ Δ₂.unaryRel := (hΓdef f fn hmem).2
  -- Rel side: m = Rel.call fn arg₁ k₁
  simp only [Relation.encoderOps, Rel.call] at hrun
  let ctx := freshValueCtx s hΔ hcov
  have hfreshΔ₁ : ctx.r ∉ Δ₁.allNames := ctx.fresh_of_subset hsub1
  have hfreshΔ₂ : ctx.r ∉ Δ₂.allNames := ctx.fresh_of_subset (hsub21.trans hsub1)
  have hr_ne_res : ctx.r ≠ res := ctx.ne_of_var_mem hres
  cases hk₁run : k₁ (.var .value ctx.r) ctx.s' with
  | error msg =>
    rw [← ctx.hr, ← ctx.hs', hk₁run] at hrun
    simp [Bind.bind, Except.bind] at hrun
  | ok φ' =>
    rw [← ctx.hr, ← ctx.hs', hk₁run] at hrun
    simp only [Bind.bind, Except.bind, Except.ok.injEq] at hrun
    subst hrun
    -- the relational call edge supplies the witness
    simp only [Formula.eval] at hφ
    obtain ⟨w, hcall, hbody'⟩ := hφ
    have hargΔ : arg₁.wfIn Δ := Term.wfIn_mono _ harg₁ hsub1 hΔ
    have hargeval' : arg₁.eval (ρ₁.updateConst .value ctx.r w) = arg₁.eval ρ₁ :=
      ctx.eval_update_fresh hargΔ
    have hcall' : ρ₁.binaryRel .value .value fn.relName (arg₁.eval ρ₁) w := by
      simpa [SpecFn.rel, Formula.eval, BinPred.eval, Term.eval,
        Env.updateConst_binaryRel, Env.lookupConst_updateConst_same, hargeval']
        using hcall
    have hsplit := hΓc f fn hmem (arg₁.eval ρ₁) w hcall'
    have hunary_eq : ρ₁.unary .value .value (fn.funcName) =
        ρ₂.unary .value .value (fn.funcName) :=
      hag.2.2.1 (fn.func) hfun_mem
    have hunaryRel_eq : ρ₁.unaryRel .value (fn.defName) =
        ρ₂.unaryRel .value (fn.defName) :=
      hag.2.2.2.2.1 (fn.defined) hdef_mem
    have hw_eq : w = ρ₂.unary .value .value (fn.funcName) (arg₂.eval ρ₂) := by
      rw [← hsplit.2, congrFun hunary_eq (arg₁.eval ρ₁), hargeval]
    have hisdef_ev : (fn.isDefined arg₂).eval ρ₂ := by
      have hu := hsplit.1
      rw [congrFun hunaryRel_eq (arg₁.eval ρ₁), hargeval] at hu
      simpa [SpecFn.isDefined, Formula.eval, UnPred.eval] using hu
    -- recurse through the continuation
    have hsplit_upd : Γ.splitComplete (ρ₁.updateConst .value ctx.r w) :=
      FunCtx.splitComplete_updateConst hΓc .value ctx.r w
    have hag_upd : Env.agreeOn Δ₂ (ρ₁.updateConst .value ctx.r w) ρ₂ :=
      Env.agreeOn_trans
        (Env.agreeOn_symm
          (Env.agreeOn_update_fresh_const (c := ⟨ctx.r, .value⟩) hfreshΔ₂))
        hag
    have hcallwf : (fn.call arg₂).wfIn Δ₂ :=
      SpecFn.call_wfIn hfun_mem hΔ₂ harg₂
    have hagree₁ : Env.agreeOn Δ₁ ρ₁ (ρ₁.updateConst .value ctx.r w) :=
      Env.agreeOn_update_fresh_const (c := ⟨ctx.r, .value⟩) hfreshΔ₁
    have heval_eq :
        Term.eval (ρ₁.updateConst .value ctx.r w) (Term.var .value ctx.r) =
          Term.eval ρ₂ (fn.call arg₂) := by
      simp [Term.eval, SpecFn.call, UnOp.eval, Env.lookupConst_updateConst_same, hw_eq]
    have hcont :=
      hk (hsub1.trans ctx.subset) (Signature.Subset.refl Δ₂) ctx.wf hΔ₂
        hagree₁ Env.agreeOn_refl
        (Term.var .value ctx.r) (fn.call arg₂) ctx.var_wf hcallwf heval_eq
    have hrec := hcont ctx.Δ' ctx.s' φ' n
      (hsub21.trans (hsub1.trans ctx.subset)) hΔ₂ hΓdef
      (Signature.Subset.refl ctx.Δ') ctx.wf ctx.covers
      (ctx.subset.vars _ hres) hk₁run hkn hnwf hsplit_upd hag_upd
      (by rw [Env.lookupConst_updateConst_ne hr_ne_res.symm]; exact hres_eq)
      hbody'
    refine ⟨?_, hrec.2⟩
    simp only [DefVal.call, Formula.eval]
    exact ⟨hisdef_ev, hrec.1⟩

/-- Operation-level binary data: the completeness relation is preserved by the
encoder operations. As for soundness, `unop`/`binop` are handled generically
by `encodeWith_bind_binary`, so only `call`, `ite` and `error` appear here. -/
def completeBinary_ops (Γ : FunCtx) (P : Env → Srt.value.denote → Prop) (res : String) :
    EncoderOpsBinary Γ Relation.encoderOps encoderOps (CompleteBinary Γ P res) where
  error_binary := by
    intro _Δ₁ _Δ₂ _ρ₁ _ρ₂ msg Δ s φ body _ _ _ _ _ _ _ _ hd _ _ _ _ _
    simp [encoderOps] at hd
  ite_binary := CompleteBinary.ite
  call_binary := CompleteBinary.call

/-- Pinned-result completeness, obtained directly from a successful paired
encoding of the same expression: the relational formula implies the split
body's definedness and value. -/
theorem encodeWith_kEq_complete {Γ : FunCtx} {Δenc Δrun : Signature}
    {srun : NameSupply} {ρ : Env}
    {e : Typed.Expr} {body : DefVal}
    {res : String} {φ : Formula}
    (hrun : encodeWith Relation.encoderOps Γ (VarEnv.ofSignature Δenc) e (Relation.kEq res) srun = .ok φ)
    (hdef : encode Γ Δenc e = .ok body)
    (hΓ : Γ.splitComplete ρ) (hΓdef : Γ.splitWfIn Δenc)
    (hΔenc : Δenc.wf) (hΔrun : Δrun.wf) (hcov : srun.Covers Δrun)
    (hsub : Δenc.Subset Δrun)
    (hbody : body.wfIn Δenc)
    (hres : (⟨res, .value⟩ : Var) ∈ Δrun.vars) :
    φ.eval ρ →
      body.defined.eval ρ ∧ body.value.eval ρ = (Term.var .value res).eval ρ := by
  intro hφ
  have hbinary :
      CompleteBinary Γ (fun ρ v => v = (Term.var .value res).eval ρ) res Δenc Δenc ρ ρ
        (encodeWith Relation.encoderOps Γ (VarEnv.ofSignature Δenc) e (Relation.kEq res))
        (encodeWith encoderOps Γ (VarEnv.ofSignature Δenc) e (fun v => .ok (DefVal.pure v))) := by
    refine encodeWith_bind_binary (δ₁ := VarEnv.ofSignature Δenc)
      (δ₂ := VarEnv.ofSignature Δenc) (completeBinary_ops Γ _ res) e
      (Signature.Subset.refl _) (Signature.Subset.refl _) hΔenc hΔenc
      ?_ ?_
    · exact varEnv_ofSignature_agree_self hΔenc
    -- EncoderContSpec for the `(kEq res, pure)` continuation pair
    intro Δ₁' Δ₂' ρ₁' ρ₂' _hs₁ _hs₂ _hw₁ _hw₂ _ha₁ _ha₂ v₁ v₂ _hv₁ _hv₂ heval Δ s φ' body'
      _ _ _ _ _ _ _ hrun' hd' _ _ _ hres_eq' hφ'
    simp only [Relation.kEq, Except.ok.injEq] at hrun'
    simp only [Except.ok.injEq] at hd'
    subst hd'
    subst hrun'
    simp only [DefVal.pure, Formula.eval, Term.eval] at hφ' ⊢
    refine ⟨trivial, ?_⟩
    rw [← heval, hφ', hres_eq']
  exact hbinary Δrun srun φ body (Signature.Subset.refl _) hΔenc hΓdef hsub hΔrun hcov
    hres hrun hdef hbody hΓ Env.agreeOn_refl rfl hφ

/-! ## Transport between split and combined environments -/

theorem defval_eval_transport_from_relSplit_final
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} {R : ValRel}
    {D : Srt.value.denote → Prop} {F : Srt.value.denote → Srt.value.denote}
    (henc : encodeBody Γ Δ f fn x res e = .ok body)
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
    encodeBody_wfIn_defvalBodySig hΔ hΓdef hheadFresh henc
  have hag := splitEnv_relSplitEnv_agreeOn_defvalBodySig
    (ρ := ρ) (R := R) (D := D) (F := F) hheadFresh vin vout
  exact ⟨(Formula.eval_env_agree hbody.2 hag).mpr hsplit.1,
    (Term.eval_env_agree hbody.1 hag).trans hsplit.2⟩

/-- A relational edge through the semantic body determines the split
definedness predicate and the value computed by the split body. This is one
half of the relation/split fixpoint equivalence. -/
theorem semrel_complete
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (henc : encodeBody Γ Δ f fn x res e = .ok body)
    (hΓ : Γ.splitCompatible ρ)
    (hΓwf : Γ.wfIn Δ)
    (hΔ : Δ.wf) (hheadFresh : HeadFresh Δ fn x res)
    (hρdet : Relation.BinaryRelDet Γ ρ ρ)
    (vin vout : Srt.value.denote) :
    semrel Γ Δ ρ f fn x res e vin vout →
      semdef Γ Δ ρ f fn x res e body vin ∧
      body.value.eval
        ((defInterpEnv Γ Δ ρ f fn x res e body).updateConst .value x vin) =
      vout := by
  intro hrel
  obtain ⟨φ, hrelEnc⟩ := encodeBody_relEncodeBody hΔ hΓwf.split hheadFresh henc
  set m := encodeWith Relation.encoderOps (Relation.ctx Γ f fn)
      (VarEnv.ofSignature (bodySig Δ fn x)) e (Relation.kEq res) with hm_def
  have hrun : m (relBodySupply Δ fn x res) = .ok φ := by
    have hvars :
        VarEnv.ofSignature (bodySig Δ fn x) =
          VarEnv.ofSignature (Relation.bodySig Δ fn x) := by
      simp [VarEnv.ofSignature, bodySig, Relation.bodySig, Signature.declVar,
        Signature.addBinaryRel, Signature.addUnary, Signature.addUnaryRel,
        Signature.remove, Signature.addVar]
    rw [hm_def, hvars]
    simpa [Relation.relEncodeBody] using hrelEnc
  have hbodyWf_body : body.wfIn (bodySig Δ fn x) :=
    encode_wfIn e (bodySig_wf_of_headFresh hΔ hheadFresh)
      (ctx_splitWfIn_bodySig_of_headFresh hΓwf.split hheadFresh) (encodeBody_def_bodySig henc)
  have hres_mem : (⟨res, .value⟩ : Var) ∈ (sig Δ fn x res).vars := by
    unfold sig
    exact Signature.var_mem_declVar _ ⟨res, .value⟩
  let R : ValRel := semrel Γ Δ ρ f fn x res e
  let D : Srt.value.denote → Prop := semdef Γ Δ ρ f fn x res e body
  let F : Srt.value.denote → Srt.value.denote := semFunc R
  let S : ValRel := fun x y => D x ∧ F x = y
  have hrelEncR : Relation.relEncodeBody Γ Δ f fn x res e = .ok φ := by
    exact hrelEnc
  have hrel_eq :
      R = Fix.lfp (Relation.semanticBody Formula.sem ρ fn x res φ) := by
    simp [R, Relation.semrel, Relation.semanticFixpoint, hrelEncR]
  have hpre :
      Fix.le (Relation.semanticBody Formula.sem ρ fn x res φ S) S := by
    intro vin vout hbody
    let ρS := relSplitEnv ρ fn S D F
    have hΓS : (Relation.ctx Γ f fn).splitComplete ρS := by
      intro g fn' hmem a b hcall
      cases hmem with
      | head =>
          have hhead :
              ρS.binaryRel .value .value fn.relName a b →
                ρS.unaryRel .value (fn.defName) a ∧
                  ρS.unary .value .value (fn.funcName) a = b := by
            simp [ρS, relSplitEnv, S, Env.updateBinaryRel, Env.updateUnary,
              Env.updateUnaryRel]
          exact hhead hcall
      | tail _ htail =>
          have hnames := freshFn_of_headFresh hΓwf hheadFresh g fn' htail
          have htailComplete :
              ρS.binaryRel .value .value fn'.relName a b →
                ρS.unaryRel .value (fn'.defName) a ∧
                  ρS.unary .value .value (fn'.funcName) a = b := by
            simpa [ρS, relSplitEnv, Env.updateBinaryRel, Env.updateUnary,
              Env.updateUnaryRel, hnames.1, hnames.2.1, hnames.2.2]
              using (hΓ g fn' htail a b).mp
          exact htailComplete hcall
    have hbodyρS :
        φ.eval ((ρS.updateConst .value x vin).updateConst .value res vout) := by
      simpa [ρS] using
        (rel_body_eval_iff (D := D) (F := F) hΓwf.rel hΔ hheadFresh hrelEnc vin vout).mpr hbody
    have hproof :=
      encodeWith_kEq_complete (Γ := Relation.ctx Γ f fn)
        (Δenc := bodySig Δ fn x) (Δrun := sig Δ fn x res)
        (srun := relBodySupply Δ fn x res)
        (ρ := (ρS.updateConst .value x vin).updateConst .value res vout)
        (e := e) (body := body) (res := res) (φ := φ)
        hrun (encodeBody_def_bodySig henc)
        (FunCtx.splitComplete_updateConst
          (FunCtx.splitComplete_updateConst hΓS .value x vin) .value res vout)
        (ctx_splitWfIn_bodySig_of_headFresh hΓwf.split hheadFresh)
        (bodySig_wf_of_headFresh hΔ hheadFresh)
        (sig_wf_of_headFresh hΔ hheadFresh)
        (relBodySupply_covers_sig Δ fn x res)
        (bodySig_subset_sig_of_headFresh hheadFresh)
        hbodyWf_body hres_mem
    have hsplitρS :
        body.defined.eval ((ρS.updateConst .value x vin).updateConst .value res vout) ∧
          body.value.eval ((ρS.updateConst .value x vin).updateConst .value res vout) =
            vout := by
      simpa [Term.eval, Env.lookupConst_updateConst_same] using hproof hbodyρS
    have hsplit :
        body.defined.eval ((splitEnv ρ fn D F).updateConst .value x vin) ∧
          body.value.eval ((splitEnv ρ fn D F).updateConst .value x vin) =
            vout := by
      exact defval_eval_transport_from_relSplit_final henc hΓwf.split hΔ hheadFresh
        vin vout hsplitρS
    have hdefined : D vin := by
      exact (semdef_unfold_of_encode (ρ := ρ) (x := x) (res := res) henc vin).mpr
        (by simpa [D, F, defBody, defEnv] using hsplit.1)
    have hfun : F vin = vout := by
      simpa [D, F, R, defInterpEnv] using
        semFunc_eq_of_semdef_value henc hΓ hΓwf hΔ hheadFresh hρdet
          vin vout (by simpa [D] using hdefined)
          (by simpa [D, F, R, defInterpEnv] using hsplit.2)
    exact ⟨hdefined, hfun⟩
  have hlfp :
      Fix.lfp (Relation.semanticBody Formula.sem ρ fn x res φ) vin vout := by
    simpa [R, hrel_eq] using hrel
  have hS : S vin vout := Fix.lfp_le_of_prefixed hpre vin vout hlfp
  have hdefined : D vin := hS.1
  let vbody :=
    body.value.eval
      ((defInterpEnv Γ Δ ρ f fn x res e body).updateConst .value x vin)
  have hbody_eq_fun : vbody = F vin := by
    have hfun : F vin = vbody := by
      simpa [D, F, R, defInterpEnv, vbody] using
        semFunc_eq_of_semdef_value henc hΓ hΓwf hΔ hheadFresh hρdet
          vin vbody (by simpa [D] using hdefined) rfl
    exact hfun.symm
  exact ⟨by simpa [D] using hdefined, by simpa [vbody] using hbody_eq_fun.trans hS.2⟩

end Skolemize
end Verifier.RelationalEncoding
