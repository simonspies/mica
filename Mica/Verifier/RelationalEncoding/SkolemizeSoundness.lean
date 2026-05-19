-- SUMMARY: Soundness of Skolemization: split definedness/value implies the relational encoding.
import Mica.Verifier.RelationalEncoding.SkolemizeCommon

namespace Verifier.RelationalEncoding
open Relation

namespace Skolemize

/-! ## The soundness binary relation

`SoundBinary Γ P res` is the relation fed to the generic
`encodeWith_bind_binary` to transfer information *from* the split
defined/value encoding *to* the relational encoding. It is the soundness
analogue of the old `Soundness` predicate, with the two interpreting
environments threaded explicitly: `ρ₁` interprets the relational carrier and
`ρ₂` the `DefVal` carrier. The continuation contract that used to be packaged
as `RelContSemSoundness`/`BindSpec` is now handled generically by
`EncoderContSpec`.

`P` is an abstract value postcondition; `res` is the pinned result variable
used by the top-level `kEq` continuation. -/
def SoundBinary (Γ : FunCtx) (P : Env → Srt.value.denote → Prop) (res : String) :
    Signature → Signature → Env → Env → Rel → Except String DefVal → Prop :=
  fun Δ₁ Δ₂ ρ₁ ρ₂ m d =>
    ∀ (Δ : Signature) (s : NameSupply) (φ : Formula) (body : DefVal),
      Δ₂.Subset Δ₁ → Δ₂.wf → Γ.defWfIn Δ₂ →
      Δ₁.Subset Δ → Δ.wf → s.Covers Δ →
      (⟨res, .value⟩ : Var) ∈ Δ.vars →
      m s = .ok φ →
      d = .ok body →
      body.wfIn Δ₂ →
      Γ.splitSound ρ₁ →
      Env.agreeOn Δ₂ ρ₁ ρ₂ →
      ρ₁.lookupConst .value res = ρ₂.lookupConst .value res →
      body.defined.eval ρ₂ →
      P ρ₂ (body.value.eval ρ₂) →
      φ.eval ρ₁

/-- Soundness binary case for conditionals. The generic paired-encoding
induction supplies binary hypotheses for both branches; this lemma unpacks the
two successful carriers and dispatches to the branch selected by the condition. -/
theorem SoundBinary.ite
    {Γ : FunCtx} {P : Env → Srt.value.denote → Prop} {res : String}
    {Δ₁ Δ₂ : Signature} {ρ₁ ρ₂ : Env}
    {c₁ c₂ : Term .bool} {t₁ e₁ : Rel} {t₂ e₂ : Except String DefVal}
    (hceval : Term.eval ρ₁ c₁ = Term.eval ρ₂ c₂)
    (ht : SoundBinary Γ P res Δ₁ Δ₂ ρ₁ ρ₂ t₁ t₂)
    (he : SoundBinary Γ P res Δ₁ Δ₂ ρ₁ ρ₂ e₁ e₂) :
  SoundBinary Γ P res Δ₁ Δ₂ ρ₁ ρ₂
      (Relation.encoderOps.ite c₁ t₁ e₁) (encoderOps.ite c₂ t₂ e₂) := by
  intro Δ s φ body hsub21 hΔ₂ hΓdef hsub1 hΔ hcov hres hrun hd hbody hΓs hag
    hres_eq hdefd hP
  obtain ⟨dt, de, ht₂, he₂, rfl⟩ :=
    Skolemize.encoderOps_ite_ok hd
  obtain ⟨φt, φe, ht₁, he₁, rfl⟩ :=
    Skolemize.relation_encoderOps_ite_ok hrun
  have hdtwf : dt.wfIn Δ₂ := DefVal.wfIn_of_ite_then hbody
  have hdewf : de.wfIn Δ₂ := DefVal.wfIn_of_ite_else hbody
  simp only [DefVal.ite, Formula.iteBool, Formula.eval, Term.eval, Const.denote]
    at hdefd hP ⊢
  constructor
  · intro hc1
    have hc2 : c₂.eval ρ₂ = true := by rw [← hceval]; exact hc1
    refine ht Δ s φt dt hsub21 hΔ₂ hΓdef hsub1 hΔ hcov hres ht₁ ht₂
      hdtwf hΓs hag hres_eq (hdefd.1 hc2) ?_
    simpa [hc2] using hP
  · intro hc1
    have hc2 : c₂.eval ρ₂ = false := by rw [← hceval]; exact hc1
    refine he Δ s φe de hsub21 hΔ₂ hΓdef hsub1 hΔ hcov hres he₁ he₂
      hdewf hΓs hag hres_eq (hdefd.2 hc2) ?_
    simpa [hc2] using hP

/-- Soundness binary case for calls. A split call contributes the definedness
and value-function facts; `Γ.splitSound` turns those facts into a relational
edge, and the continuation runs under a fresh pinned result variable. -/
theorem SoundBinary.call
    {Γ : FunCtx} {P : Env → Srt.value.denote → Prop} {res : String}
    {Δ₁ Δ₂ : Signature} {ρ₁ ρ₂ : Env}
    {f rel : String} {arg₁ arg₂ : Term .value}
    {k₁ : Term .value → Rel} {k₂ : Term .value → Except String DefVal}
    (hmem : (f, rel) ∈ Γ)
    (harg₁ : arg₁.wfIn Δ₁) (harg₂ : arg₂.wfIn Δ₂)
    (hargeval : Term.eval ρ₁ arg₁ = Term.eval ρ₂ arg₂)
    (hk : EncoderContSpec (SoundBinary Γ P res) Δ₁ Δ₂ ρ₁ ρ₂ k₁ k₂) :
    SoundBinary Γ P res Δ₁ Δ₂ ρ₁ ρ₂
      (Relation.encoderOps.call rel arg₁ k₁) (encoderOps.call rel arg₂ k₂) := by
  intro Δ s φ body hsub21 hΔ₂ hΓdef hsub1 hΔ hcov hres hrun hd hbody hΓs hag
    hres_eq hdefd hP
  -- DefVal side: d = encoderOps.call rel arg₂ k₂ = DefVal.bind (DefVal.call rel arg₂) k₂
  simp only [encoderOps] at hd
  obtain ⟨n, hkn, hbodyeq⟩ := DefVal.bind_ok hd
  simp only [DefVal.call] at hkn
  subst hbodyeq
  -- decompose well-formedness, definedness, value postcondition
  obtain ⟨hnval_wf, hisdef_wf, hndef_wf⟩ := hbody
  simp only [Formula.eval] at hdefd
  obtain ⟨hisdef_ev, hndef_ev⟩ := hdefd
  have hnwf : n.wfIn Δ₂ := ⟨hnval_wf, hndef_wf⟩
  have hfun_mem : SpecFn.func rel ∈ Δ₂.unary := (hΓdef f rel hmem).1
  have hdef_mem : SpecFn.defined rel ∈ Δ₂.unaryRel := (hΓdef f rel hmem).2
  -- Rel side: m = Rel.call rel arg₁ k₁
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
    -- existential witness
    set w := ρ₂.unary .value .value (SpecFn.funcName rel) (arg₂.eval ρ₂) with hw
    simp only [Formula.eval]
    refine ⟨w, ?_, ?_⟩
    · -- the relational call edge holds
      have hunary_eq : ρ₁.unary .value .value (SpecFn.funcName rel) =
          ρ₂.unary .value .value (SpecFn.funcName rel) :=
        hag.2.2.1 (SpecFn.func rel) hfun_mem
      have hunaryRel_eq : ρ₁.unaryRel .value (SpecFn.defName rel) =
          ρ₂.unaryRel .value (SpecFn.defName rel) :=
        hag.2.2.2.2.1 (SpecFn.defined rel) hdef_mem
      have hisdef_ev' : ρ₂.unaryRel .value (SpecFn.defName rel) (arg₂.eval ρ₂) := by
        simpa [SpecFn.isDefined, Formula.eval, UnPred.eval] using hisdef_ev
      have hargΔ : arg₁.wfIn Δ := Term.wfIn_mono _ harg₁ hsub1 hΔ
      have hargeval' : arg₁.eval (ρ₁.updateConst .value ctx.r w) = arg₁.eval ρ₁ :=
        ctx.eval_update_fresh hargΔ
      have hedge : ρ₁.binaryRel .value .value rel (arg₁.eval ρ₁) w := by
        refine hΓs f rel hmem (arg₁.eval ρ₁) w ⟨?_, ?_⟩
        · rw [congrFun hunaryRel_eq (arg₁.eval ρ₁), hargeval]
          exact hisdef_ev'
        · rw [congrFun hunary_eq (arg₁.eval ρ₁), hargeval, hw]
      simpa [Formula.funcall, Formula.eval, BinPred.eval, Term.eval,
        Env.updateConst_binaryRel, Env.lookupConst_updateConst_same, hargeval']
        using hedge
    · -- the continuation is sound
      have hsplit_upd : Γ.splitSound (ρ₁.updateConst .value ctx.r w) :=
        FunCtx.splitSound_updateConst hΓs .value ctx.r w
      have hag_upd : Env.agreeOn Δ₂ (ρ₁.updateConst .value ctx.r w) ρ₂ :=
        Env.agreeOn_trans
          (Env.agreeOn_symm
            (Env.agreeOn_update_fresh_const (c := ⟨ctx.r, .value⟩) hfreshΔ₂))
          hag
      have hcallwf : (SpecFn.call rel arg₂).wfIn Δ₂ :=
        SpecFn.call_wfIn hfun_mem hΔ₂ harg₂
      have hagree₁ : Env.agreeOn Δ₁ ρ₁ (ρ₁.updateConst .value ctx.r w) :=
        Env.agreeOn_update_fresh_const (c := ⟨ctx.r, .value⟩) hfreshΔ₁
      have heval_eq :
          Term.eval (ρ₁.updateConst .value ctx.r w) (Term.var .value ctx.r) =
            Term.eval ρ₂ (SpecFn.call rel arg₂) := by
        simp [Term.eval, SpecFn.call, UnOp.eval, Env.lookupConst_updateConst_same, hw]
      have hcont :=
        hk (hsub1.trans ctx.subset) (Signature.Subset.refl Δ₂) ctx.wf hΔ₂
          hagree₁ Env.agreeOn_refl
          (Term.var .value ctx.r) (SpecFn.call rel arg₂) ctx.var_wf hcallwf heval_eq
      exact hcont ctx.Δ' ctx.s' φ' n
        (hsub21.trans (hsub1.trans ctx.subset)) hΔ₂ hΓdef
        (Signature.Subset.refl ctx.Δ') ctx.wf ctx.covers
        (ctx.subset.vars _ hres) hk₁run hkn hnwf hsplit_upd hag_upd
        (by rw [Env.lookupConst_updateConst_ne hr_ne_res.symm]; exact hres_eq)
        hndef_ev hP

/-- Operation-level binary data: the soundness relation is preserved by the
encoder operations. `unop`/`binop` are handled generically by
`encodeWith_bind_binary`, so only `call`, `ite` and `error` appear here. -/
def soundBinary_ops (Γ : FunCtx) (P : Env → Srt.value.denote → Prop) (res : String) :
    EncoderOpsBinary Γ Relation.encoderOps encoderOps (SoundBinary Γ P res) where
  error_binary := by
    intro _Δ₁ _Δ₂ _ρ₁ _ρ₂ msg Δ s φ body _ _ _ _ _ _ _ _ hd _ _ _ _ _
    simp [encoderOps] at hd
  ite_binary := SoundBinary.ite
  call_binary := SoundBinary.call

/-- Pinned-result soundness, obtained directly from a successful paired
encoding of the same expression: the split body's definedness and value
imply the relational formula. -/
theorem encodeWith_kEq_sound {Γ : FunCtx} {Δenc Δrun : Signature}
    {srun : NameSupply} {ρ : Env}
    {e : Typed.Expr} {body : DefVal}
    {res : String} {φ : Formula}
    (hrun : encodeWith Relation.encoderOps Γ (VarEnv.ofSignature Δenc) e (Relation.kEq res) srun = .ok φ)
    (hdef : encode Γ Δenc e = .ok body)
    (hΓ : Γ.splitSound ρ) (hΓdef : Γ.defWfIn Δenc)
    (hΔenc : Δenc.wf) (hΔrun : Δrun.wf) (hcov : srun.Covers Δrun)
    (hsub : Δenc.Subset Δrun)
    (hbody : body.wfIn Δenc)
    (hres : (⟨res, .value⟩ : Var) ∈ Δrun.vars) :
    body.defined.eval ρ ∧ body.value.eval ρ = (Term.var .value res).eval ρ →
      φ.eval ρ := by
  intro hsplit
  have hbinary :
      SoundBinary Γ (fun ρ v => v = (Term.var .value res).eval ρ) res Δenc Δenc ρ ρ
        (encodeWith Relation.encoderOps Γ (VarEnv.ofSignature Δenc) e (Relation.kEq res))
        (encodeWith encoderOps Γ (VarEnv.ofSignature Δenc) e (fun v => .ok (DefVal.pure v))) := by
    refine encodeWith_bind_binary (δ₁ := VarEnv.ofSignature Δenc)
      (δ₂ := VarEnv.ofSignature Δenc) (soundBinary_ops Γ _ res) e
      (Signature.Subset.refl _) (Signature.Subset.refl _) hΔenc hΔenc
      ?_ ?_
    · exact varEnv_ofSignature_agree_self hΔenc
    -- EncoderContSpec for the `(kEq res, pure)` continuation pair
    intro Δ₁' Δ₂' ρ₁' ρ₂' _hs₁ _hs₂ _hw₁ _hw₂ _ha₁ _ha₂ v₁ v₂ _hv₁ _hv₂ heval Δ s φ' body'
      _ _ _ _ _ _ _ hrun' hd' _ _ _ hres_eq' _ hP'
    simp only [Relation.kEq, Except.ok.injEq] at hrun'
    simp only [Except.ok.injEq] at hd'
    subst hd'
    subst hrun'
    simp only [DefVal.pure, Formula.eval, Term.eval] at hP' ⊢
    rw [heval, hP', hres_eq']
  exact hbinary Δrun srun φ body (Signature.Subset.refl _) hΔenc hΓdef hsub hΔrun hcov
    hres hrun hdef hbody hΓ Env.agreeOn_refl rfl hsplit.1 hsplit.2

/-! ## Transport between split and combined environments -/

theorem defval_eval_transport_to_relSplit_domain
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {rel : String} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} {R : ValRel}
    {P : Srt.value.denote → Prop} {F : Srt.value.denote → Srt.value.denote}
    (henc : encodeBody Γ Δ f rel x res e = .ok body)
    (hΓdef : Γ.defWfIn Δ) (hΔ : Δ.wf) (hheadFresh : HeadFresh Δ rel x res)
    (vin : Srt.value.denote)
    (hdefBody : defBody ρ rel x body F P vin) :
    let vbody := body.value.eval (defEnv ρ rel x P F vin)
    body.defined.eval (((relSplitEnv ρ rel R P F).updateConst .value x vin).updateConst .value res vbody) ∧
      body.value.eval (((relSplitEnv ρ rel R P F).updateConst .value x vin).updateConst .value res vbody) =
        vbody := by
  let vbody := body.value.eval (defEnv ρ rel x P F vin)
  have hbody : body.wfIn (defvalBodySig Δ rel x) :=
    encodeBody_wfIn_defvalBodySig hΔ hΓdef hheadFresh henc
  have hag : Env.agreeOn (defvalBodySig Δ rel x)
      (defEnv ρ rel x P F vin)
      (((relSplitEnv ρ rel R P F).updateConst .value x vin).updateConst .value res vbody) :=
    splitEnv_relSplitEnv_agreeOn_defvalBodySig (R := R) (D := P) (F := F)
      hheadFresh vin vbody
  exact ⟨(Formula.eval_env_agree hbody.2 hag).mp hdefBody,
    (Term.eval_env_agree hbody.1 hag).symm⟩

/-- Split definedness plus the split body value gives a relational edge. This
is the converse half of the relation/split fixpoint equivalence. -/
theorem semrel_sound
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {rel : String} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (henc : encodeBody Γ Δ f rel x res e = .ok body)
    (hΓ : Γ.splitCompatible ρ)
    (hΓrel : Γ.wfIn Δ) (hΓdef : Γ.defWfIn Δ)
    (hΔ : Δ.wf) (hheadFresh : HeadFresh Δ rel x res)
    (vin vout : Srt.value.denote) :
    semdef Γ Δ ρ f rel x res e body vin →
      body.value.eval
        ((defInterpEnv Γ Δ ρ f rel x res e body).updateConst .value x vin) =
      vout →
      semrel Γ Δ ρ f rel x res e vin vout := by
  intro hsem hval
  obtain ⟨φ, hrelEnc⟩ := encodeBody_relEncodeBody hΔ hΓdef hheadFresh henc
  set m := encodeWith Relation.encoderOps (Relation.ctx Γ f rel)
      (VarEnv.ofSignature (bodySig Δ rel x)) e (Relation.kEq res) with hm_def
  have hrun : m (relBodySupply Δ rel x res) = .ok φ := by
    have hvars :
        VarEnv.ofSignature (bodySig Δ rel x) =
          VarEnv.ofSignature (Relation.bodySig Δ rel x) := by
      simp [VarEnv.ofSignature, bodySig, Relation.bodySig, Signature.declVar,
        Signature.addBinaryRel, Signature.addUnary, Signature.addUnaryRel,
        Signature.remove, Signature.addVar]
    rw [hm_def, hvars]
    simpa [Relation.relEncodeBody] using hrelEnc
  let R : ValRel := semrel Γ Δ ρ f rel x res e
  let F : Srt.value.denote → Srt.value.denote := semFunc R
  let D : Srt.value.denote → Prop := semdef Γ Δ ρ f rel x res e body
  have hrelEncR : Relation.relEncodeBody Γ Δ f rel x res e = .ok φ := by
    exact hrelEnc
  have hrel_eq :
      R = Fix.lfp (Relation.semanticBody Formula.sem ρ rel x res φ) := by
    simp [R, Relation.semrel, Relation.semanticFixpoint, hrelEncR]
  have hmMono : Rel.Mono m :=
    encodeWith_ind Relation.encoderOps_preservesMono e (Relation.kEq_mono res)
  have hmonoφ : SemanticMono Formula.sem φ :=
    hmMono (relBodySupply Δ rel x res) φ hrun
  have hpreR :
      Fix.le (Relation.semanticBody Formula.sem ρ rel x res φ R) R := by
    rw [hrel_eq]
    exact Fix.lfp_prefixed (Relation.semanticBody_mono_of_semanticMono hmonoφ)
  have hbodyWf_body : body.wfIn (bodySig Δ rel x) :=
    encode_wfIn e (bodySig_wf_of_headFresh hΔ hheadFresh)
      (ctx_defWfIn_bodySig_of_headFresh hΓdef hheadFresh) (encodeBody_def_bodySig henc)
  have hres_mem : (⟨res, .value⟩ : Var) ∈ (sig Δ rel x res).vars := by
    unfold sig
    exact Signature.var_mem_declVar _ ⟨res, .value⟩
  have hφ_of_split
      {ρsplit : Env} {vin' vout' : Srt.value.denote}
      (hΓsplit : (Relation.ctx Γ f rel).splitSound ρsplit)
      (hsplit :
        body.defined.eval ((ρsplit.updateConst .value x vin').updateConst .value res vout') ∧
          body.value.eval ((ρsplit.updateConst .value x vin').updateConst .value res vout') =
            vout') :
      φ.eval ((ρsplit.updateConst .value x vin').updateConst .value res vout') :=
    encodeWith_kEq_sound (Γ := Relation.ctx Γ f rel)
      (Δenc := bodySig Δ rel x) (Δrun := sig Δ rel x res)
      (srun := relBodySupply Δ rel x res)
      (ρ := (ρsplit.updateConst .value x vin').updateConst .value res vout')
      (e := e) (body := body) (res := res) (φ := φ)
      hrun (encodeBody_def_bodySig henc)
      (FunCtx.splitSound_updateConst
        (FunCtx.splitSound_updateConst hΓsplit .value x vin') .value res vout')
      (ctx_defWfIn_bodySig_of_headFresh hΓdef hheadFresh)
      (bodySig_wf_of_headFresh hΔ hheadFresh)
      (sig_wf_of_headFresh hΔ hheadFresh) (relBodySupply_covers_sig Δ rel x res)
      (bodySig_subset_sig_of_headFresh hheadFresh)
      hbodyWf_body hres_mem
      (by simpa [Term.eval, Env.lookupConst_updateConst_same] using hsplit)
  have hdomain :
      UnaryFix.le D (semDefined R) := by
    unfold D semdef
    apply UnaryFix.lfp_le_of_prefixed
    intro vin hdefBody
    let P : Srt.value.denote → Prop := semDefined R
    let vbody := body.value.eval (defEnv ρ rel x P F vin)
    let ρP := relSplitEnv ρ rel R P F
    have hΓP : (Relation.ctx Γ f rel).splitSound ρP := by
      exact splitSound_cons_relSplitEnv
        (FunCtx.splitSound_of_compatible hΓ)
        (freshFn_of_headFresh hΓrel hΓdef hheadFresh)
        (by
          intro a b hsplit
          have hcall : R a (F a) := semFunc_spec hsplit.1
          simpa [hsplit.2] using hcall)
    have hsplitP :
        body.defined.eval ((ρP.updateConst .value x vin).updateConst .value res vbody) ∧
          body.value.eval ((ρP.updateConst .value x vin).updateConst .value res vbody) =
            vbody :=
      defval_eval_transport_to_relSplit_domain (R := R) (P := P)
        henc hΓdef hΔ hheadFresh vin hdefBody
    have hφP :
        φ.eval ((ρP.updateConst .value x vin).updateConst .value res vbody) :=
      hφ_of_split hΓP hsplitP
    have hbodyR : Relation.semanticBody Formula.sem ρ rel x res φ R vin vbody :=
      (rel_body_eval_iff (D := P) (F := F) hΓrel hΔ hheadFresh hrelEnc vin vbody).mp hφP
    exact ⟨vbody, hpreR vin vbody hbodyR⟩
  have hdefBody :
      defBody ρ rel x body F D vin := by
    simpa [D, F] using
      (semdef_unfold_of_encode (ρ := ρ) (x := x) (res := res) henc vin).mp hsem
  let ρD := relSplitEnv ρ rel R D F
  have hΓD : (Relation.ctx Γ f rel).splitSound ρD := by
    exact splitSound_cons_relSplitEnv
      (FunCtx.splitSound_of_compatible hΓ)
      (freshFn_of_headFresh hΓrel hΓdef hheadFresh)
      (by
        intro a b hsplit
        have hcall : R a (F a) := semFunc_spec (hdomain a hsplit.1)
        simpa [hsplit.2] using hcall)
  have hsplitD :
      body.defined.eval ((ρD.updateConst .value x vin).updateConst .value res vout) ∧
        body.value.eval ((ρD.updateConst .value x vin).updateConst .value res vout) =
          vout := by
    have hvalEq : body.value.eval (defEnv ρ rel x D F vin) = vout := by
      simpa [D, F, R, defInterpEnv, defEnv] using hval
    rw [← hvalEq]
    exact defval_eval_transport_to_relSplit_domain (R := R) (P := D)
      henc hΓdef hΔ hheadFresh vin hdefBody
  have hφD :
      φ.eval ((ρD.updateConst .value x vin).updateConst .value res vout) :=
    hφ_of_split hΓD hsplitD
  have hbodyR : Relation.semanticBody Formula.sem ρ rel x res φ R vin vout :=
    (rel_body_eval_iff (D := D) (F := F) hΓrel hΔ hheadFresh hrelEnc vin vout).mp hφD
  exact hpreR vin vout hbodyR

theorem relation_semrel_functional_of_encodeBody
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {fn : SpecFn} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (henc : encodeBody Γ Δ f fn x res e = .ok body)
    (hΔ : Δ.wf) (hΓfn : Γ.wfIn Δ) (hΓdef : Γ.defWfIn Δ)
    (hheadFresh : HeadFresh Δ fn x res)
    (hρdet : Relation.BinaryRelDet Γ ρ ρ)
    (vin y₁ y₂ : Srt.value.denote) :
    semrel Γ Δ ρ f fn x res e vin y₁ →
      semrel Γ Δ ρ f fn x res e vin y₂ →
      y₁ = y₂ := by
  obtain ⟨φ, hrelEnc⟩ := encodeBody_relEncodeBody hΔ hΓdef hheadFresh henc
  have hresFreshR : res ∉ (Relation.bodySig Δ fn x).allNames := by
    intro hres
    exact hheadFresh.resFresh (Signature.allNames_subset
      (relBodySig_subset_bodySig (Δ := Δ) (fn := fn) (x := x)) _ hres)
  exact Relation.semrel_functional hrelEnc hΓfn hheadFresh.relFresh
    (relBodySig_wf_of_headFresh hΔ hheadFresh)
    hresFreshR hρdet vin y₁ y₂

/-- If the split body is defined at an input, then the body value is the
canonical value chosen from the relational semantics. This is the exact
soundness fact needed by the completeness direction when it builds the graph
of the split interpretation inside the relational fixpoint. -/
theorem semFunc_eq_of_semdef_value
    {Γ : FunCtx} {Δ : Signature} {ρ : Env}
    {f : TinyML.Var} {rel : String} {x res : TinyML.Var} {e : Typed.Expr}
    {body : DefVal} (henc : encodeBody Γ Δ f rel x res e = .ok body)
    (hΓ : Γ.splitCompatible ρ)
    (hΓrel : Γ.wfIn Δ) (hΓdef : Γ.defWfIn Δ)
    (hΔ : Δ.wf) (hheadFresh : HeadFresh Δ rel x res)
    (hρdet : Relation.BinaryRelDet Γ ρ ρ)
    (vin vout : Srt.value.denote) :
    semdef Γ Δ ρ f rel x res e body vin →
      body.value.eval
        ((defInterpEnv Γ Δ ρ f rel x res e body).updateConst .value x vin) =
      vout →
      semFunc (semrel Γ Δ ρ f rel x res e) vin = vout := by
  intro hdefined hval
  let R : ValRel := semrel Γ Δ ρ f rel x res e
  have hrelBody : R vin vout := by
    simpa [R] using
      semrel_sound henc hΓ hΓrel hΓdef hΔ hheadFresh vin vout hdefined hval
  have hdefinedR : semDefined R vin := ⟨vout, hrelBody⟩
  have hchosen : R vin (semFunc R vin) := semFunc_spec hdefinedR
  exact relation_semrel_functional_of_encodeBody henc hΔ hΓrel hΓdef hheadFresh hρdet vin
      (semFunc R vin) vout (by simpa [R] using hchosen) (by simpa [R] using hrelBody)

end Skolemize
end Verifier.RelationalEncoding
