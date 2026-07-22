-- SUMMARY: Predicate transformers for function specifications, together with their semantics and call and implementation protocols.
import Mica.TinyML.Typed
import Mica.TinyML.Typing
import Mica.FOL.Printing
import Mica.Verifier.Monad
import Mica.Verifier.Atoms
import Mica.Verifier.Assertions
import Mica.Verifier.Utils
import Mica.Base.Fresh
import Mathlib.Data.Finmap


open Iris Iris.BI

variable [MicaGS HasLC.hasLC Sig]

/-!
# Predicate Transformers

Defines `PredTrans` and `SpecPredicate`.
-/

-- ---------------------------------------------------------------------------
-- Core types
-- ---------------------------------------------------------------------------

def PredTrans := Assertion (Pred (Assertion Unit))
abbrev SpecPredicate := MultiPred PredTrans

instance : DecidableEq PredTrans := by
  unfold PredTrans Pred
  infer_instance

-- ---------------------------------------------------------------------------
-- Well-formedness
-- ---------------------------------------------------------------------------

/-- A predicate transformer is well-formed when its outer assertion is well-formed
    and each inner postcondition assertion is also well-formed (in the extended context). -/
def PredTrans.wfIn (Δ : Signature) (pt : PredTrans) : Prop :=
  Assertion.wfIn
    (fun post Δ' => Assertion.wfIn (fun _ _ => True) (Δ'.declVar ⟨post.1, .value⟩) post.2)
    Δ pt


def PredTrans.checkWf (Δ : Signature) (pt : PredTrans) : Except String Unit :=
  Assertion.checkWf
    (fun post Δ' => Assertion.checkWf (fun _ _ => .ok ()) (Δ'.declVar ⟨post.1, .value⟩) post.2)
    Δ pt

omit [MicaGS HasLC.hasLC Sig] in
theorem PredTrans.checkWf_ok {pt : PredTrans} {Δ : Signature}
    (h : pt.checkWf Δ = .ok ()) : pt.wfIn Δ :=
  Assertion.checkWf_ok
    (fun _ _ hok => Assertion.checkWf_ok (fun _ _ _ => trivial) hok)
    h

-- ---------------------------------------------------------------------------
-- Semantics
-- ---------------------------------------------------------------------------

def PredTrans.apply (Θ : TinyML.TypeEnv) (Φ : Runtime.Val → iProp) (m : PredTrans) (ρ : VerifM.Env) : iProp :=
  Assertion.pre Θ (fun post ρ' =>
    BIBase.forall fun v : Runtime.Val =>
      Assertion.post Θ (fun () _ => Φ v) post.2 (ρ'.updateConst .value post.1 v)
  ) m ρ

-- ---------------------------------------------------------------------------
-- Verifier operations
-- ---------------------------------------------------------------------------

/-- The caller side of a predicate transformer: assert the precondition (prove the outer
    assertion) and assume the postcondition (assume the inner assertion). Returns a term
    representing the result value. -/
def PredTrans.call (σ : FiniteSubst) (pt : PredTrans) : VerifM (Term .value) := do
  let (σ₁, (postName, postBody)) ← Assertion.prove σ pt
  let resVar ← VerifM.decl (some postName) .value
  let σ₂ := σ₁.rename ⟨postName, .value⟩ resVar.name
  let (_, ()) ← Assertion.assume σ₂ postBody
  pure (.const (.uninterpreted resVar.name .value))

/-- The implementor side of a predicate transformer: assume the precondition (assume the outer
    assertion), run `body` to produce a result term, then assert the postcondition (prove the
    inner assertion). Dual to `PredTrans.call`. -/
def PredTrans.implement (σ : FiniteSubst) (pt : PredTrans) (body : VerifM (Term .value)) : VerifM Unit := do
  let (σ₁, (postName, postBody)) ← Assertion.assume σ pt
  let result ← body
  let resVar ← VerifM.decl (some postName) .value
  let σ₂ := σ₁.rename ⟨postName, .value⟩ resVar.name
  VerifM.assume (.pure (.eq .value (.const (.uninterpreted resVar.name .value)) result))
  let (_, ()) ← Assertion.prove σ₂ postBody
  pure ()

-- ---------------------------------------------------------------------------
-- Properties
-- ---------------------------------------------------------------------------

omit [MicaGS HasLC.hasLC Sig] in
theorem PredTrans.wfIn_mono {pt : PredTrans} {Δ Δ' : Signature}
    (h : pt.wfIn Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) : pt.wfIn Δ' := by
  unfold PredTrans.wfIn at h ⊢
  exact Assertion.wfIn_mono pt _
    (fun post ds ds' hsub' hwf' hpost =>
      Assertion.wfIn_mono post.2 _ (fun _ _ _ _ _ h => h) hpost
        (Signature.Subset.declVar hsub' ⟨post.1, .value⟩)
        (Signature.wf_declVar hwf'))
    h hsub hwf

theorem PredTrans.apply_env_agree (Θ : TinyML.TypeEnv) {pt : PredTrans} {Φ : Runtime.Val → iProp}
    {ρ ρ' : VerifM.Env} {Δ : Signature}
    (hwf : pt.wfIn Δ) (hagree : VerifM.Env.agreeOn Δ ρ ρ') :
    PredTrans.apply Θ Φ pt ρ ⊢ PredTrans.apply Θ Φ pt ρ' := by
  unfold PredTrans.apply at ⊢
  apply Assertion.pre_env_agree Θ hwf hagree
  intro ⟨postName, postBody⟩ Δ' ρ₁ ρ₂ hwf_post hagree_post
  apply forall_intro
  intro v
  exact (forall_elim v).trans <|
    Assertion.post_env_agree Θ hwf_post
      (VerifM.Env.agreeOn_declVar hagree_post)
      (fun _ _ _ _ _ _ => .rfl)

-- ---------------------------------------------------------------------------
-- Correctness
-- ---------------------------------------------------------------------------

theorem PredTrans.call_correct (Θ : TinyML.TypeEnv) (pt : PredTrans) (Δ_base : Signature) (σ : FiniteSubst)
    (st : TransState) (ρ : VerifM.Env)
    (Ψ : Term .value → TransState → VerifM.Env → Prop) (Φ : Runtime.Val → iProp) R :
    pt.wfIn (Δ_base.declVars σ.dom) →
    σ.wfIn Δ_base st.decls →
    VerifM.eval (PredTrans.call σ pt) st ρ Ψ →
    (∀ v st' ρ' t, Ψ t st' ρ' → t.wfIn st'.decls → t.eval ρ'.env = v →
      (st'.sl Θ ρ' ∗ R ⊢ Φ v)) →
    st.sl Θ ρ ∗ R ⊢ PredTrans.apply Θ Φ pt (VerifM.Env.withEnv ρ (σ.subst.eval ρ.env)) := by
  intro hwf hσwf heval hΨ
  simp only [PredTrans.call] at heval
  have hb := VerifM.eval_bind heval
  let retWf : (String × Assertion Unit) → Signature → Prop :=
    fun post Δ' => Assertion.wfIn (fun _ _ => True) (Δ'.declVar ⟨post.1, .value⟩) post.2
  let Φpost : (String × Assertion Unit) → VerifM.Env → iProp :=
    fun post ρ' =>
      BIBase.forall fun v : Runtime.Val =>
        Assertion.post Θ (fun () _ => Φ v) post.2 (ρ'.updateConst .value post.1 v)
  let Ψcall : (FiniteSubst × (String × Assertion Unit)) → TransState → VerifM.Env → Prop :=
    fun r st' ρ' =>
      match r with
      | (σ₁, postName, postBody) => (do
          let resVar ← VerifM.decl (some postName) Srt.value
          let _ ← Assertion.assume (σ₁.rename ⟨postName, .value⟩ resVar.name) postBody
          Pure.pure (Term.const (.uninterpreted resVar.name .value))).eval st' ρ' Ψ
  have hpre : st.sl Θ ρ ∗ R ⊢ Assertion.pre Θ Φpost pt (VerifM.Env.withEnv ρ (σ.subst.eval ρ.env)) := by
    exact Assertion.prove_correct Θ pt Δ_base σ retWf st ρ Ψcall Φpost R
      (fun ⟨postName, postBody⟩ Δ' ρ₁ ρ₂ hwf_post hagree =>
        forall_intro fun v =>
          (forall_elim v).trans <|
            Assertion.post_env_agree Θ hwf_post
              (VerifM.Env.agreeOn_declVar hagree)
              (fun _ _ _ _ _ _ => .rfl))
      hσwf hwf hb
      (fun σ₁ ⟨postName, postBody⟩ st₁ ρ₁ hcont hσ₁wf hwf₁ => by
        apply forall_intro
        intro v
        have hb2 := VerifM.eval_bind hcont
        have hdecl := VerifM.eval_decl hb2
        set resVar := st₁.freshConst (some postName) .value
        have hfresh_decls : resVar.name ∉ st₁.decls.allNames :=
          st₁.freshConst_fresh (some postName) .value
        have hfresh_range : resVar.name ∉ σ₁.range.allNames :=
          hσ₁wf.fresh_range hfresh_decls
        specialize hdecl v
        have hb3 := VerifM.eval_bind hdecl
        set σ₂ := σ₁.rename ⟨postName, .value⟩ resVar.name
        have hσ₂wf : σ₂.wfIn Δ_base (st₁.decls.addConst resVar) := by
          simpa [σ₂] using
            (FiniteSubst.rename_wfIn (σ := σ₁) (Δ_base := Δ_base) (Δ_use := st₁.decls)
              (v := ⟨postName, .value⟩) (name' := resVar.name)
              hσ₁wf hfresh_range hfresh_decls)
        have hwf₁' : Assertion.wfIn (fun _ _ => True) (Δ_base.declVars σ₂.dom) postBody := by
          simpa [σ₂, FiniteSubst.rename_source_eq] using hwf₁
        have hgrow := VerifM.eval.decls_grow (ρ₁.updateConst .value resVar.name v) hb3
        have hassume := Assertion.assume_correct Θ postBody Δ_base σ₂ (fun _ _ => True)
          { st₁ with decls := st₁.decls.addConst resVar }
          (ρ₁.updateConst .value resVar.name v)
          (fun a st' ρ' =>
            { st₁ with decls := st₁.decls.addConst resVar }.decls.Subset st'.decls ∧
              VerifM.Env.agreeOn { st₁ with decls := st₁.decls.addConst resVar }.decls
                (ρ₁.updateConst .value resVar.name v) ρ' ∧
              (Pure.pure (Term.const (.uninterpreted resVar.name .value)) : VerifM (Term .value)).eval st' ρ' Ψ)
          (fun () _ => Φ v) R
          (fun _ _ _ _ _ _ => .rfl)
          hσ₂wf hwf₁' hgrow
          (fun _ () st₂ ρ₂ ⟨hsub, hagree, hcont'⟩ _ _ => by
            have hret := VerifM.eval_ret hcont'
            have hwfst₂ : st₂.decls.wf := (VerifM.eval.wf hcont').namesDisjoint
            apply hΨ _ st₂ ρ₂ (.const (.uninterpreted resVar.name .value)) hret
            · exact Term.const_wfIn_of_mem hwfst₂ (hsub.consts resVar (List.Mem.head _))
            · simp only [Term.eval, Const.denote]
              have := hagree.2.1 resVar (List.Mem.head _)
              simpa [Env.lookupConst, Env.updateConst] using this.symm)
        have hinterp_bi :
            st₁.sl Θ ρ₁ ⊣⊢ st₁.sl Θ (ρ₁.updateConst .value resVar.name v) :=
          SpatialContext.interp_env_agree Θ (VerifM.eval.wf hcont).ownsWf
            (Env.agreeOn_update_fresh_const (c := resVar) hfresh_decls)
        exact (sep_mono_left hinterp_bi.1).trans <| hassume.trans <| Assertion.post_env_agree Θ hwf₁'
          (by
            simpa [σ₂, VerifM.Env.agreeOn, VerifM.Env.withEnv_env, VerifM.Env.updateConst] using
              (FiniteSubst.rename_agreeOn (σ := σ₁) (Δ_base := Δ_base) (Δ_use := st₁.decls)
                (v := ⟨postName, .value⟩) (name' := resVar.name)
                (ρ := ρ₁.env) (u := v) hσ₁wf hfresh_range))
          (fun _ _ _ _ _ _ => .rfl))
  simpa [PredTrans.apply, Φpost] using hpre


theorem PredTrans.implement_correct (Θ : TinyML.TypeEnv) (pt : PredTrans) (Δ_base : Signature) (σ : FiniteSubst)
    (body : VerifM (Term .value))
    (st : TransState) (ρ : VerifM.Env) (Φ : Runtime.Val → iProp) (R : iProp) :
    pt.wfIn (Δ_base.declVars σ.dom) →
    σ.wfIn Δ_base st.decls →
    VerifM.eval (PredTrans.implement σ pt body) st ρ (fun _ _ _ => True) →
    (∀ st' ρ' (Q : iProp),
      st.decls.Subset st'.decls →
      VerifM.Env.agreeOn st.decls ρ ρ' →
      VerifM.eval body st' ρ'
      (fun result st'' ρ'' =>
        ∀ (S : iProp),
        result.wfIn st''.decls →
        (st''.sl Θ ρ'' ∗ Q ∗ (Φ (result.eval ρ''.env) -∗ S) ⊢ S)) →
      st'.sl Θ ρ' ∗ Q ⊢ R) →
    st.sl Θ ρ ∗ PredTrans.apply Θ Φ pt (VerifM.Env.withEnv ρ (σ.subst.eval ρ.env)) ⊢ R := by
  intro hwf hσwf heval hbody
  simp only [PredTrans.implement] at heval
  have hb := VerifM.eval_bind heval
  have hb_grow := VerifM.eval.decls_grow ρ hb
  let retWf : (String × Assertion Unit) → Signature → Prop :=
    fun post Δ' => Assertion.wfIn (fun _ _ => True) (Δ'.declVar ⟨post.1, .value⟩) post.2
  let OuterQ : (String × Assertion Unit) → VerifM.Env → iProp :=
    fun ⟨postName, postBody⟩ ρ' =>
      BIBase.forall fun v : Runtime.Val =>
        Assertion.post Θ (fun () _ => Φ v) postBody (ρ'.updateConst .value postName v)
  let Φpost : (String × Assertion Unit) → VerifM.Env → iProp :=
    fun a ρ' => OuterQ a ρ' -∗ R
  have hpost := Assertion.assume_correct Θ pt Δ_base σ retWf
    st ρ _ Φpost emp
    (fun ⟨postName, postBody⟩ Δ' ρ₁ ρ₂ hwf_post hagree => by
      refine wand_intro ?_
      iintro H
      icases H with ⟨Hcont, HQ₂⟩
      iapply Hcont
      apply forall_intro
      intro v
      exact (forall_elim v).trans <|
        Assertion.post_env_agree Θ hwf_post
          (Env.agreeOn_symm (Env.agreeOn_declVar hagree))
          (fun _ _ _ _ _ _ => .rfl))
    hσwf hwf hb_grow
    (fun σ₁ ⟨postName, postBody⟩ st₁ ρ₁ ⟨hdsub_st, hagree_st, hcont⟩ hσ₁wf hwf_postBody => by
      apply BIBase.Entails.trans sep_comm.1
      apply BIBase.Entails.trans emp_sep.1
      have hcont_body := VerifM.eval_bind hcont
      change st₁.sl Θ ρ₁ ⊢ OuterQ (postName, postBody) (VerifM.Env.withEnv ρ₁ (σ₁.subst.eval ρ₁.env)) -∗ R
      refine wand_intro ?_
      refine hbody st₁ ρ₁ _ hdsub_st hagree_st ?_
      refine (VerifM.eval.decls_grow ρ₁ hcont_body).mono ?_
      intro result st₂ ρ₂ ⟨hdsub_body, hagree_body, hrest⟩ S hwf_result
      have hb2 := VerifM.eval_bind hrest
      have hdecl := VerifM.eval_decl hb2
      set resVar := st₂.freshConst (some postName) .value
      have hwfst₂ : st₂.decls.wf := (VerifM.eval.wf hrest).namesDisjoint
      have hσ₁wf₂ : σ₁.wfIn Δ_base st₂.decls := hσ₁wf.mono hdsub_body hwfst₂
      have hfresh_decls : resVar.name ∉ st₂.decls.allNames :=
        st₂.freshConst_fresh (some postName) .value
      have hfresh_range : resVar.name ∉ σ₁.range.allNames :=
        hσ₁wf₂.fresh_range hfresh_decls
      specialize hdecl (result.eval ρ₂.env)
      have hb3 := VerifM.eval_bind hdecl
      have hassume := VerifM.eval_assumePure hb3
        (Formula.eq_wfIn_addConst_of_fresh (c := resVar) hwfst₂ hwf_result hfresh_decls)
        (Formula.eq_eval_updateConst_of_fresh (c := resVar) (ρ := ρ₂.env) hwf_result hfresh_decls)
      set σ₂ := σ₁.rename ⟨postName, .value⟩ resVar.name
      have hσ₂wf : σ₂.wfIn Δ_base (st₂.decls.addConst resVar) := by
        simpa [σ₂] using
          (FiniteSubst.rename_wfIn (σ := σ₁) (Δ_base := Δ_base) (Δ_use := st₂.decls)
            (v := ⟨postName, .value⟩) (name' := resVar.name)
            hσ₁wf₂ hfresh_range hfresh_decls)
      have hb4 := VerifM.eval_bind hassume
      have hwf_postBody' : Assertion.wfIn (fun _ _ => True) (Δ_base.declVars σ₂.dom) postBody := by
        simpa [σ₂, FiniteSubst.rename_source_eq] using hwf_postBody
      let st₃ : TransState :=
        { st₂ with
          decls := st₂.decls.addConst resVar
          asserts := Formula.eq Srt.value (Term.const (.uninterpreted resVar.name .value)) result :: st₂.asserts }
      have hpre := @Assertion.prove_correct _ Unit Θ postBody Δ_base σ₂ (fun _ _ => True)
        st₃
        (ρ₂.updateConst .value resVar.name (result.eval ρ₂.env))
        _ (fun () _ => Φ (result.eval ρ₂.env) -∗ S) (Φ (result.eval ρ₂.env) -∗ S)
        (fun _ _ _ _ _ _ => .rfl)
        hσ₂wf hwf_postBody' hb4
        (fun _ () st' ρ' hret _ _ => by
          show st'.sl Θ ρ' ∗ (Φ (result.eval ρ₂.env) -∗ S) ⊢
            (Φ (result.eval ρ₂.env) -∗ S)
          exact sep_elim_right)
      have hag_rename :=
        FiniteSubst.rename_agreeOn (σ := σ₁) (Δ_base := Δ_base) (Δ_use := st₂.decls)
          (v := ⟨postName, .value⟩) (name' := resVar.name)
          (ρ := ρ₂.env) (u := result.eval ρ₂.env) hσ₁wf₂ hfresh_range
      have hagree_st₁ : Env.agreeOn st₁.decls ρ₂.env ρ₁.env := by
        simpa [VerifM.Env.agreeOn] using VerifM.Env.agreeOn_symm hagree_body
      have hag_eval := FiniteSubst.eval_agreeOn hσ₁wf hagree_st₁
      have hag_eval' : Env.agreeOn (Δ_base.declVars σ₂.dom)
          ((σ₁.subst.eval ρ₂.env).updateConst .value postName (result.eval ρ₂.env))
          ((σ₁.subst.eval ρ₁.env).updateConst .value postName (result.eval ρ₂.env)) := by
        apply Env.agreeOn_mono
          (FiniteSubst.rename_source_subset_rev σ₁ Δ_base ⟨postName, .value⟩ resVar.name)
        exact Env.agreeOn_update (Env.agreeOn_remove hag_eval)
      have hpost_transport : Assertion.post Θ (fun () _ => Φ (result.eval ρ₂.env)) postBody
          (VerifM.Env.withEnv ρ₁ ((σ₁.subst.eval ρ₁.env).updateConst .value postName (result.eval ρ₂.env))) ⊢
          Assertion.post Θ (fun () _ => Φ (result.eval ρ₂.env)) postBody
            (VerifM.Env.withEnv (ρ₂.updateConst .value resVar.name (result.eval ρ₂.env))
              (σ₂.subst.eval (ρ₂.updateConst .value resVar.name (result.eval ρ₂.env)).env)) := by
        exact Assertion.post_env_agree Θ hwf_postBody'
          (by
            simpa [VerifM.Env.agreeOn, VerifM.Env.withEnv]
              using (Env.agreeOn_symm (Env.agreeOn_trans hag_rename hag_eval')))
          (fun _ _ _ _ _ _ => .rfl)
      have howns_agree : st₃.sl Θ ρ₂
            ⊢
          st₃.sl Θ (ρ₂.updateConst .value resVar.name (result.eval ρ₂.env)) := by
        simpa using
          (SpatialContext.interp_env_agree Θ (VerifM.eval.wf hrest).ownsWf
            (Env.agreeOn_update_fresh_const hfresh_decls)).1
      have hpre_final :
          st₂.sl Θ ρ₂ ∗ (Φ (result.eval ρ₂.env) -∗ S) ⊢
            Assertion.pre Θ (fun () _ => Φ (result.eval ρ₂.env) -∗ S) postBody
              (VerifM.Env.withEnv (ρ₂.updateConst .value resVar.name (result.eval ρ₂.env))
                (σ₂.subst.eval (ρ₂.updateConst .value resVar.name (result.eval ρ₂.env)).env)) := by
        have hinput :
            st₂.sl Θ ρ₂ ∗ (Φ (result.eval ρ₂.env) -∗ S) ⊢
              st₃.sl Θ (ρ₂.updateConst .value resVar.name (result.eval ρ₂.env)) ∗
                (Φ (result.eval ρ₂.env) -∗ S) := by
          iintro ⟨Howns, Hwand⟩
          iframe Hwand
          iapply howns_agree
          simp [st₃, TransState.sl]
        exact hinput.trans hpre
      have hpost_final :
          OuterQ (postName, postBody) (VerifM.Env.withEnv ρ₁ (σ₁.subst.eval ρ₁.env)) ⊢
            Assertion.post Θ (fun () _ => Φ (result.eval ρ₂.env)) postBody
              (VerifM.Env.withEnv (ρ₂.updateConst .value resVar.name (result.eval ρ₂.env))
                (σ₂.subst.eval (ρ₂.updateConst .value resVar.name (result.eval ρ₂.env)).env)) := by
        exact (forall_elim (result.eval ρ₂.env)).trans hpost_transport
      iintro ⟨Howns, HQ, Hwand⟩
      iapply (Assertion.pre_post_combine Θ
        (ρ := VerifM.Env.withEnv (ρ₂.updateConst .value resVar.name (result.eval ρ₂.env))
          (σ₂.subst.eval (ρ₂.updateConst .value resVar.name (result.eval ρ₂.env)).env))
        (m := postBody)
        (Φ := fun () _ => Φ (result.eval ρ₂.env) -∗ S)
        (Ψ := fun () _ => Φ (result.eval ρ₂.env))
        (R := S)
        (fun () _ => by
          iintro ⟨Hwand, HΦ⟩
          iapply Hwand
          iexact HΦ))
      isplitl [Howns Hwand]
      · iapply hpre_final
        iframe
      · iapply hpost_final
        iexact HQ
      )
  have hpre :
      PredTrans.apply Θ Φ pt (VerifM.Env.withEnv ρ (σ.subst.eval ρ.env)) =
      Assertion.pre Θ OuterQ pt (VerifM.Env.withEnv ρ (σ.subst.eval ρ.env)) := rfl
  rw [hpre]
  exact BIBase.Entails.trans
    (by
      have hpost' : st.sl Θ ρ ∗ emp ⊢
          Assertion.post Θ Φpost pt (VerifM.Env.withEnv ρ (σ.subst.eval ρ.env)) := by
        simpa [VerifM.Env.withEnv] using hpost
      exact sep_comm.1.trans (sep_mono_right (sep_emp.2.trans hpost')))
    (Assertion.pre_post_combine Θ
      (ρ := VerifM.Env.withEnv ρ (σ.subst.eval ρ.env))
      (m := pt)
      (Φ := OuterQ)
      (Ψ := Φpost)
      (R := R)
      (fun _ _ => by
        iintro H
        icases H with ⟨HQ, Hcont⟩
        iapply Hcont
        iexact HQ))
