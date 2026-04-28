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


/-!
# Predicate Transformers

Defines `PredTrans` and `SpecPredicate`.
-/

-- ---------------------------------------------------------------------------
-- Core types
-- ---------------------------------------------------------------------------

def PredTrans := Assertion (Pred (Assertion Unit))
abbrev SpecPredicate := MultiPred PredTrans

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

theorem PredTrans.checkWf_ok {pt : PredTrans} {Δ : Signature}
    (h : pt.checkWf Δ = .ok ()) : pt.wfIn Δ :=
  Assertion.checkWf_ok
    (fun _ _ hok => Assertion.checkWf_ok (fun _ _ _ => trivial) hok)
    h

-- ---------------------------------------------------------------------------
-- Semantics
-- ---------------------------------------------------------------------------

def PredTrans.apply (Φ : Runtime.Val → iProp) (m : PredTrans) (ρ : VerifM.Env) : iProp :=
  Assertion.pre (fun post ρ' =>
    BIBase.forall fun v : Runtime.Val =>
      Assertion.post (fun () _ => Φ v) post.2 (ρ'.updateConst .value post.1 v)
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

theorem PredTrans.wfIn_mono {pt : PredTrans} {Δ Δ' : Signature}
    (h : pt.wfIn Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) : pt.wfIn Δ' := by
  unfold PredTrans.wfIn at h ⊢
  exact Assertion.wfIn_mono pt _
    (fun post ds ds' hsub' hwf' hpost =>
      Assertion.wfIn_mono post.2 _ (fun _ _ _ _ _ h => h) hpost
        (Signature.Subset.declVar hsub' ⟨post.1, .value⟩)
        (Signature.wf_declVar hwf'))
    h hsub hwf

theorem PredTrans.apply_env_agree {pt : PredTrans} {Φ : Runtime.Val → iProp}
    {ρ ρ' : VerifM.Env} {Δ : Signature}
    (hwf : pt.wfIn Δ) (hagree : VerifM.Env.agreeOn Δ ρ ρ') :
    PredTrans.apply Φ pt ρ ⊢ PredTrans.apply Φ pt ρ' := by
  unfold PredTrans.apply at ⊢
  apply Assertion.pre_env_agree hwf hagree
  intro ⟨postName, postBody⟩ Δ' ρ₁ ρ₂ hwf_post hagree_post
  apply forall_intro
  intro v
  exact (forall_elim v).trans <|
    Assertion.post_env_agree hwf_post
      (VerifM.Env.agreeOn_declVar hagree_post)
      (fun _ _ _ _ _ _ => .rfl)

-- ---------------------------------------------------------------------------
-- Correctness
-- ---------------------------------------------------------------------------

theorem PredTrans.call_correct (pt : PredTrans) (Δ_base : Signature) (σ : FiniteSubst)
    (st : TransState) (ρ : VerifM.Env)
    (Ψ : Term .value → TransState → VerifM.Env → Prop) (Φ : Runtime.Val → iProp) R :
    pt.wfIn (Δ_base.declVars σ.dom) →
    σ.wfIn Δ_base st.decls →
    VerifM.eval (PredTrans.call σ pt) st ρ Ψ →
    (∀ v st' ρ' t, Ψ t st' ρ' → t.wfIn st'.decls → t.eval ρ'.env = v →
      (st'.sl ρ' ∗ R ⊢ Φ v)) →
    st.sl ρ ∗ R ⊢ PredTrans.apply Φ pt (VerifM.Env.withEnv ρ (σ.subst.eval ρ.env)) := by
  intro hwf hσwf heval hΨ
  simp only [PredTrans.call] at heval
  have hb := VerifM.eval_bind _ _ _ _ heval
  let retWf : (String × Assertion Unit) → Signature → Prop :=
    fun post Δ' => Assertion.wfIn (fun _ _ => True) (Δ'.declVar ⟨post.1, .value⟩) post.2
  let Φpost : (String × Assertion Unit) → VerifM.Env → iProp :=
    fun post ρ' =>
      BIBase.forall fun v : Runtime.Val =>
        Assertion.post (fun () _ => Φ v) post.2 (ρ'.updateConst .value post.1 v)
  let Ψcall : (FiniteSubst × (String × Assertion Unit)) → TransState → VerifM.Env → Prop :=
    fun r st' ρ' =>
      match r with
      | (σ₁, postName, postBody) => (do
          let resVar ← VerifM.decl (some postName) Srt.value
          let _ ← Assertion.assume (σ₁.rename ⟨postName, .value⟩ resVar.name) postBody
          Pure.pure (Term.const (.uninterpreted resVar.name .value))).eval st' ρ' Ψ
  have hpre : st.sl ρ ∗ R ⊢ Assertion.pre Φpost pt (VerifM.Env.withEnv ρ (σ.subst.eval ρ.env)) := by
    exact Assertion.prove_correct pt Δ_base σ retWf st ρ Ψcall Φpost R
      (fun ⟨postName, postBody⟩ Δ' ρ₁ ρ₂ hwf_post hagree =>
        forall_intro fun v =>
          (forall_elim v).trans <|
            Assertion.post_env_agree hwf_post
              (VerifM.Env.agreeOn_declVar hagree)
              (fun _ _ _ _ _ _ => .rfl))
      hσwf hwf hb
      (fun σ₁ ⟨postName, postBody⟩ st₁ ρ₁ hcont hσ₁wf hwf₁ => by
        apply forall_intro
        intro v
        rcases hσ₁wf with ⟨hσ₁subst, hσ₁base, hσ₁use, hσ₁srcwf, hσ₁rangewf, hσ₁usewf, hσ₁basevars⟩
        have hσ₁wf : σ₁.wfIn Δ_base st₁.decls :=
          ⟨hσ₁subst, hσ₁base, hσ₁use, hσ₁srcwf, hσ₁rangewf, hσ₁usewf, hσ₁basevars⟩
        have hb2 := VerifM.eval_bind _ _ _ _ hcont
        have hdecl := VerifM.eval_decl hb2
        set resVar := st₁.freshConst (some postName) .value
        have hfresh_decls : resVar.name ∉ st₁.decls.allNames :=
          Fresh.freshNumbers_not_mem postName st₁.decls.allNames
        have hfresh_range : resVar.name ∉ σ₁.range.allNames :=
          fun h => hfresh_decls (Signature.allNames_subset hσ₁use _ h)
        specialize hdecl v
        have hb3 := VerifM.eval_bind _ _ _ _ hdecl
        set σ₂ := σ₁.rename ⟨postName, .value⟩ resVar.name
        have hσ₂wf : σ₂.wfIn Δ_base (st₁.decls.addConst resVar) := by
          simpa [σ₂] using
            (FiniteSubst.rename_wfIn (σ := σ₁) (Δ_base := Δ_base) (Δ_use := st₁.decls)
              (v := ⟨postName, .value⟩) (name' := resVar.name)
              hσ₁wf hfresh_range hfresh_decls)
        have hwf₁' : Assertion.wfIn (fun _ _ => True) (Δ_base.declVars σ₂.dom) postBody := by
          simpa [σ₂, FiniteSubst.rename_source_eq] using hwf₁
        have hgrow := VerifM.eval.decls_grow (ρ₁.updateConst .value resVar.name v) hb3
        have hassume := Assertion.assume_correct postBody Δ_base σ₂ (fun _ _ => True)
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
            · simp only [Term.wfIn, Const.wfIn]
              refine ⟨hsub.consts resVar (List.Mem.head _), ?_, ?_⟩
              · intro τ' hvar
                exact Signature.wf_no_var_of_const hwfst₂ (hsub.consts resVar (List.Mem.head _)) hvar
              · intro τ' hc'
                exact Signature.wf_unique_const hwfst₂ (hsub.consts resVar (List.Mem.head _)) hc'
            · simp only [Term.eval, Const.denote]
              have := hagree.2.1 resVar (List.Mem.head _)
              simpa [Env.lookupConst, Env.updateConst] using this.symm)
        have hinterp_bi :
            st₁.sl ρ₁ ⊣⊢ st₁.sl (ρ₁.updateConst .value resVar.name v) :=
          SpatialContext.interp_env_agree (VerifM.eval.wf hcont).ownsWf
            (Env.agreeOn_update_fresh_const (c := resVar) hfresh_decls)
        exact (sep_mono hinterp_bi.1 (by
          iintro HR
          iexact HR)).trans <| hassume.trans <| Assertion.post_env_agree hwf₁'
          (by
            simpa [σ₂, VerifM.Env.agreeOn, VerifM.Env.withEnv_env, VerifM.Env.updateConst] using
              (FiniteSubst.rename_agreeOn (σ := σ₁) (Δ_base := Δ_base) (Δ_use := st₁.decls)
                (v := ⟨postName, .value⟩) (name' := resVar.name)
                (ρ := ρ₁.env) (u := v) hσ₁wf hfresh_range))
          (fun _ _ _ _ _ _ => .rfl))
  simpa [PredTrans.apply, Φpost] using hpre


theorem PredTrans.implement_correct (pt : PredTrans) (Δ_base : Signature) (σ : FiniteSubst)
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
        (st''.sl ρ'' ∗ Q ∗ (Φ (result.eval ρ''.env) -∗ S) ⊢ S)) →
      st'.sl ρ' ∗ Q ⊢ R) →
    st.sl ρ ∗ PredTrans.apply Φ pt (VerifM.Env.withEnv ρ (σ.subst.eval ρ.env)) ⊢ R := by
  intro hwf hσwf heval hbody
  simp only [PredTrans.implement] at heval
  have hb := VerifM.eval_bind _ _ _ _ heval
  have hb_grow := VerifM.eval.decls_grow ρ hb
  let retWf : (String × Assertion Unit) → Signature → Prop :=
    fun post Δ' => Assertion.wfIn (fun _ _ => True) (Δ'.declVar ⟨post.1, .value⟩) post.2
  let OuterQ : (String × Assertion Unit) → VerifM.Env → iProp :=
    fun ⟨postName, postBody⟩ ρ' =>
      BIBase.forall fun v : Runtime.Val =>
        Assertion.post (fun () _ => Φ v) postBody (ρ'.updateConst .value postName v)
  let Φpost : (String × Assertion Unit) → VerifM.Env → iProp :=
    fun a ρ' => OuterQ a ρ' -∗ R
  have hpost := Assertion.assume_correct pt Δ_base σ retWf
    st ρ _ Φpost emp
    (fun ⟨postName, postBody⟩ Δ' ρ₁ ρ₂ hwf_post hagree => by
      refine wand_intro ?_
      iintro H
      icases H with ⟨Hcont, HQ₂⟩
      iapply Hcont
      apply forall_intro
      intro v
      exact (forall_elim v).trans <|
        Assertion.post_env_agree hwf_post
          (Env.agreeOn_symm (Env.agreeOn_declVar hagree))
          (fun _ _ _ _ _ _ => .rfl))
    hσwf hwf hb_grow
    (fun σ₁ ⟨postName, postBody⟩ st₁ ρ₁ ⟨hdsub_st, hagree_st, hcont⟩ hσ₁wf hwf_postBody => by
      apply BIBase.Entails.trans sep_comm.1
      apply BIBase.Entails.trans emp_sep.1
      rcases hσ₁wf with ⟨hσ₁subst, hσ₁base, hσ₁use, hσ₁srcwf, hσ₁rangewf, hσ₁usewf, hσ₁basevars⟩
      have hσ₁wf : σ₁.wfIn Δ_base st₁.decls :=
        ⟨hσ₁subst, hσ₁base, hσ₁use, hσ₁srcwf, hσ₁rangewf, hσ₁usewf, hσ₁basevars⟩
      have hcont_body := VerifM.eval_bind _ _ _ _ hcont
      change st₁.sl ρ₁ ⊢ OuterQ (postName, postBody) (VerifM.Env.withEnv ρ₁ (σ₁.subst.eval ρ₁.env)) -∗ R
      refine wand_intro ?_
      refine hbody st₁ ρ₁ _ hdsub_st hagree_st ?_
      refine (VerifM.eval.decls_grow ρ₁ hcont_body).mono ?_
      intro result st₂ ρ₂ ⟨hdsub_body, hagree_body, hrest⟩ S hwf_result
      have hb2 := VerifM.eval_bind _ _ _ _ hrest
      have hdecl := VerifM.eval_decl hb2
      set resVar := st₂.freshConst (some postName) .value
      have hfresh_decls : resVar.name ∉ st₂.decls.allNames :=
        Fresh.freshNumbers_not_mem postName st₂.decls.allNames
      have hfresh_range : resVar.name ∉ σ₁.range.allNames :=
        fun hmem => hfresh_decls (Signature.allNames_subset (Signature.Subset.trans hσ₁use hdsub_body) _ hmem)
      specialize hdecl (result.eval ρ₂.env)
      have hb3 := VerifM.eval_bind _ _ _ _ hdecl
      have heq_wf : (Formula.eq Srt.value (Term.const (.uninterpreted resVar.name .value)) result).wfIn
          (st₂.decls.addConst resVar) := by
        have hwf' : (st₂.decls.addConst resVar).wf :=
          (TransState.freshConst.wf _ (VerifM.eval.wf hrest)).namesDisjoint
        refine ⟨?_, Term.wfIn_mono result hwf_result (Signature.Subset.subset_addConst _ _) hwf'⟩
        simp only [Term.wfIn, Const.wfIn, Signature.addConst]
        refine ⟨List.Mem.head _, ?_, ?_⟩
        · intro τ' hvar
          exact hfresh_decls (Signature.mem_allNames_of_var hvar)
        · intro τ' hc'
          exact Signature.wf_unique_const hwf' (List.Mem.head _) hc'
      have heq_holds : (Formula.eq Srt.value (Term.const (.uninterpreted resVar.name .value)) result).eval
          (ρ₂.updateConst .value resVar.name (result.eval ρ₂.env)).env := by
        simp only [Formula.eval, Term.eval, Const.denote]
        simpa [Env.lookupConst, Env.updateConst] using
          (Term.eval_env_agree hwf_result (Env.agreeOn_update_fresh_const hfresh_decls))
      have hassume := VerifM.eval_assumePure hb3 heq_wf heq_holds
      set σ₂ := σ₁.rename ⟨postName, .value⟩ resVar.name
      have hσ₁wf₂ : σ₁.wfIn Δ_base st₂.decls := by
        exact ⟨hσ₁subst, hσ₁base, Signature.Subset.trans hσ₁use hdsub_body,
          hσ₁srcwf, hσ₁rangewf, (VerifM.eval.wf hrest).namesDisjoint, hσ₁basevars⟩
      have hσ₂wf : σ₂.wfIn Δ_base (st₂.decls.addConst resVar) := by
        simpa [σ₂] using
          (FiniteSubst.rename_wfIn (σ := σ₁) (Δ_base := Δ_base) (Δ_use := st₂.decls)
            (v := ⟨postName, .value⟩) (name' := resVar.name)
            hσ₁wf₂ hfresh_range hfresh_decls)
      have hb4 := VerifM.eval_bind _ _ _ _ hassume
      have hwf_postBody' : Assertion.wfIn (fun _ _ => True) (Δ_base.declVars σ₂.dom) postBody := by
        simpa [σ₂, FiniteSubst.rename_source_eq] using hwf_postBody
      let st₃ : TransState :=
        { st₂ with
          decls := st₂.decls.addConst resVar
          asserts := Formula.eq Srt.value (Term.const (.uninterpreted resVar.name .value)) result :: st₂.asserts }
      have hpre := @Assertion.prove_correct Unit postBody Δ_base σ₂ (fun _ _ => True)
        st₃
        (ρ₂.updateConst .value resVar.name (result.eval ρ₂.env))
        _ (fun () _ => Φ (result.eval ρ₂.env) -∗ S) (Φ (result.eval ρ₂.env) -∗ S)
        (fun _ _ _ _ _ _ => .rfl)
        hσ₂wf hwf_postBody' hb4
        (fun _ () st' ρ' hret _ _ => by
          show st'.sl ρ' ∗ (Φ (result.eval ρ₂.env) -∗ S) ⊢
            (Φ (result.eval ρ₂.env) -∗ S)
          exact sep_elim_r)
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
      have hpost_transport : Assertion.post (fun () _ => Φ (result.eval ρ₂.env)) postBody
          (VerifM.Env.withEnv ρ₁ ((σ₁.subst.eval ρ₁.env).updateConst .value postName (result.eval ρ₂.env))) ⊢
          Assertion.post (fun () _ => Φ (result.eval ρ₂.env)) postBody
            (VerifM.Env.withEnv (ρ₂.updateConst .value resVar.name (result.eval ρ₂.env))
              (σ₂.subst.eval (ρ₂.updateConst .value resVar.name (result.eval ρ₂.env)).env)) := by
        exact Assertion.post_env_agree hwf_postBody'
          (by
            simpa [VerifM.Env.agreeOn, VerifM.Env.withEnv]
              using (Env.agreeOn_symm (Env.agreeOn_trans hag_rename hag_eval')))
          (fun _ _ _ _ _ _ => .rfl)
      have howns_agree : st₃.sl ρ₂
            ⊢
          st₃.sl (ρ₂.updateConst .value resVar.name (result.eval ρ₂.env)) := by
        simpa using
          (SpatialContext.interp_env_agree (VerifM.eval.wf hrest).ownsWf
            (Env.agreeOn_update_fresh_const hfresh_decls)).1
      have hpre_final :
          st₂.sl ρ₂ ∗ (Φ (result.eval ρ₂.env) -∗ S) ⊢
            Assertion.pre (fun () _ => Φ (result.eval ρ₂.env) -∗ S) postBody
              (VerifM.Env.withEnv (ρ₂.updateConst .value resVar.name (result.eval ρ₂.env))
                (σ₂.subst.eval (ρ₂.updateConst .value resVar.name (result.eval ρ₂.env)).env)) := by
        have hinput :
            st₂.sl ρ₂ ∗ (Φ (result.eval ρ₂.env) -∗ S) ⊢
              st₃.sl (ρ₂.updateConst .value resVar.name (result.eval ρ₂.env)) ∗
                (Φ (result.eval ρ₂.env) -∗ S) := by
          iintro H
          icases H with ⟨Howns, Hwand⟩
          isplitl [Howns]
          · iapply howns_agree
            simp [st₃, TransState.sl]
          · iexact Hwand
        exact hinput.trans hpre
      have hpost_final :
          OuterQ (postName, postBody) (VerifM.Env.withEnv ρ₁ (σ₁.subst.eval ρ₁.env)) ⊢
            Assertion.post (fun () _ => Φ (result.eval ρ₂.env)) postBody
              (VerifM.Env.withEnv (ρ₂.updateConst .value resVar.name (result.eval ρ₂.env))
                (σ₂.subst.eval (ρ₂.updateConst .value resVar.name (result.eval ρ₂.env)).env)) := by
        exact (forall_elim (result.eval ρ₂.env)).trans hpost_transport
      iintro H
      icases H with ⟨Howns, HQ, Hwand⟩
      iapply (Assertion.pre_post_combine
        (ρ := VerifM.Env.withEnv (ρ₂.updateConst .value resVar.name (result.eval ρ₂.env))
          (σ₂.subst.eval (ρ₂.updateConst .value resVar.name (result.eval ρ₂.env)).env))
        (m := postBody)
        (Φ := fun () _ => Φ (result.eval ρ₂.env) -∗ S)
        (Ψ := fun () _ => Φ (result.eval ρ₂.env))
        (R := S)
        (fun () _ => by
          iintro H
          icases H with ⟨Hwand, HΦ⟩
          iapply Hwand
          iexact HΦ))
      isplitl [Howns Hwand]
      · iapply hpre_final
        isplitl [Howns]
        · iexact Howns
        · iexact Hwand
      · iapply hpost_final
        iexact HQ
      )
  have hpre :
      PredTrans.apply Φ pt (VerifM.Env.withEnv ρ (σ.subst.eval ρ.env)) =
      Assertion.pre OuterQ pt (VerifM.Env.withEnv ρ (σ.subst.eval ρ.env)) := rfl
  rw [hpre]
  exact BIBase.Entails.trans
    (by
      iintro H
      icases H with ⟨Howns, Happ⟩
      isplitr [Howns]
      · iexact Happ
      · have hpost' : st.sl ρ ∗ emp ⊢ Assertion.post Φpost pt (VerifM.Env.withEnv ρ (σ.subst.eval ρ.env)) := by
          simpa [VerifM.Env.withEnv] using hpost
        iapply hpost'
        isplitl
        . iexact Howns
        . iemp_intro)
    (Assertion.pre_post_combine
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
