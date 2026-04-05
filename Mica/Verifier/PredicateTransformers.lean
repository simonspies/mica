import Mica.TinyML.Typed
import Mica.TinyML.Typing
import Mica.TinyML.WeakestPre
import Mica.FOL.Printing
import Mica.Verifier.Monad
import Mica.Verifier.Atoms
import Mica.Verifier.Assertions
import Mica.Verifier.Utils
import Mica.Base.Fresh
import Mathlib.Data.Finmap

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

def PredTrans.apply (Φ : Runtime.Val → Prop) (m : PredTrans) (ρ : Env) : Prop :=
  Assertion.pre (fun post ρ' =>
    ∀ v : Runtime.Val, Assertion.post (fun () _ => Φ v) post.2 (ρ'.updateConst .value post.1 v)
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
  VerifM.assume (.eq .value (.const (.uninterpreted resVar.name .value)) result)
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

theorem PredTrans.apply_env_agree {pt : PredTrans} {Φ : Runtime.Val → Prop}
    {ρ ρ' : Env} {Δ : Signature}
    (hwf : pt.wfIn Δ) (hagree : Env.agreeOn Δ ρ ρ')
    (h : PredTrans.apply Φ pt ρ) : PredTrans.apply Φ pt ρ' := by
  unfold PredTrans.apply at h ⊢
  apply Assertion.pre_env_agree hwf hagree _ h
  intro ⟨postName, postBody⟩ Δ' ρ₁ ρ₂ hwf_post hagree_post hpost v
  exact Assertion.post_env_agree hwf_post
    (Env.agreeOn_declVar hagree_post)
    (fun _ _ _ _ _ _ h => h) (hpost v)

-- ---------------------------------------------------------------------------
-- Correctness
-- ---------------------------------------------------------------------------

theorem PredTrans.call_correct (pt : PredTrans) (σ : FiniteSubst)
    (st : TransState) (ρ : Env)
    (Ψ : Term .value → TransState → Env → Prop) (Φ : Runtime.Val → Prop) :
    pt.wfIn (Signature.ofVars σ.dom) →
    (Signature.ofVars σ.dom).wf →
    σ.wf st.decls →
    VerifM.eval (PredTrans.call σ pt) st ρ Ψ →
    (∀ v st' ρ' t, Ψ t st' ρ' → t.wfIn st'.decls → t.eval ρ' = v → Φ v) →
    PredTrans.apply Φ pt (σ.subst.eval ρ) := by
  intro hwf hdomwf hσwf heval hΨ
  simp only [PredTrans.call] at heval
  have hb := VerifM.eval_bind _ _ _ _ heval
  let retWf : (String × Assertion Unit) → Signature → Prop :=
    fun post Δ' => Assertion.wfIn (fun _ _ => True) (Δ'.declVar ⟨post.1, .value⟩) post.2
  let Φpost : (String × Assertion Unit) → Env → Prop :=
    fun post ρ' => ∀ v : Runtime.Val, Assertion.post (fun () _ => Φ v) post.2 (ρ'.updateConst .value post.1 v)
  have hpre : Assertion.pre Φpost pt (σ.subst.eval ρ) := by
    exact Assertion.prove_correct pt σ retWf st ρ _ Φpost
      (fun ⟨postName, postBody⟩ Δ' ρ₁ ρ₂ hwf_post hagree hpost v =>
        Assertion.post_env_agree hwf_post
          (Env.agreeOn_declVar hagree)
          (fun _ _ _ _ _ _ h => h) (hpost v))
      hσwf hdomwf hwf hb
      (fun σ₁ ⟨postName, postBody⟩ st₁ ρ₁ hcont hσ₁wf hσ₁domwf hwf₁ v => by
  have hb2 := VerifM.eval_bind _ _ _ _ hcont
  have hdecl := VerifM.eval_decl hb2
  set resVar := st₁.freshConst (some postName) .value
  have hfresh_decls : resVar.name ∉ st₁.decls.allNames :=
    fresh_not_mem (addNumbers postName) st₁.decls.allNames (addNumbers_injective _)
  have hfresh_range : resVar.name ∉ σ₁.range.allNames :=
    fun h => hfresh_decls (Signature.allNames_subset hσ₁wf.2.1 _ h)
  specialize hdecl v
  have hb3 := VerifM.eval_bind _ _ _ _ hdecl
  set σ₂ := σ₁.rename ⟨postName, .value⟩ resVar.name
  have hσ₂wf : σ₂.wf (st₁.decls.addConst resVar) := by
    simpa [σ₂] using
      (FiniteSubst.rename_wf (σ := σ₁) (v := ⟨postName, .value⟩) (name' := resVar.name) hσ₁wf hfresh_range)
  have hσ₂domwf : (Signature.ofVars σ₂.dom).wf := by
    simpa [σ₂] using
      (FiniteSubst.rename_dom_wf (σ := σ₁) (v := ⟨postName, .value⟩) (name' := resVar.name) hσ₁domwf)
  have hwf₁' : Assertion.wfIn (fun _ _ => True) (Signature.ofVars σ₂.dom) postBody := by
    simpa [σ₂, FiniteSubst.rename, Signature.ofVars, Signature.declVar] using hwf₁
  -- Use decls_grow to track that resVar stays in decls and env agrees
  have hgrow := VerifM.eval.decls_grow (ρ₁.updateConst .value resVar.name v) hb3
  have hassume := Assertion.assume_correct postBody σ₂ (fun _ _ => True)
    { st₁ with decls := st₁.decls.addConst resVar }
    (ρ₁.updateConst .value resVar.name v) _ (fun () _ => Φ v)
    (fun _ _ _ _ _ _ h => h)
    hσ₂wf hσ₂domwf hwf₁' hgrow
    (fun _ () st₂ ρ₂ ⟨hsub, hagree, hcont'⟩ _ _ _ => by
      have hret := VerifM.eval_ret hcont'
      have hwfst₂ : st₂.decls.wf := (VerifM.eval.wf hcont').namesDisjoint
      apply hΨ _ st₂ ρ₂ (.const (.uninterpreted resVar.name .value)) hret
      · simp only [Term.wfIn, Const.wfIn]
        refine ⟨hsub.consts resVar (List.Mem.head _), ?_⟩
        intro τ' hvar
        exact Signature.wf_no_var_of_const hwfst₂ (hsub.consts resVar (List.Mem.head _)) hvar
      · simp only [Term.eval, Const.denote]
        have := hagree.2.1 resVar (List.Mem.head _)
        simpa [Env.lookupConst, Env.updateConst] using this.symm
        )
  -- Transport from σ₂.subst.eval ρ₂ to (σ₁.subst.eval ρ₁).updateConst .value postName v
  exact Assertion.post_env_agree hwf₁
    (by
      simpa [σ₂, FiniteSubst.rename, Signature.ofVars, Signature.declVar] using
        (FiniteSubst.rename_agreeOn (σ := σ₁) (v := ⟨postName, .value⟩) (c := resVar)
          hσ₁wf.1 hfresh_range rfl))
    (fun _ _ _ _ _ _ h => h) hassume)
  simpa [PredTrans.apply, Φpost]

theorem PredTrans.implement_correct (pt : PredTrans) (σ : FiniteSubst)
    (body : VerifM (Term .value))
    (st : TransState) (ρ : Env) (Φ : Runtime.Val → Prop) (R : Prop) :
    pt.wfIn (Signature.ofVars σ.dom) →
    (Signature.ofVars σ.dom).wf →
    σ.wf st.decls →
    VerifM.eval (PredTrans.implement σ pt body) st ρ (fun _ _ _ => True) →
    PredTrans.apply Φ pt (σ.subst.eval ρ) →
    (∀ st' ρ', st.decls.Subset st'.decls → Env.agreeOn st.decls ρ ρ' →
      VerifM.eval body st' ρ'
      (fun result st'' ρ'' => result.wfIn st''.decls → Φ (result.eval ρ'')) → R) →
    R := by
  intro hwf hdomwf hσwf heval happly hR
  simp only [PredTrans.implement] at heval
  have hb := VerifM.eval_bind _ _ _ _ heval
  -- Strengthen with decls_grow to carry subset/agree info into the assume_correct callback
  have hb_grow := VerifM.eval.decls_grow ρ hb
  -- Choose Φ_post so that pre_post_combine with apply gives R
  let retWf : (String × Assertion Unit) → Signature → Prop :=
    fun post Δ' => Assertion.wfIn (fun _ _ => True) (Δ'.declVar ⟨post.1, .value⟩) post.2
  set Φ_post : (String × Assertion Unit) → Env → Prop :=
    fun ⟨postName, postBody⟩ ρ_log =>
      (∀ v, Assertion.post (fun () _ => Φ v) postBody (ρ_log.updateConst .value postName v)) → R
  have hpost := Assertion.assume_correct pt σ retWf
    st ρ _ Φ_post
    (fun ⟨pN, pB⟩ Δ' ρ₁ ρ₂ hwf_post hagree hΦ =>
      fun hpost_all => hΦ (fun v => Assertion.post_env_agree hwf_post
        (Env.agreeOn_symm (Env.agreeOn_declVar hagree))
        (fun _ _ _ _ _ _ h => h) (hpost_all v)))
    hσwf hdomwf hwf hb_grow
    -- Callback for assume_correct: given continuation eval + subset/agree, produce Φ_post
    (fun σ₁ ⟨postName, postBody⟩ st₁ ρ₁ ⟨hdsub_st, hagree_st, hcont⟩ hσ₁wf hσ₁domwf hwf_postBody hpost_all => by
      -- Decompose continuation: body >>= decl >>= assume >>= prove >>= ret
      have hcont_body := VerifM.eval_bind _ _ _ _ hcont
      -- Strengthen with decls_grow to track subset/agree through body
      have hcont_grow := VerifM.eval.decls_grow ρ₁ hcont_body
      -- Weaken body postcondition to what we need
      exact hR st₁ ρ₁ hdsub_st hagree_st <|
        hcont_grow.mono fun result st_b ρ_b ⟨hdsub_b, hagree_b, hrest⟩ => by
        -- Given the rest of the continuation succeeds, show result.wfIn → Φ (result.eval)
        intro hwf_result
        -- Decompose: decl, assume eq, prove
        have hb2 := VerifM.eval_bind _ _ _ _ hrest
        have hdecl := VerifM.eval_decl hb2
        set resVar := st_b.freshConst (some postName) .value
        have hfresh_decls_b : resVar.name ∉ st_b.decls.allNames :=
          fresh_not_mem (addNumbers postName) st_b.decls.allNames (addNumbers_injective _)
        have hfresh_range_b : resVar.name ∉ σ₁.range.allNames :=
          fun hmem => hfresh_decls_b (Signature.allNames_subset (Signature.Subset.trans hσ₁wf.2.1 hdsub_b) _ hmem)
        specialize hdecl (result.eval ρ_b)
        have hb3 := VerifM.eval_bind _ _ _ _ hdecl
        -- The eq formula
        have heq_wf : (Formula.eq Srt.value (Term.const (.uninterpreted resVar.name .value)) result).wfIn
            (st_b.decls.addConst resVar) := by
          have hwfst_b' : (st_b.decls.addConst resVar).wf :=
            (TransState.freshConst.wf _ (VerifM.eval.wf hrest)).namesDisjoint
          refine ⟨?_, Term.wfIn_mono result hwf_result (Signature.Subset.subset_addConst _ _) hwfst_b'⟩
          · simp only [Term.wfIn, Const.wfIn, Signature.addConst]
            refine ⟨List.Mem.head _, ?_⟩
            intro τ' hvar
            exact hfresh_decls_b (Signature.mem_allNames_of_var hvar)
        have heq_holds : (Formula.eq Srt.value (Term.const (.uninterpreted resVar.name .value)) result).eval
            (ρ_b.updateConst .value resVar.name (result.eval ρ_b)) := by
          simp only [Formula.eval, Term.eval, Const.denote]
          simpa [Env.lookupConst, Env.updateConst] using
            (Term.eval_env_agree hwf_result (agreeOn_update_fresh_const hfresh_decls_b))
        have hassume := VerifM.eval_assume hb3 heq_wf heq_holds
        -- Prove σ₂ postBody
        set σ₂ := σ₁.rename ⟨postName, .value⟩ resVar.name
        have hσ₂wf : σ₂.wf (st_b.decls.addConst resVar) :=
          by
            simpa [σ₂] using
              (FiniteSubst.rename_wf (σ := σ₁) (v := ⟨postName, .value⟩)
                (name' := resVar.name) ⟨hσ₁wf.1, Signature.Subset.trans hσ₁wf.2.1 hdsub_b, hσ₁wf.2.2⟩
                hfresh_range_b)
        have hσ₂domwf : (Signature.ofVars σ₂.dom).wf := by
          simpa [σ₂] using
            (FiniteSubst.rename_dom_wf (σ := σ₁) (v := ⟨postName, .value⟩) (name' := resVar.name) hσ₁domwf)
        have hb4 := VerifM.eval_bind _ _ _ _ hassume
        have hwf_postBody' : Assertion.wfIn (fun _ _ => True) (Signature.ofVars σ₂.dom) postBody := by
          simpa [σ₂, FiniteSubst.rename, Signature.ofVars, Signature.declVar] using hwf_postBody
        -- From prove_correct: get Assertion.pre on postBody
        have hpre := Assertion.prove_correct postBody σ₂ (fun _ _ => True)
          { st_b with decls := st_b.decls.addConst resVar,
                      asserts := Formula.eq Srt.value (Term.const (.uninterpreted resVar.name .value)) result :: st_b.asserts }
          (ρ_b.updateConst .value resVar.name (result.eval ρ_b)) _ (fun () _ => True)
          (fun _ _ _ _ _ _ h => h)
          hσ₂wf hσ₂domwf hwf_postBody' hb4 (fun _ () _ _ _ _ _ _ => trivial)
        -- Transport pre to (σ₁.subst.eval ρ₁).updateConst .value postName (result.eval ρ_b)
        have hag_rename := @FiniteSubst.rename_agreeOn σ₁ ⟨postName, .value⟩ resVar
          ρ_b (result.eval ρ_b) hσ₁wf.1 hfresh_range_b rfl
        -- Need to go from σ₁.subst.eval ρ_b to σ₁.subst.eval ρ₁
        have hag_eval := FiniteSubst.eval_agreeOn hσ₁wf.1
          (Env.agreeOn_mono hσ₁wf.2.1 (Env.agreeOn_symm hagree_b))
        have hag_eval' : Env.agreeOn (Signature.ofVars σ₂.dom)
            ((σ₁.subst.eval ρ_b).updateConst .value postName (result.eval ρ_b))
            ((σ₁.subst.eval ρ₁).updateConst .value postName (result.eval ρ_b)) := by
          apply Env.agreeOn_mono
            (Δ₁ := Signature.ofVars σ₂.dom)
            (Δ₂ := Signature.ofVars (⟨postName, .value⟩ :: σ₁.dom))
            (Signature.Subset.of_vars_subset_ofVars (vars := σ₂.dom) (vars' := ⟨postName, .value⟩ :: σ₁.dom)
              (fun x hx => by
              simp [σ₂, FiniteSubst.rename] at hx ⊢
              rcases hx with rfl | ⟨hx, _⟩
              · exact Or.inl rfl
              · exact Or.inr hx))
          exact Env.agreeOn_update hag_eval
        have hag_combined : Env.agreeOn (Signature.ofVars σ₂.dom)
            (σ₂.subst.eval (ρ_b.updateConst .value resVar.name (result.eval ρ_b)))
            ((σ₁.subst.eval ρ₁).updateConst .value postName (result.eval ρ_b)) :=
          Env.agreeOn_trans hag_rename hag_eval'
        have hpre' := Assertion.pre_env_agree hwf_postBody'
          (by
            simpa [σ₂, FiniteSubst.rename, Signature.ofVars, Signature.declVar] using hag_combined)
          (fun _ _ _ _ _ _ h => h) hpre
        -- Combine with hpost_all via pre_post_combine
        exact Assertion.pre_post_combine hpre' (hpost_all (result.eval ρ_b))
          (fun () _ _ hΦ => hΦ))
  -- Now use pre_post_combine on happly (pre) and hpost (post) to get R
  exact Assertion.pre_post_combine happly hpost
    (fun ⟨postName, postBody⟩ _ hpre_all hΦ_post => hΦ_post hpre_all)
