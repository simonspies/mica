import Mica.TinyML.Expr
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
-- TODO: For now, we only support single argument specs. We will improve on this in the future.
abbrev SpecPredicate := Pred PredTrans

-- ---------------------------------------------------------------------------
-- Well-formedness
-- ---------------------------------------------------------------------------

/-- A predicate transformer is well-formed when its outer assertion is well-formed
    and each inner postcondition assertion is also well-formed (in the extended context). -/
def PredTrans.wfIn (decls : List Var) (pt : PredTrans) : Prop :=
  Assertion.wfIn (fun post decls' => Assertion.wfIn (fun _ _ => True) (Var.mk post.1 .value :: decls') post.2) decls pt


def PredTrans.checkWf (decls : List Var) (pt : PredTrans) : Except String Unit :=
  Assertion.checkWf
    (fun post decls' => Assertion.checkWf (fun _ _ => .ok ()) (Var.mk post.1 .value :: decls') post.2)
    decls pt

theorem PredTrans.checkWf_ok {pt : PredTrans} {decls : List Var}
    (h : pt.checkWf decls = .ok ()) : pt.wfIn decls :=
  Assertion.checkWf_ok
    (fun _ _ hok => Assertion.checkWf_ok (fun _ _ _ => trivial) hok)
    h

-- ---------------------------------------------------------------------------
-- Semantics
-- ---------------------------------------------------------------------------

def PredTrans.apply (Φ : TinyML.Val → Prop) (m : PredTrans) (ρ : Env) : Prop :=
  Assertion.pre (fun post ρ' =>
    ∀ v : TinyML.Val, Assertion.post (fun () _ => Φ v) post.2 (ρ'.update .value post.1 v)
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
  pure (.var .value resVar.name)

/-- The implementor side of a predicate transformer: assume the precondition (assume the outer
    assertion), run `body` to produce a result term, then assert the postcondition (prove the
    inner assertion). Dual to `PredTrans.call`. -/
def PredTrans.implement (σ : FiniteSubst) (pt : PredTrans) (body : VerifM (Term .value)) : VerifM Unit := do
  let (σ₁, (postName, postBody)) ← Assertion.assume σ pt
  let result ← body
  let resVar ← VerifM.decl (some postName) .value
  let σ₂ := σ₁.rename ⟨postName, .value⟩ resVar.name
  VerifM.assume (.eq .value (.var .value resVar.name) result)
  let (_, ()) ← Assertion.prove σ₂ postBody
  pure ()

-- ---------------------------------------------------------------------------
-- Properties
-- ---------------------------------------------------------------------------

theorem PredTrans.wfIn_mono {pt : PredTrans} {decls decls' : List Var}
    (h : pt.wfIn decls) (hsub : decls ⊆ decls') : pt.wfIn decls' := by
  unfold PredTrans.wfIn at h ⊢
  exact Assertion.wfIn_mono pt _
    (fun post ds ds' hsub' hwf =>
      Assertion.wfIn_mono post.2 _ (fun _ _ _ _ h => h) hwf
        (List.cons_subset_cons ⟨post.1, .value⟩ hsub'))
    h hsub

theorem PredTrans.apply_env_agree {pt : PredTrans} {Φ : TinyML.Val → Prop}
    {ρ ρ' : Env} {Δ : List Var}
    (hwf : pt.wfIn Δ) (hagree : Env.agreeOn Δ ρ ρ')
    (h : PredTrans.apply Φ pt ρ) : PredTrans.apply Φ pt ρ' := by
  unfold PredTrans.apply at h ⊢
  apply Assertion.pre_env_agree hwf hagree _ h
  intro ⟨postName, postBody⟩ decls ρ₁ ρ₂ hwf_post hagree_post hpost v
  exact Assertion.post_env_agree hwf_post (Env.agreeOn_update hagree_post)
    (fun _ _ _ _ _ _ h => h) (hpost v)

-- ---------------------------------------------------------------------------
-- Correctness
-- ---------------------------------------------------------------------------

theorem PredTrans.call_correct (pt : PredTrans) (σ : FiniteSubst)
    (st : TransState) (ρ : Env)
    (Ψ : Term .value → TransState → Env → Prop) (Φ : TinyML.Val → Prop) :
    pt.wfIn σ.dom →
    σ.wf st.decls →
    VerifM.eval (PredTrans.call σ pt) st ρ Ψ →
    (∀ v st' ρ' t, Ψ t st' ρ' → t.wfIn st'.decls → t.eval ρ' = v → Φ v) →
    PredTrans.apply Φ pt (σ.subst.eval ρ) := by
  intro hwf hσwf heval hΨ
  simp only [PredTrans.call] at heval
  have hb := VerifM.eval_bind _ _ _ _ heval
  apply Assertion.prove_correct pt σ
    (fun post decls' => Assertion.wfIn (fun _ _ => True) (Var.mk post.1 .value :: decls') post.2)
    st ρ _ _
    (fun ⟨postName, postBody⟩ decls ρ₁ ρ₂ hwf_post hagree hpost v =>
      Assertion.post_env_agree hwf_post (Env.agreeOn_update hagree)
        (fun _ _ _ _ _ _ h => h) (hpost v))
    hσwf hwf hb
  intro σ₁ ⟨postName, postBody⟩ st₁ ρ₁ hcont hσ₁wf hwf₁ v
  have hb2 := VerifM.eval_bind _ _ _ _ hcont
  have hdecl := VerifM.eval_decl hb2
  set resVar := st₁.freshVar (some postName) .value
  have hfresh_decls : resVar.name ∉ st₁.decls.map Var.name :=
    fresh_not_mem (addNumbers postName) (st₁.decls.map Var.name) (addNumbers_injective _)
  have hfresh_range : ⟨resVar.name, Srt.value⟩ ∉ σ₁.range := by
    intro hmem; exact hfresh_decls (List.mem_map.mpr ⟨⟨resVar.name, .value⟩, hσ₁wf.2 hmem, rfl⟩)
  specialize hdecl v
  have hb3 := VerifM.eval_bind _ _ _ _ hdecl
  set σ₂ := σ₁.rename ⟨postName, .value⟩ resVar.name
  have hσ₂wf : σ₂.wf (resVar :: st₁.decls) := FiniteSubst.rename_wf hσ₁wf hfresh_range
  -- Use decls_grow to track that resVar stays in decls and env agrees
  have hgrow := VerifM.eval.decls_grow (ρ₁.update .value resVar.name v) hb3
  have hassume := Assertion.assume_correct postBody σ₂ (fun _ _ => True)
    { st₁ with decls := resVar :: st₁.decls }
    (ρ₁.update .value resVar.name v) _ (fun () _ => Φ v)
    (fun _ _ _ _ _ _ h => h)
    hσ₂wf hwf₁ hgrow
    (fun _ () st₂ ρ₂ ⟨hsub, hagree, hcont'⟩ _ _ => by
      have hret := VerifM.eval_ret hcont'
      apply hΨ _ st₂ ρ₂ (.var .value resVar.name) hret
      · intro w hw
        simp only [Term.freeVars, List.mem_singleton] at hw
        subst hw
        exact hsub (List.mem_cons_self ..)
      · simp only [Term.eval]
        have := hagree ⟨resVar.name, .value⟩ (List.mem_cons_self ..)
        simp only [Env.lookup_update_same] at this
        exact this.symm)
  -- Transport from σ₂.subst.eval ρ₂ to (σ₁.subst.eval ρ₁).update .value postName v
  exact Assertion.post_env_agree hwf₁
    (FiniteSubst.rename_agreeOn hσ₁wf.1 hfresh_range)
    (fun _ _ _ _ _ _ h => h) hassume

theorem PredTrans.implement_correct (pt : PredTrans) (σ : FiniteSubst)
    (body : VerifM (Term .value))
    (st : TransState) (ρ : Env) (Φ : TinyML.Val → Prop) (R : Prop) :
    pt.wfIn σ.dom →
    σ.wf st.decls →
    VerifM.eval (PredTrans.implement σ pt body) st ρ (fun _ _ _ => True) →
    PredTrans.apply Φ pt (σ.subst.eval ρ) →
    (∀ st' ρ', st.decls ⊆ st'.decls → ρ.agreeOn st.decls ρ' →
      VerifM.eval body st' ρ'
      (fun result st'' ρ'' => result.wfIn st''.decls → Φ (result.eval ρ'')) → R) →
    R := by
  intro hwf hσwf heval happly hR
  simp only [PredTrans.implement] at heval
  have hb := VerifM.eval_bind _ _ _ _ heval
  -- Strengthen with decls_grow to carry subset/agree info into the assume_correct callback
  have hb_grow := VerifM.eval.decls_grow ρ hb
  -- Choose Φ_post so that pre_post_combine with apply gives R
  set Φ_post : (String × Assertion Unit) → Env → Prop :=
    fun ⟨postName, postBody⟩ ρ_log =>
      (∀ v, Assertion.post (fun () _ => Φ v) postBody (ρ_log.update .value postName v)) → R
  have hpost := Assertion.assume_correct pt σ
    (fun post decls' => Assertion.wfIn (fun _ _ => True) (Var.mk post.1 .value :: decls') post.2)
    st ρ _ Φ_post
    (fun ⟨pN, pB⟩ decls ρ₁ ρ₂ hwf_post hagree hΦ =>
      fun hpost_all => hΦ (fun v => Assertion.post_env_agree hwf_post
        (Env.agreeOn_update (Env.agreeOn_symm hagree)) (fun _ _ _ _ _ _ h => h) (hpost_all v)))
    hσwf hwf hb_grow
    -- Callback for assume_correct: given continuation eval + subset/agree, produce Φ_post
    (fun σ₁ ⟨postName, postBody⟩ st₁ ρ₁ ⟨hdsub_st, hagree_st, hcont⟩ hσ₁wf hwf_postBody => by
      -- Φ_post: given ∀ v, post (...) postBody (...), show R
      intro hpost_all
      -- Decompose continuation: body >>= decl >>= assume >>= prove >>= ret
      have hcont_body := VerifM.eval_bind _ _ _ _ hcont
      -- Strengthen with decls_grow to track subset/agree through body
      have hcont_grow := VerifM.eval.decls_grow ρ₁ hcont_body
      -- Weaken body postcondition to what we need
      apply hR st₁ ρ₁ hdsub_st hagree_st
      exact hcont_grow.mono fun result st_b ρ_b ⟨hdsub_b, hagree_b, hrest⟩ => by
        -- Given the rest of the continuation succeeds, show result.wfIn → Φ (result.eval)
        intro hwf_result
        -- Decompose: decl, assume eq, prove
        have hb2 := VerifM.eval_bind _ _ _ _ hrest
        have hdecl := VerifM.eval_decl hb2
        set resVar := st_b.freshVar (some postName) .value
        have hfresh_decls_b : resVar.name ∉ st_b.decls.map Var.name :=
          fresh_not_mem (addNumbers postName) (st_b.decls.map Var.name) (addNumbers_injective _)
        have hfresh_range_b : ⟨resVar.name, Srt.value⟩ ∉ σ₁.range := by
          intro hmem
          exact hfresh_decls_b (List.mem_map.mpr ⟨⟨resVar.name, .value⟩,
            (hdsub_b (hσ₁wf.2 hmem)), rfl⟩)
        specialize hdecl (result.eval ρ_b)
        have hb3 := VerifM.eval_bind _ _ _ _ hdecl
        -- The eq formula
        have heq_wf : (Formula.eq Srt.value (Term.var .value resVar.name) result).wfIn
            (resVar :: st_b.decls) := by
          intro w hw
          simp only [Formula.freeVars, Term.freeVars] at hw
          cases hw with
          | head => exact .head _
          | tail _ hw => exact .tail _ (hwf_result w hw)
        have heq_holds : (Formula.eq Srt.value (Term.var .value resVar.name) result).eval
            (ρ_b.update .value resVar.name (result.eval ρ_b)) := by
          simp only [Formula.eval, Term.eval, Env.lookup_update_same]
          exact Term.eval_env_agree hwf_result (agreeOn_update_fresh hfresh_decls_b)
        have hassume := VerifM.eval_assume hb3 heq_wf heq_holds
        -- Prove σ₂ postBody
        set σ₂ := σ₁.rename ⟨postName, .value⟩ resVar.name
        have hσ₂wf : σ₂.wf (resVar :: st_b.decls) :=
          FiniteSubst.rename_wf ⟨hσ₁wf.1, hσ₁wf.2.trans hdsub_b⟩ hfresh_range_b
        have hb4 := VerifM.eval_bind _ _ _ _ hassume
        -- From prove_correct: get Assertion.pre on postBody
        have hpre := Assertion.prove_correct postBody σ₂ (fun _ _ => True)
          { st_b with decls := resVar :: st_b.decls,
                      asserts := Formula.eq Srt.value (Term.var .value resVar.name) result :: st_b.asserts }
          (ρ_b.update .value resVar.name (result.eval ρ_b)) _ (fun () _ => True)
          (fun _ _ _ _ _ _ h => h)
          hσ₂wf hwf_postBody hb4 (fun _ () _ _ _ _ _ => trivial)
        -- Transport pre to (σ₁.subst.eval ρ₁).update .value postName (result.eval ρ_b)
        have hag_rename := @FiniteSubst.rename_agreeOn σ₁ ⟨postName, .value⟩ resVar.name
          ρ_b (result.eval ρ_b) hσ₁wf.1 hfresh_range_b
        -- Need to go from σ₁.subst.eval ρ_b to σ₁.subst.eval ρ₁
        have hag_eval := FiniteSubst.eval_agreeOn hσ₁wf.1
          (Env.agreeOn_mono hσ₁wf.2 (Env.agreeOn_symm hagree_b))
        have hag_combined : Env.agreeOn (⟨postName, .value⟩ :: σ₁.dom)
            (σ₂.subst.eval (ρ_b.update .value resVar.name (result.eval ρ_b)))
            ((σ₁.subst.eval ρ₁).update .value postName (result.eval ρ_b)) :=
          Env.agreeOn_trans hag_rename (Env.agreeOn_update hag_eval)
        have hpre' := Assertion.pre_env_agree hwf_postBody hag_combined
          (fun _ _ _ _ _ _ h => h) hpre
        -- Combine with hpost_all via pre_post_combine
        exact Assertion.pre_post_combine hpre' (hpost_all (result.eval ρ_b))
          (fun () _ _ hΦ => hΦ))
  -- Now use pre_post_combine on happly (pre) and hpost (post) to get R
  exact Assertion.pre_post_combine happly hpost
    (fun ⟨postName, postBody⟩ _ hpre_all hΦ_post => hΦ_post hpre_all)
