import Mica.TinyML.Typed
import Mica.TinyML.Typing
import Mica.TinyML.OpSem
import Mica.Verifier.Monad
import Mica.Verifier.Assertions
import Mica.Verifier.PredicateTransformers
import Mica.Verifier.Specifications
import Mica.Verifier.Utils
import Mica.Verifier.Expressions
import Mica.Engine.Driver
import Mica.Base.Fresh
import Mathlib.Data.Finmap

open Typed


def checkSpec (Θ : TinyML.TypeEnv) (S : SpecMap) (e : Expr) (s : Spec) : VerifM Unit := do
  let (fb, argNames, body) ← match e with
    | .fix fb argBinders _ body => do
      match extractArgNames argBinders s.args with
      | .ok names => pure (fb, names, body)
      | .error msg => VerifM.fatal msg
    | _ => VerifM.fatal "checkSpec: expected function"
  let S' := SpecMap.eraseAll argNames (S.insert' fb s)
  Spec.implement s fun argVars => do
    let B : Bindings := Bindings.empty ++ (argNames.zip argVars).reverse
    let Γ := (argNames.zip (s.args.map Prod.snd)).foldl (fun ctx (name, ty) => ctx.extend name ty) TinyML.TyCtx.empty
    let se ← compile Θ S' B Γ body
    if TinyML.Typ.sub Θ body.ty s.retTy then pure ()
    else VerifM.fatal s!"checkSpec: return type mismatch"
    pure se

theorem checkSpec_body_correct (Θ : TinyML.TypeEnv) (S : SpecMap) (s : Spec)
    (γ : Runtime.Subst)
    (hswf : s.wfIn Signature.empty) (hSwf : S.wfIn Signature.empty)
    (hS : S.satisfiedBy Θ γ)
    (st : TransState) (ρ : Env)
    (fb : Binder) (argBinders : List Binder) (body : Expr)
    (argNames : List String)
    (hext : extractArgNames argBinders s.args = Except.ok argNames)
    (bs : List Runtime.Binder) (hbs_def : bs = argBinders.map (·.runtime))
    (fval : Runtime.Val)
    (hbody : (Spec.implement s fun argVars => do
        let S' := SpecMap.eraseAll argNames (S.insert' fb s)
        let B : Bindings := Bindings.empty ++ (argNames.zip argVars).reverse
        let Γ := (argNames.zip (s.args.map Prod.snd)).foldl
          (fun ctx (x : String × TinyML.Typ) => ctx.extend x.1 x.2) TinyML.TyCtx.empty
        let se ← compile Θ S' B Γ body
        if TinyML.Typ.sub Θ body.ty s.retTy then pure ()
        else VerifM.fatal s!"checkSpec: return type mismatch"
        pure se).eval st ρ (fun _ _ _ => True))
    (vs : List Runtime.Val) (P : Runtime.Val → iProp)
    (htyped_args : TinyML.ValsHaveTypes Θ vs (s.args.map Prod.snd))
    (isPrecond_rec : s.isPrecondFor Θ fval) :
    st.owns.interp ρ ∗
      PredTrans.apply (fun r => ⌜TinyML.ValHasType Θ r s.retTy⌝ -∗ P r) s.pred
        (Spec.argsEnv Env.empty s.args vs) ⊢
      wp (body.runtime.subst (γ.update' fb.runtime fval |>.updateAll' bs vs)) P := by
  obtain ⟨hlen1, hlen2, hbs_eq⟩ := extractArgNames_spec hext
  have hbs_runtime : bs = argNames.map Runtime.Binder.named := by rw [hbs_def]; exact hbs_eq
  have hlen_nv : argNames.length = vs.length := by
    have := htyped_args.length_eq; simp at this; omega
  have hlen : bs.length = vs.length := by simp [hbs_runtime]; omega
  set γ_body := γ.update' fb.runtime fval |>.updateAll' bs vs
  set S' : SpecMap := SpecMap.eraseAll argNames (S.insert' fb s)
  -- Use implement_correct
  apply Spec.implement_correct Θ s _ st ρ vs P
    (wp (body.runtime.subst γ_body) P)
    hswf htyped_args hbody
  intro argVars st' ρ' Q hargVars_mem hargVars_sort hargVars_lookup hbody_eval
  -- Establish spec map satisfaction
  have hS'wf : S'.wfIn Signature.empty :=
    SpecMap.wfIn_eraseAll (SpecMap.wfIn_insert' hSwf hswf)
  have hS'_sat : S'.satisfiedBy Θ γ_body := by
    have hS_ext : (S.insert' fb s).satisfiedBy Θ (γ.update' fb.runtime fval) :=
      SpecMap.satisfiedBy_insert'_update' hS isPrecond_rec
    have hsat := SpecMap.satisfiedBy_eraseAll_updateAll' hS_ext hlen_nv
    change (SpecMap.eraseAll argNames (S.insert' fb s)).satisfiedBy Θ
      ((γ.update' fb.runtime fval).updateAll' bs vs)
    rw [hbs_runtime]; exact hsat
  -- Set up bindings, agreement, well-formedness, typed substitution
  set Γ := (argNames.zip (s.args.map Prod.snd)).foldl
    (fun ctx (x : String × TinyML.Typ) => ctx.extend x.1 x.2) TinyML.TyCtx.empty
  set B : Bindings := Bindings.empty ++ (argNames.zip argVars).reverse
  have hlen_avs : argNames.length = argVars.length := by
    have := hargVars_lookup.length_eq
    have := htyped_args.length_eq; simp at this; omega
  have hagree : Bindings.agreeOnLinked B ρ' γ_body := by
    show Bindings.agreeOnLinked (Bindings.empty ++ (argNames.zip argVars).reverse) ρ'
      ((γ.update' fb.runtime fval).updateAll' bs vs)
    rw [show Bindings.empty ++ (argNames.zip argVars).reverse =
        (argNames.zip argVars).reverse ++ Bindings.empty from by simp [Bindings.empty]]
    rw [hbs_runtime]
    apply Bindings.agreeOnLinked_updateAll' Bindings.empty argNames argVars vs
      (γ.update' fb.runtime fval) ρ'
    · intro x x' h; simp [Bindings.empty] at h
    · exact hlen_avs
    · exact hlen_nv
    · exact hargVars_sort
    · exact hargVars_lookup
  have hbwf : Bindings.wf B st'.decls := by
    intro ⟨n, v⟩ hp
    apply hargVars_mem v
    have hmem : (n, v) ∈ (argNames.zip argVars) := by simp [B, Bindings.empty] at hp; exact hp
    exact List.of_mem_zip hmem |>.2
  have hts : Bindings.typedSubst Θ B Γ γ_body := by
    apply Bindings.typedSubst_of_agreeOnLinked hagree
    intro x x' t hmem hΓ
    show TinyML.ValHasType Θ (ρ'.consts .value x'.name) t
    set args' := argNames.zip (s.args.map Prod.snd)
    have hfst : args'.map Prod.fst = argNames := by
      simp [args']; exact List.map_fst_zip (by simp; omega)
    have hsnd : args'.map Prod.snd = s.args.map Prod.snd := by
      simp [args']; exact List.map_snd_zip (by simp; omega)
    exact val_typed_of_last_wins args' argVars vs ρ' TinyML.TyCtx.empty x x' t
      (by rw [hfst]; exact hlen_avs)
      (by rw [hfst]; exact hlen_nv)
      (by rw [hfst]; simp [B, Bindings.empty] at hmem; exact hmem)
      hΓ hargVars_lookup
      (by rw [hsnd]; exact htyped_args)
  -- Use compile_correct
  have hcompile := VerifM.eval_bind _ _ _ _ hbody_eval
  exact compile_correct Θ Q body S' B Γ st' ρ' γ_body _ _
    (VerifM.eval.decls_grow ρ' hcompile) hagree hbwf hts hS'_sat hS'wf
    (fun v ρ'' st'' se hΨ hse_wf heval_se htyped => by
      obtain ⟨hdecls, hagreeOn, hΨ⟩ := hΨ
      by_cases hsub : TinyML.Typ.sub Θ body.ty s.retTy
      · simp [hsub] at hΨ
        have hΨ' := VerifM.eval_ret hΨ
        dsimp only at hΨ'
        subst heval_se
        have hret : TinyML.ValHasType Θ (se.eval ρ'') s.retTy :=
          TinyML.ValHasType_sub htyped (TinyML.Typ.sub_sound hsub)
        refine (show st''.owns.interp ρ'' ∗ Q ⊢
            st''.owns.interp ρ'' ∗ Q ∗
              ((⌜TinyML.ValHasType Θ (se.eval ρ'') s.retTy⌝ -∗ P (se.eval ρ'')) -∗
                P (se.eval ρ'')) from ?_).trans (hΨ' _ hse_wf)
        istart
        iintro ⟨Howns, HQ⟩
        isplitl [Howns]
        · iexact Howns
        · isplitl [HQ]
          · iexact HQ
          · iintro Hwand
            iapply Hwand
            ipure_intro
            exact hret
      · simp [hsub] at hΨ
        exact (VerifM.eval_fatal hΨ).elim)

/-- Sorry'd helper: extract `isPrecondFor` (a `Prop`) from an iProp wand.

The hypothesis is a universally quantified wand asserting that the spec's predicate
transformer entails `wp` of calling `f`. The conclusion `isPrecondFor` says the same
at the `Prop` level. The only gap is the wand-to-entailment and `⌜ValsHaveTypes⌝`-to-Prop
conversions.

Once `isPrecondFor` is migrated to a persistent separation logic assertion, this becomes
a direct consequence of the hypothesis. -/
theorem isPrecondFor_of_wp_rec (Θ : TinyML.TypeEnv) (s : Spec)
    (f : Runtime.Val) :
    (∀ (vs : List Runtime.Val) (P : Runtime.Val → iProp),
      ⌜TinyML.ValsHaveTypes Θ vs (s.args.map Prod.snd)⌝ ∗
        PredTrans.apply (fun r => ⌜TinyML.ValHasType Θ r s.retTy⌝ -∗ P r) s.pred
          (Spec.argsEnv Env.empty s.args vs) -∗
        wp (Runtime.Expr.app (.val f) (vs.map Runtime.Expr.val)) P) ⊢
    ⌜s.isPrecondFor Θ f⌝ := by
  sorry

theorem checkSpec_correct (Θ : TinyML.TypeEnv) (S : SpecMap) (e : Expr) (s : Spec)
    (γ : Runtime.Subst)
    (hswf : s.wfIn Signature.empty) (hSwf : S.wfIn Signature.empty)
    (hS : S.satisfiedBy Θ γ)
    (st : TransState) (ρ : Env) :
    VerifM.eval (checkSpec Θ S e s) st ρ (fun _ _ _ => True) →
    st.owns.interp ρ ⊢ wp (e.runtime.subst γ) (fun v => ⌜s.isPrecondFor Θ v⌝) := by
  intro heval
  cases e
  case fix fb argBinders retTy body =>
    simp only [checkSpec] at heval
    -- Case split on extractArgNames result
    cases hext : extractArgNames argBinders s.args with
    | error msg =>
      simp [hext] at heval
      exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ heval)).elim
    | ok argNames =>
      simp [hext] at heval
      have hbody := VerifM.eval_ret (VerifM.eval_bind _ _ _ _ heval)
      dsimp only at hbody
      set bs := argBinders.map (·.runtime)
      set γ' := (γ.remove' fb.runtime).removeAll' bs with hγ'_def
      set S' : SpecMap := SpecMap.eraseAll argNames (S.insert' fb s)
      have hgoal : (Expr.fix fb argBinders retTy body).runtime.subst γ =
          Runtime.Expr.fix fb.runtime (argBinders.map (·.runtime))
            (body.runtime.subst γ') := by
        conv_lhs => unfold Expr.runtime
        simp only [Runtime.Expr.subst_fix, hγ'_def, bs]
      rw [hgoal]
      set fval := Runtime.Val.fix fb.runtime (argBinders.map (·.runtime))
        (body.runtime.subst γ') with hfval_def
      -- Use the extracted body correctness lemma
      have body_correct := fun vs P htyped_args isPrecond_rec =>
        checkSpec_body_correct Θ S s γ hswf hSwf hS st ρ fb argBinders body argNames
          hext bs rfl fval hbody vs P htyped_args isPrecond_rec
      -- Step 1: Apply wp.func to reduce wp (Expr.fix ...) to the value case
      -- Goal: owns ⊢ wp (Expr.fix fb bs body') (fun v => ⌜isPrecondFor Θ v s⌝)
      -- wp.func: P fval ⊢ wp (Expr.fix fb bs body') P, where fval = Val.fix fb bs body'
      change st.owns.interp ρ ⊢ wp (Runtime.Expr.fix fb.runtime bs (body.runtime.subst γ'))
        (fun v => ⌜s.isPrecondFor Θ v⌝)
      -- Set up Φ for wp_fix': Φ P vs = ⌜ValsHaveTypes⌝ ∗ PredTrans.apply (... -∗ P) s.pred ...
      set Φ : (Runtime.Val → iProp) → List Runtime.Val → iProp :=
        fun P vs => ⌜TinyML.ValsHaveTypes Θ vs (s.args.map Prod.snd)⌝ ∗
          PredTrans.apply (fun r => ⌜TinyML.ValHasType Θ r s.retTy⌝ -∗ P r) s.pred
            (Spec.argsEnv Env.empty s.args vs)
      -- Apply wp_fix' to get the recursive spec, then isPrecondFor_of_wp_rec to extract Prop
      suffices hwp : st.owns.interp ρ ⊢
          ∀ (vs : List Runtime.Val) (P : Runtime.Val → iProp),
            Φ P vs -∗ wp (Runtime.Expr.app (.val fval) (vs.map Runtime.Expr.val)) P by
        -- Extract the Prop-level recursive spec, then lift it through `wp_func`.
        have hgoal2 := hwp.trans (isPrecondFor_of_wp_rec Θ s fval)
        exact SpatialContext.wp_func hgoal2
      -- Prove the wp_fix' obligation
      obtain ⟨_, _, hbs_eq⟩ := extractArgNames_spec hext
      have hbs_runtime : bs = argNames.map Runtime.Binder.named := hbs_eq
      apply SpatialContext.wp_fix'
      istart
      iintro Howns IH %vs %P ⟨%htyped, Hpred⟩
      -- Extract the Prop-level recursive spec from the recursive wp hypothesis.
      ihave ⌜hipc⌝ := isPrecondFor_of_wp_rec Θ s fval $$ IH
      -- Use body_correct: needs owns ∗ PredTrans ⊢ wp (body.subst (γ.update'...))
      -- wp_fix' gives body.subst (id.update'...) — bridge via subst_fix_comp
      have hlen_vs : bs.length = vs.length := by
        simp [hbs_runtime]; have := htyped.length_eq; simp at this; omega
      have hsub := Runtime.Expr.subst_fix_comp body.runtime fb.runtime bs γ fval vs hlen_vs
      simp only [] at hsub; rw [hsub]
      iapply (body_correct vs _ htyped hipc)
      isplitl [Howns]
      · iexact Howns
      · iexact Hpred
  all_goals
    simp only [checkSpec] at heval
    exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ heval)).elim
