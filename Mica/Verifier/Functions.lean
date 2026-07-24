-- SUMMARY: Verification of function bodies against specifications, including the soundness of specification checking.
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
import Mica.Verifier.Intrinsic

open Iris Iris.BI

variable [MicaGS HasLC.hasLC Sig]
open Typed


/-- Compile the body of a specification under its argument context and
    check that the inferred return type is a subtype of the declared one. -/
def checkBody (reg : Verifier.Registry) (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (S : SpecMap) (s : Spec)
    (argNames : List String) (body : Expr)
    (argVars : List FOL.Const) : VerifM (Term .value) := do
  let B : Bindings := Bindings.empty ++ (argNames.zip argVars).reverse
  let Γ := (argNames.zip (s.args.map Prod.snd)).foldl
    (fun ctx (name, ty) => ctx.extend name ty) TinyML.TyCtx.empty
  let se ← compile reg Θ Δ_spec S B Γ body
  if TinyML.Typ.sub Θ body.ty s.retTy then pure ()
  else VerifM.fatal s!"checkSpec: return type mismatch"
  pure se

def checkSpec (reg : Verifier.Registry) (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (S : SpecMap) (e : Expr) (s : Spec) : VerifM Unit := do
  let (fb, argNames, body) ← match e with
    | .fix fb argBinders _ body => do
      match extractArgNames argBinders s.args with
      | .ok names => pure (fb, names, body)
      | .error msg => VerifM.fatal msg
    | _ => VerifM.fatal "checkSpec: expected function"
  let S' := SpecMap.eraseAll argNames (S.insertBinder fb s)
  VerifM.persist
  Spec.implement Δ_spec s (checkBody reg Θ Δ_spec S' s argNames body)

/-- Soundness of `checkBody`: given argument variables supplied by
    `Spec.implement_correct` and a successful `checkBody` evaluation, the
    compiled body's `wp` holds. -/
theorem checkBody_correct (reg : Verifier.Registry) (hSound : Verifier.Registry.Sound reg)
    (W : TinyML.World) (hW : W.pctx = reg.primCtx) (S : SpecMap) (s : Spec)
    (γ : Runtime.Subst)
    (hswf : s.wfIn W.Δ_spec) (hSwf : S.wfIn W.Δ_spec)
    (hwf : W.wf)
    (fb : Binder) (argBinders : List Binder) (body : Expr)
    (argNames : List String)
    (hext : extractArgNames argBinders s.args = Except.ok argNames)
    (bs : List Runtime.Binder) (hbs_def : bs = argBinders.map (·.runtime))
    (fval : Runtime.Val)
    (vs : List Runtime.Val)
    (P : Runtime.Val → iProp)
    {argVars : List FOL.Const} {st' : TransState} {ρ' : VerifM.Env} {Q : iProp}
    (hag : W.agrees st'.decls ρ'.env)
    (hΔreg : Verifier.Registry.symSubset reg W.Δ_spec)
    (hρreg : Verifier.Registry.symAgree reg W.ρ_spec)
    (hargVars_mem : ∀ v ∈ argVars, v ∈ st'.decls.consts)
    (hargVars_sort : ∀ v ∈ argVars, v.sort = .value)
    (hargVars_lookup : List.Forall₂ (fun av val => ρ'.env.consts .value av.name = val) argVars vs)
    (hbody_eval : VerifM.eval
        (checkBody reg W.Θ W.Δ_spec (SpecMap.eraseAll argNames (S.insertBinder fb s)) s argNames body argVars)
        st' ρ'
        (fun result st'' ρ'' => ∀ S, result.wfIn st''.decls →
          st''.sl W ρ'' ∗ Q ∗
            ((TinyML.ValHasType W (result.eval ρ''.env) s.retTy -∗ P (result.eval ρ''.env)) -∗ S) ⊢ S)) :
    st'.sl W ρ' ∗ TinyML.ValsHaveTypes W vs (s.args.map Prod.snd) ∗ Q ⊢
      (S.satisfiedBy W γ ∗ s.isPrecondFor W fval) -∗
        wp W.pctx (body.runtime.subst (γ.updateBinder fb.runtime fval |>.updateAllBinder bs vs)) P := by
  simp only [checkBody] at hbody_eval
  obtain ⟨hargNames_len, _, hbs_eq⟩ := extractArgNames_spec hext
  have hbs_runtime : bs = argNames.map Runtime.Binder.named := hbs_def ▸ hbs_eq
  set γ_body := γ.updateBinder fb.runtime fval |>.updateAllBinder bs vs
  set S' : SpecMap := SpecMap.eraseAll argNames (S.insertBinder fb s)
  have hS'wf : S'.wfIn W.Δ_spec :=
    SpecMap.wfIn_eraseAll (SpecMap.wfIn_insertBinder hSwf hswf)
  set Γ := (argNames.zip (s.args.map Prod.snd)).foldl
    (fun ctx (x : String × TinyML.Typ) => ctx.extend x.1 x.2) TinyML.TyCtx.empty
  set B : Bindings := Bindings.empty ++ (argNames.zip argVars).reverse
  have hbwf : Bindings.wfIn B st'.decls := by
    intro ⟨n, v⟩ hp
    apply hargVars_mem v
    have hmem : (n, v) ∈ (argNames.zip argVars) := by simp [B, Bindings.empty] at hp; exact hp
    exact List.of_mem_zip hmem |>.2
  -- Use compile_correct
  have hcompile := VerifM.eval_bind hbody_eval
  iintro ⟨Howns, #Hvals, HQ⟩
  ihave %hlen_vals := TinyML.ValsHaveTypes.length_eq $$ Hvals
  have hlen_nv : argNames.length = vs.length := by
    simp [List.length_map] at hlen_vals
    omega
  have hlen_avs : argNames.length = argVars.length := by
    have := hargVars_lookup.length_eq
    omega
  have hagree : Bindings.agreeOnLinked B ρ'.env γ_body := by
    show Bindings.agreeOnLinked (Bindings.empty ++ (argNames.zip argVars).reverse) ρ'.env
      ((γ.updateBinder fb.runtime fval).updateAllBinder bs vs)
    rw [show Bindings.empty ++ (argNames.zip argVars).reverse =
        (argNames.zip argVars).reverse ++ Bindings.empty from by simp [Bindings.empty]]
    rw [hbs_runtime]
    apply Bindings.agreeOnLinked_updateAllBinder Bindings.empty argNames argVars vs
      (γ.updateBinder fb.runtime fval) ρ'.env
    · intro x x' h; simp [Bindings.empty] at h
    · exact hlen_avs
    · exact hlen_nv
    · exact hargVars_sort
    · exact hargVars_lookup
  have hts :
      TinyML.ValsHaveTypes W vs (s.args.map Prod.snd) ⊢
        Bindings.typedSubst W B Γ γ_body := by
    iintro #HvalsArg
    iapply (Bindings.typedSubst_of_agreeOnLinked (W := W) hagree)
    imodintro
    iintro %x %x' %t %hmem %hΓ
    set args' := argNames.zip (s.args.map Prod.snd)
    have hfst : args'.map Prod.fst = argNames := by
      simp [args']; exact List.map_fst_zip (by simp; omega)
    have hsnd : args'.map Prod.snd = s.args.map Prod.snd := by
      simp [args']; exact List.map_snd_zip (by simp; omega)
    iapply (valHasType_lookup_zip_reverse args' argVars vs ρ'.env TinyML.TyCtx.empty x x' t
      (by rw [hfst]; exact hlen_avs)
      (by rw [hfst]; exact hlen_nv)
      (by rw [hfst]; simp [B, Bindings.empty] at hmem; exact hmem)
      hΓ hargVars_lookup)
    rw [hsnd]
    iassumption
  have hS'_sat :
      S.satisfiedBy W γ ∗ s.isPrecondFor W fval ⊢
        S'.satisfiedBy W γ_body := by
    have hinsert :
        S.satisfiedBy W γ ∗ s.isPrecondFor W fval ⊢
          (S.insertBinder fb s).satisfiedBy W (γ.updateBinder fb.runtime fval) :=
      SpecMap.satisfiedBy_insertBinder_updateBinder
    have herase :
        (S.insertBinder fb s).satisfiedBy W (γ.updateBinder fb.runtime fval) ⊢
          S'.satisfiedBy W ((γ.updateBinder fb.runtime fval).updateAllBinder (argNames.map Runtime.Binder.named) vs) :=
      SpecMap.satisfiedBy_eraseAll_updateAllBinder hlen_nv
    exact hinsert.trans <| by simpa [S', γ_body, hbs_runtime] using herase
  have hbody_wp :
      st'.sl W ρ' ∗ (S'.satisfiedBy W γ_body ∗ Bindings.typedSubst W B Γ γ_body ∗ Q) ⊢
        wp W.pctx (body.runtime.subst γ_body) P := by
    refine compile_correct reg hSound body W Q S' B Γ st' ρ' γ_body _ _ hW
      (VerifM.eval.decls_grow ρ' hcompile) hagree hbwf hS'wf hwf
      hag hΔreg hρreg ?_
    intro v ρ'' st'' se hΨ hse_wf heval_se
    obtain ⟨_, _, hΨ⟩ := hΨ
    by_cases hsub : TinyML.Typ.sub W.Θ body.ty s.retTy
    case neg =>
      simp [hsub] at hΨ
      exact (VerifM.eval_fatal hΨ).elim
    simp [hsub] at hΨ
    have hΨ' := VerifM.eval_ret hΨ
    dsimp only at hΨ'
    rw [← heval_se]
    refine (show st''.sl W ρ'' ∗ TinyML.ValHasType W (se.eval ρ''.env) body.ty ∗ Q ⊢
        st''.sl W ρ'' ∗ Q ∗
          ((TinyML.ValHasType W (se.eval ρ''.env) s.retTy -∗ P (se.eval ρ''.env)) -∗
            P (se.eval ρ''.env)) from ?_).trans (hΨ' _ hse_wf)
    iintro ⟨Howns, Hty, HQ⟩
    iframe Howns HQ
    iintro Hwand
    iapply Hwand
    iapply (TinyML.ValHasType.sub (TinyML.Typ.sub_sound hsub))
    iexact Hty
  iintro HSat
  iapply hbody_wp
  iframe Howns HQ
  isplitl [HSat]
  · iapply hS'_sat
    iexact HSat
  · iapply hts
    iexact Hvals

theorem checkSpec_correct (reg : Verifier.Registry) (hSound : Verifier.Registry.Sound reg)
    (W : TinyML.World) (hW : W.pctx = reg.primCtx) (S : SpecMap) (e : Expr) (s : Spec)
    (γ : Runtime.Subst)
    (hswf : s.wfIn W.Δ_spec) (hSwf : S.wfIn W.Δ_spec)
    (hwf : W.wf)
    (st : TransState) (ρ : VerifM.Env)
    (hag : W.agrees st.decls ρ.env)
    (hΔreg : Verifier.Registry.symSubset reg W.Δ_spec)
    (hρreg : Verifier.Registry.symAgree reg W.ρ_spec) :
    VerifM.eval (checkSpec reg W.Θ W.Δ_spec S e s) st ρ (fun _ _ _ => True) →
    st.sl W ρ ∗ S.satisfiedBy W γ ⊢ wp W.pctx (e.runtime.subst γ) (fun v => s.isPrecondFor W v) := by
  intro heval
  -- All non-`fix` shapes (and bad `extractArgNames`) discharge the same way.
  have elim_bind_fatal : ∀ {α β} {msg} {k : α → VerifM β} {st ρ Ψ},
      VerifM.eval (VerifM.fatal msg >>= k) st ρ Ψ → False :=
    fun h => VerifM.eval_fatal (VerifM.eval_bind h)
  cases e
  case fix fb argBinders retTy body =>
    simp only [checkSpec] at heval
    -- Case split on extractArgNames result
    cases hext : extractArgNames argBinders s.args with
    | error msg =>
      simp [hext] at heval
      exact (elim_bind_fatal heval).elim
    | ok argNames =>
      simp [hext] at heval
      have hcont := VerifM.eval_ret (VerifM.eval_bind heval)
      have hpersist := VerifM.eval_persist (VerifM.eval_bind hcont)
      have himpl := hpersist
      dsimp only at himpl
      set bs := argBinders.map (·.runtime)
      set γ' := (γ.remove' fb.runtime).removeAll' bs with hγ'_def
      set S' : SpecMap := SpecMap.eraseAll argNames (S.insertBinder fb s)
      have hgoal : (Expr.fix fb argBinders retTy body).runtime.subst γ =
          Runtime.Expr.fix fb.runtime (argBinders.map (·.runtime))
            (body.runtime.subst γ') := by
        conv_lhs => unfold Expr.runtime
        simp only [Runtime.Expr.subst_fix, hγ'_def, bs]
      rw [hgoal]
      set fval := Runtime.Val.fix fb.runtime (argBinders.map (·.runtime))
        (body.runtime.subst γ') with hfval_def
      obtain ⟨_, hargs_len, hbs_eq⟩ := extractArgNames_spec hext
      have hbs_runtime : bs = argNames.map Runtime.Binder.named := hbs_eq
      apply SpatialContext.wp_func
      apply Spec.isPrecondFor_fix (by simpa using hargs_len)
      istart
      iintro H
      icases H with ⟨Hsl, #Hspec⟩
      imodintro
      iintro Hrec %ρ_call %vs %P %hagree_call #Htyped Hpred
      -- `isPrecondFor_fix` hands us the body's subst as `id.updateBinder ... |>.updateAllBinder ...`;
      -- fuse it with γ via `subst_fix_comp` so it matches `body_correct`.
      ihave %hlen_typed := TinyML.ValsHaveTypes.length_eq $$ Htyped
      have hlen_vs : bs.length = vs.length := by
        simp [hbs_runtime, List.length_map] at hlen_typed ⊢
        omega
      have hsub := Runtime.Expr.subst_fix_comp body.runtime fb.runtime bs γ fval vs hlen_vs
      simp only [] at hsub; rw [hsub]
      have hbody' : TinyML.ValsHaveTypes W vs (s.args.map Prod.snd) ∗
          PredTrans.apply W (fun r => TinyML.ValHasType W r s.retTy -∗ P r) s.pred
          (Spec.argsEnv ρ_call s.args vs) ⊢
          SpecMap.satisfiedBy W S γ ∗ s.isPrecondFor W fval -∗
            wp W.pctx (Runtime.Expr.subst ((Runtime.Subst.updateBinder fb.runtime fval γ).updateAllBinder bs vs) body.runtime) P := by
        iintro H
        icases H with ⟨Htyped', Hpred'⟩
        iintuitionistic Htyped'
        have hag_persist : W.agrees (TransState.persist st).decls ρ.env := by
          simpa using hag
        ihave Hwand := Spec.implement_correct W s _ (TransState.persist st) ρ vs P
          (TinyML.ValsHaveTypes W vs (s.args.map Prod.snd) -∗
            (S.satisfiedBy W γ ∗ s.isPrecondFor W fval) -∗
              wp W.pctx (body.runtime.subst (γ.updateBinder fb.runtime fval |>.updateAllBinder bs vs)) P)
          hswf hwf hag_persist himpl
          (fun argVars st' ρ' Q hst_sub hρ_agree hargVars_mem hargVars_sort hargVars_lookup hbody_eval => by
            have hag' : W.agrees st'.decls ρ'.env := hag_persist.step hst_sub hρ_agree
            iintro ⟨Hsl, HQ⟩ Htyped''
            iapply (checkBody_correct reg hSound W hW S s γ hswf hSwf hwf fb argBinders body argNames
              hext bs rfl fval vs P hag' hΔreg hρreg hargVars_mem hargVars_sort hargVars_lookup hbody_eval)
            isplitl [Hsl]
            · iexact Hsl
            · isplitl [Htyped'']
              · iexact Htyped''
              · iexact HQ) $$ [Htyped' Hpred']
        · isplitl []
          · simp
            iempintro
          · isplitl [Htyped']
            · iexact Htyped'
            · have hlen_vals_call : s.args.length ≤ vs.length := by
                have hlen := hlen_typed
                simp [List.length_map] at hlen
                omega
              iapply (PredTrans.apply_env_agree W (ρ := Spec.argsEnv ρ_call s.args vs)
                (ρ' := Spec.argsEnv ⟨W.ρ_spec⟩ s.args vs) hswf
                (Spec.argsEnv_agreeOn (Δ := W.Δ_spec) (ρ₁ := ρ_call) (ρ₂ := ⟨W.ρ_spec⟩)
                  (VerifM.Env.agreeOn_symm hagree_call) s.args vs hlen_vals_call))
              iexact Hpred'
        iapply Hwand
        iexact Htyped'
      iapply hbody' $$ [Htyped Hpred] [Hspec Hrec]
      · isplitl [Htyped]
        · iexact Htyped
        · iexact Hpred
      · isplitl [Hspec]
        · iexact Hspec
        · iexact Hrec
  all_goals
    simp only [checkSpec] at heval
    exact (elim_bind_fatal heval).elim
