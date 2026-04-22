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

open Iris Iris.BI
open Typed


/-- Compile the body of a specification under its argument context and
    check that the inferred return type is a subtype of the declared one. -/
def checkBody (Θ : TinyML.TypeEnv) (S : SpecMap) (s : Spec)
    (argNames : List String) (body : Expr)
    (argVars : List FOL.Const) : VerifM (Term .value) := do
  let B : Bindings := Bindings.empty ++ (argNames.zip argVars).reverse
  let Γ := (argNames.zip (s.args.map Prod.snd)).foldl
    (fun ctx (name, ty) => ctx.extend name ty) TinyML.TyCtx.empty
  let se ← compile Θ S B Γ body
  if TinyML.Typ.sub Θ body.ty s.retTy then pure ()
  else VerifM.fatal s!"checkSpec: return type mismatch"
  pure se

def checkSpec (Θ : TinyML.TypeEnv) (S : SpecMap) (e : Expr) (s : Spec) : VerifM Unit := do
  let (fb, argNames, body) ← match e with
    | .fix fb argBinders _ body => do
      match extractArgNames argBinders s.args with
      | .ok names => pure (fb, names, body)
      | .error msg => VerifM.fatal msg
    | _ => VerifM.fatal "checkSpec: expected function"
  let S' := SpecMap.eraseAll argNames (S.insert' fb s)
  Spec.implement s (checkBody Θ S' s argNames body)

/-- Soundness of `checkBody`: given argument variables supplied by
    `Spec.implement_correct` and a successful `checkBody` evaluation, the
    compiled body's `wp` holds. -/
theorem checkBody_correct (Θ : TinyML.TypeEnv) (S : SpecMap) (s : Spec)
    (γ : Runtime.Subst)
    (hswf : s.wfIn Signature.empty) (hSwf : S.wfIn Signature.empty)
    (fb : Binder) (argBinders : List Binder) (body : Expr)
    (argNames : List String)
    (hext : extractArgNames argBinders s.args = Except.ok argNames)
    (bs : List Runtime.Binder) (hbs_def : bs = argBinders.map (·.runtime))
    (fval : Runtime.Val)
    (vs : List Runtime.Val)
    (P : Runtime.Val → iProp)
    {argVars : List FOL.Const} {st' : TransState} {ρ' : VerifM.Env} {Q : iProp}
    (hargVars_mem : ∀ v ∈ argVars, v ∈ st'.decls.consts)
    (hargVars_sort : ∀ v ∈ argVars, v.sort = .value)
    (hargVars_lookup : List.Forall₂ (fun av val => ρ'.env.consts .value av.name = val) argVars vs)
    (hbody_eval : VerifM.eval
        (checkBody Θ (SpecMap.eraseAll argNames (S.insert' fb s)) s argNames body argVars)
        st' ρ'
        (fun result st'' ρ'' => ∀ S, result.wfIn st''.decls →
          st''.sl ρ'' ∗ Q ∗
            ((TinyML.ValHasType Θ (result.eval ρ''.env) s.retTy -∗ P (result.eval ρ''.env)) -∗ S) ⊢ S)) :
    st'.sl ρ' ∗ TinyML.ValsHaveTypes Θ vs (s.args.map Prod.snd) ∗ Q ⊢
      (S.satisfiedBy Θ γ ∗ s.isPrecondFor Θ fval) -∗
        wp (body.runtime.subst (γ.update' fb.runtime fval |>.updateAll' bs vs)) P := by
  simp only [checkBody] at hbody_eval
  obtain ⟨hargNames_len, _, hbs_eq⟩ := extractArgNames_spec hext
  have hbs_runtime : bs = argNames.map Runtime.Binder.named := hbs_def ▸ hbs_eq
  set γ_body := γ.update' fb.runtime fval |>.updateAll' bs vs
  set S' : SpecMap := SpecMap.eraseAll argNames (S.insert' fb s)
  have hS'wf : S'.wfIn Signature.empty :=
    SpecMap.wfIn_eraseAll (SpecMap.wfIn_insert' hSwf hswf)
  set Γ := (argNames.zip (s.args.map Prod.snd)).foldl
    (fun ctx (x : String × TinyML.Typ) => ctx.extend x.1 x.2) TinyML.TyCtx.empty
  set B : Bindings := Bindings.empty ++ (argNames.zip argVars).reverse
  have hbwf : Bindings.wf B st'.decls := by
    intro ⟨n, v⟩ hp
    apply hargVars_mem v
    have hmem : (n, v) ∈ (argNames.zip argVars) := by simp [B, Bindings.empty] at hp; exact hp
    exact List.of_mem_zip hmem |>.2
  -- Use compile_correct
  have hcompile := VerifM.eval_bind _ _ _ _ hbody_eval
  iintro ⟨Howns, □Hvals, HQ⟩
  ihave %hlen_vals := TinyML.ValsHaveTypes.length_eq $$ Hvals
  have hlen_nv : argNames.length = vs.length := by
    simp [List.length_map] at hlen_vals
    omega
  have hlen_avs : argNames.length = argVars.length := by
    have := hargVars_lookup.length_eq
    omega
  have hagree : Bindings.agreeOnLinked B ρ'.env γ_body := by
    show Bindings.agreeOnLinked (Bindings.empty ++ (argNames.zip argVars).reverse) ρ'.env
      ((γ.update' fb.runtime fval).updateAll' bs vs)
    rw [show Bindings.empty ++ (argNames.zip argVars).reverse =
        (argNames.zip argVars).reverse ++ Bindings.empty from by simp [Bindings.empty]]
    rw [hbs_runtime]
    apply Bindings.agreeOnLinked_updateAll' Bindings.empty argNames argVars vs
      (γ.update' fb.runtime fval) ρ'.env
    · intro x x' h; simp [Bindings.empty] at h
    · exact hlen_avs
    · exact hlen_nv
    · exact hargVars_sort
    · exact hargVars_lookup
  have hts :
      TinyML.ValsHaveTypes Θ vs (s.args.map Prod.snd) ⊢
        Bindings.typedSubst Θ B Γ γ_body := by
    iintro #HvalsArg
    iapply (Bindings.typedSubst_of_agreeOnLinked (Θ := Θ) hagree)
    imodintro
    iintro %x %x' %t %hmem %hΓ
    set args' := argNames.zip (s.args.map Prod.snd)
    have hfst : args'.map Prod.fst = argNames := by
      simp [args']; exact List.map_fst_zip (by simp; omega)
    have hsnd : args'.map Prod.snd = s.args.map Prod.snd := by
      simp [args']; exact List.map_snd_zip (by simp; omega)
    iapply (val_typed_of_last_wins args' argVars vs ρ'.env TinyML.TyCtx.empty x x' t
      (by rw [hfst]; exact hlen_avs)
      (by rw [hfst]; exact hlen_nv)
      (by rw [hfst]; simp [B, Bindings.empty] at hmem; exact hmem)
      hΓ hargVars_lookup)
    rw [hsnd]
    iassumption
  have hS'_sat :
      S.satisfiedBy Θ γ ∗ s.isPrecondFor Θ fval ⊢ S'.satisfiedBy Θ γ_body := by
    have hinsert :
        S.satisfiedBy Θ γ ∗ s.isPrecondFor Θ fval ⊢
          (S.insert' fb s).satisfiedBy Θ (γ.update' fb.runtime fval) :=
      SpecMap.satisfiedBy_insert'_update'
    have herase :
        (S.insert' fb s).satisfiedBy Θ (γ.update' fb.runtime fval) ⊢
          S'.satisfiedBy Θ ((γ.update' fb.runtime fval).updateAll' (argNames.map Runtime.Binder.named) vs) :=
      SpecMap.satisfiedBy_eraseAll_updateAll' hlen_nv
    exact hinsert.trans <| by simpa [S', γ_body, hbs_runtime] using herase
  have hbody_wp :
      st'.sl ρ' ∗ (S'.satisfiedBy Θ γ_body ∗ Bindings.typedSubst Θ B Γ γ_body ∗ Q) ⊢
        wp (body.runtime.subst γ_body) P := by
    refine compile_correct body Θ Q S' B Γ st' ρ' γ_body _ _
      (VerifM.eval.decls_grow ρ' hcompile) hagree hbwf hS'wf ?_
    intro v ρ'' st'' se hΨ hse_wf heval_se
    obtain ⟨_, _, hΨ⟩ := hΨ
    by_cases hsub : TinyML.Typ.sub Θ body.ty s.retTy
    case neg =>
      simp [hsub] at hΨ
      exact (VerifM.eval_fatal hΨ).elim
    simp [hsub] at hΨ
    have hΨ' := VerifM.eval_ret hΨ
    dsimp only at hΨ'
    rw [← heval_se]
    refine (show st''.sl ρ'' ∗ TinyML.ValHasType Θ (se.eval ρ''.env) body.ty ∗ Q ⊢
        st''.sl ρ'' ∗ Q ∗
          ((TinyML.ValHasType Θ (se.eval ρ''.env) s.retTy -∗ P (se.eval ρ''.env)) -∗
            P (se.eval ρ''.env)) from ?_).trans (hΨ' _ hse_wf)
    iintro ⟨Howns, Hty, HQ⟩
    isplitl [Howns]
    · iexact Howns
    · isplitl [HQ]
      · iexact HQ
      · iintro Hwand
        iapply Hwand
        iapply (TinyML.ValHasType.sub (TinyML.Typ.sub_sound hsub))
        iexact Hty
  iintro HSat
  iapply hbody_wp
  isplitl [Howns]
  · iexact Howns
  · isplitl [HSat]
    · iapply hS'_sat
      iexact HSat
    · isplitl []
      · iapply hts
        iexact Hvals
      · iexact HQ

theorem checkSpec_correct (Θ : TinyML.TypeEnv) (S : SpecMap) (e : Expr) (s : Spec)
    (γ : Runtime.Subst)
    (hswf : s.wfIn Signature.empty) (hSwf : S.wfIn Signature.empty)
    (ρ : VerifM.Env) :
    VerifM.eval (checkSpec Θ S e s) TransState.empty ρ (fun _ _ _ => True) →
    S.satisfiedBy Θ γ ⊢ wp (e.runtime.subst γ) (fun v => s.isPrecondFor Θ v) := by
  intro heval
  -- All non-`fix` shapes (and bad `extractArgNames`) discharge the same way.
  have elim_bind_fatal : ∀ {α β} {msg} {k : α → VerifM β} {st ρ Ψ},
      VerifM.eval (VerifM.fatal msg >>= k) st ρ Ψ → False :=
    fun h => VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ h)
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
      have himpl := VerifM.eval_ret (VerifM.eval_bind _ _ _ _ heval)
      dsimp only at himpl
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
      obtain ⟨_, _, hbs_eq⟩ := extractArgNames_spec hext
      have hbs_runtime : bs = argNames.map Runtime.Binder.named := hbs_eq
      apply SpatialContext.wp_func
      apply Spec.isPrecondFor_fix
      istart
      iintro □Hspec
      imodintro
      iintro Hrec %vs %P #Htyped Hpred
      -- `isPrecondFor_fix` hands us the body's subst as `id.update' ... |>.updateAll' ...`;
      -- fuse it with γ via `subst_fix_comp` so it matches `body_correct`.
      ihave %hlen_typed := TinyML.ValsHaveTypes.length_eq $$ Htyped
      have hlen_vs : bs.length = vs.length := by
        simp [hbs_runtime, List.length_map] at hlen_typed ⊢
        omega
      have hsub := Runtime.Expr.subst_fix_comp body.runtime fb.runtime bs γ fval vs hlen_vs
      simp only [] at hsub; rw [hsub]
      have hbody' : TinyML.ValsHaveTypes Θ vs (s.args.map Prod.snd) ∗
          PredTrans.apply (fun r => TinyML.ValHasType Θ r s.retTy -∗ P r) s.pred
          (Spec.argsEnv VerifM.Env.empty s.args vs) ⊢
          SpecMap.satisfiedBy Θ S γ ∗ s.isPrecondFor Θ fval -∗
            wp (Runtime.Expr.subst ((Runtime.Subst.update' fb.runtime fval γ).updateAll' bs vs) body.runtime) P := by
        iintro H
        icases H with ⟨Htyped', Hpred'⟩
        iintuitionistic Htyped'
        ihave Hwand := Spec.implement_correct Θ s _ TransState.empty ρ vs P
          (TinyML.ValsHaveTypes Θ vs (s.args.map Prod.snd) -∗
            (S.satisfiedBy Θ γ ∗ s.isPrecondFor Θ fval) -∗
              wp (body.runtime.subst (γ.update' fb.runtime fval |>.updateAll' bs vs)) P)
          hswf himpl
          (fun argVars st' ρ' Q hargVars_mem hargVars_sort hargVars_lookup hbody_eval => by
            iintro ⟨Hsl, HQ⟩ Htyped''
            iapply (checkBody_correct Θ S s γ hswf hSwf fb argBinders body argNames
              hext bs rfl fval vs P hargVars_mem hargVars_sort hargVars_lookup hbody_eval)
            isplitl [Hsl]
            · iexact Hsl
            · isplitl [Htyped'']
              · iexact Htyped''
              · iexact HQ) $$ [Htyped' Hpred']
        · isplitl []
          · simp [TransState.sl]
            iemp_intro
          · isplitl [Htyped']
            · iexact Htyped'
            · iexact Hpred'
        iapply Hwand
        iexact Htyped'
      iapply hbody' $$ [Htyped Hpred] [Hrec]
      · isplitl [Htyped]
        · iexact Htyped
        · iexact Hpred
      · isplitl []
        · iexact Hspec
        · iexact Hrec
  all_goals
    simp only [checkSpec] at heval
    exact (elim_bind_fatal heval).elim
