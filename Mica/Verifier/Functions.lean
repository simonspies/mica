import Mica.TinyML.Typed
import Mica.TinyML.Erasure
import Mica.TinyML.Typing
import Mica.TinyML.OpSem
import Mica.TinyML.WeakestPre
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
    if body.ty.sub Θ s.retTy then pure ()
    else VerifM.fatal s!"checkSpec: return type mismatch"
    pure se

theorem checkSpec_correct (Θ : TinyML.TypeEnv) (S : SpecMap) (e : Expr) (s : Spec)
    (γ : Runtime.Subst)
    (hswf : s.wfIn Signature.empty) (hSwf : S.wfIn Signature.empty)
    (hS : S.satisfiedBy Θ γ)
    (st : TransState) (ρ : Env) :
    VerifM.eval (checkSpec Θ S e s) st ρ (fun _ _ _ => True) →
    wp (e.runtime.subst γ) (fun v => s.isPrecondFor Θ v) := by
  intro heval
  cases e with
  | fix fb argBinders retTy body =>
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
      apply wp.func
      intro vs htyped Φ happly
      set Φ_inv : (Runtime.Val → Prop) → List Runtime.Val → Prop := fun P vs =>
        TinyML.ValsHaveTypes Θ vs (s.args.map Prod.snd) ∧
          PredTrans.apply (fun r => TinyML.ValHasType Θ r s.retTy → P r) s.pred
            (Spec.argsEnv Env.empty s.args vs)
      suffices ∀ vs P, Φ_inv P vs → wp (Runtime.Expr.app (.val fval) (vs.map Runtime.Expr.val)) P from
        this vs Φ ⟨htyped, happly⟩
      exact wp.fix' (body.runtime.subst γ') Φ_inv (fun ih_rec vs P ⟨htyped_args, happly_args⟩ => by
        -- Rewrite the double substitution into a single one
        obtain ⟨hlen1, hlen2, hbs_eq⟩ := extractArgNames_spec hext
        have hlen_nv0 : argNames.length = vs.length := by
          have := htyped_args.length_eq; simp at this; omega
        have hbs_runtime : bs = argNames.map Runtime.Binder.named := by
          simp only [bs]
          exact hbs_eq
        have hlen : bs.length = vs.length := by simp [hbs_runtime]; omega
        rw [Runtime.Expr.subst_fix_comp body.runtime fb.runtime bs γ fval vs hlen]
        set γ_body := γ.update' fb.runtime fval |>.updateAll' bs vs
        -- Use implement_correct to get into the body
        apply Spec.implement_correct Θ s _ _ _ vs _ (wp (body.runtime.subst γ_body) P) hswf htyped_args hbody happly_args
        intro argVars st' ρ' hargVars_mem hargVars_sort hargVars_lookup hbody_eval
        -- Key facts about fval and the spec map
        have isPrecond : s.isPrecondFor Θ fval := by
          intro vs' htyped' Φ' happly'
          exact ih_rec vs' Φ' ⟨htyped', happly'⟩
        have hS'wf : S'.wfIn Signature.empty :=
          SpecMap.wfIn_eraseAll (SpecMap.wfIn_insert' hSwf hswf)
        have hS'_sat : S'.satisfiedBy Θ γ_body := by
          -- Simplified using the new lemma
          have hS_ext : (S.insert' fb s).satisfiedBy Θ (γ.update' fb.runtime fval) := by
            apply SpecMap.satisfiedBy_insert'_update' hS isPrecond
          have hsat := SpecMap.satisfiedBy_eraseAll_updateAll' hS_ext hlen_nv0
          -- hsat : (eraseAll argNames (insert' S fb s)).satisfiedBy ((γ.update' fb.runtime fval).updateAll' (argNames.map .named) vs)
          -- γ_body : (γ.update' fb.runtime fval).updateAll' bs vs
          -- and bs = argNames.map .named (from hbs_eq)
          change (SpecMap.eraseAll argNames (S.insert' fb s)).satisfiedBy Θ ((γ.update' fb.runtime fval).updateAll' bs vs)
          rw [hbs_runtime]; exact hsat
        set Γ := (argNames.zip (s.args.map Prod.snd)).foldl (fun ctx (x : String × TinyML.Typ) => ctx.extend x.1 x.2) TinyML.TyCtx.empty
        set B : Bindings := Bindings.empty ++ (argNames.zip argVars).reverse
        have hlen_avs : argNames.length = argVars.length := by
          have := hargVars_lookup.length_eq
          have := htyped_args.length_eq; simp at this; omega
        have hlen_vals : argNames.length = vs.length := by
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
          · exact hlen_vals
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
            (by rw [hfst]; exact hlen_vals)
            (by rw [hfst]; simp [B, Bindings.empty] at hmem; exact hmem)
            hΓ hargVars_lookup
            (by rw [hsnd]; exact htyped_args)
        have hcompile := VerifM.eval_bind _ _ _ _ hbody_eval
        apply compile_correct Θ body S' B Γ st' ρ' γ_body _ P
          hcompile hagree hbwf hts hS'_sat hS'wf
        intro result ρ'' st'' se hΨ hse_wf hse_eval htyped_result
        by_cases hsub : body.ty.sub Θ s.retTy
        · simp [hsub] at hΨ
          have hret := VerifM.eval_ret (VerifM.eval_bind _ _ _ _ hΨ)
          have hret' := VerifM.eval_ret hret
          rw [hse_eval] at hret'
          exact hret' hse_wf (TinyML.ValHasType_sub htyped_result (TinyML.Typ.sub_iff.mp hsub))
        · simp [hsub] at hΨ
          exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ hΨ)).elim)
  | _ =>
    simp only [checkSpec] at heval
    exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ heval)).elim
