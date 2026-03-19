import Mica.TinyML.Expr
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


/-- Extract argument names from binders, pairing with spec arg info.
    Requires exact length match. -/
private def extractArgNames : List (TinyML.Binder × Option TinyML.Type_) → List (String × TinyML.Type_) →
    Except String (List String)
  | [], [] => .ok []
  | (.named x, _) :: rest, _ :: specRest => do
    let tail ← extractArgNames rest specRest
    .ok (x :: tail)
  | _, _ => .error "checkSpec: argument mismatch"

private theorem extractArgNames_spec {argBinders : List (TinyML.Binder × Option TinyML.Type_)}
    {specArgs : List (String × TinyML.Type_)} {names : List String}
    (h : extractArgNames argBinders specArgs = .ok names) :
    names.length = specArgs.length ∧
    argBinders.length = specArgs.length ∧
    argBinders.map Prod.fst = names.map TinyML.Binder.named := by
  induction specArgs generalizing argBinders names with
  | nil =>
    cases argBinders with
    | nil => simp [extractArgNames] at h; subst h; simp
    | cons _ _ => simp [extractArgNames] at h
  | cons sa sas ih =>
    cases argBinders with
    | nil => simp [extractArgNames] at h
    | cons ab abs =>
      obtain ⟨b, ty⟩ := ab
      cases b with
      | none => simp [extractArgNames] at h
      | named x =>
        unfold extractArgNames at h
        cases hrec : extractArgNames abs sas with
        | error => rw [hrec] at h; exact absurd h (by intro hc; cases hc)
        | ok tail =>
          rw [hrec] at h
          have h' : names = x :: tail := by cases h; rfl
          subst h'
          obtain ⟨h1, h2, h3⟩ := ih hrec
          exact ⟨by simp [h1], by simp [h2], by simp [h3]⟩

def checkSpec (S : SpecMap) (e : TinyML.Expr) (s : Spec) : VerifM Unit := do
  let (fb, argNames, body) ← match e with
    | .fix fb argBinders _ body => do
      match extractArgNames argBinders s.args with
      | .ok names => pure (fb, names, body)
      | .error msg => VerifM.fatal msg
    | _ => VerifM.fatal "checkSpec: expected function"
  let S' := SpecMap.eraseAll argNames (S.insert' fb s)
  Spec.implement s fun argVars => do
    let B : Bindings := (argNames.zip argVars).reverse
    let Γ := (argNames.zip (s.args.map Prod.snd)).foldl (fun ctx (name, ty) => ctx.extend name ty) TinyML.TyCtx.empty
    let (retTy, se) ← compile S' B Γ body
    if retTy.sub s.retTy then pure ()
    else VerifM.fatal s!"checkSpec: return type mismatch"
    pure se

theorem checkSpec_correct (S : SpecMap) (e : TinyML.Expr) (s : Spec)
    (γ : TinyML.Subst)
    (hswf : s.wfIn []) (hSwf : S.wfIn [])
    (hS : S.satisfiedBy γ)
    (st : TransState) (ρ : Env) :
    VerifM.eval (checkSpec S e s) st ρ (fun _ _ _ => True) →
    wp (e.subst γ) (fun v => s.isPrecondFor v) := by
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
      set bs := argBinders.map Prod.fst
      let γ' := (γ.remove' fb).removeAll' bs
      set fval := TinyML.Val.fix fb argBinders retTy (body.subst γ')
      set S' : SpecMap := SpecMap.eraseAll argNames (S.insert' fb s)
      simp only [TinyML.Expr.subst]
      apply wp.func
      intro vs htyped Φ happly
      set Φ_inv : (TinyML.Val → Prop) → List TinyML.Val → Prop := fun P vs =>
        TinyML.ValsHaveTypes vs (s.args.map Prod.snd) ∧
          PredTrans.apply (fun r => TinyML.ValHasType r s.retTy → P r) s.pred
            (Spec.argsEnv Env.empty s.args vs)
      suffices ∀ vs P, Φ_inv P vs → wp (TinyML.Expr.app (.val fval) (vs.map TinyML.Expr.val)) P from
        this vs Φ ⟨htyped, happly⟩
      exact wp.fix' (body.subst γ') Φ_inv (fun ih_rec vs P ⟨htyped_args, happly_args⟩ => by
        -- Rewrite the double substitution into a single one
        obtain ⟨hlen1, hlen2, hbs_eq⟩ := extractArgNames_spec hext
        have hlen_nv0 : argNames.length = vs.length := by
          have := htyped_args.length_eq; simp at this; omega
        have hlen : bs.length = vs.length := by simp [bs, hbs_eq]; omega
        rw [TinyML.Expr.subst_fix_comp body fb bs γ fval vs hlen]
        set γ_body := γ.update' fb fval |>.updateAll' bs vs
        -- Use implement_correct to get into the body
        apply Spec.implement_correct s _ _ _ vs _ (wp (body.subst γ_body) P) hswf htyped_args hbody happly_args
        intro argVars st' ρ' hargVars_mem hargVars_sort hargVars_lookup hbody_eval
        -- Key facts about fval and the spec map
        have isPrecond : s.isPrecondFor fval := by
          intro vs' htyped' Φ' happly'
          exact ih_rec vs' Φ' ⟨htyped', happly'⟩
        have hS'wf : S'.wfIn [] :=
          SpecMap.wfIn_eraseAll (SpecMap.wfIn_insert' hSwf hswf)
        have hS'_sat : S'.satisfiedBy γ_body := by
          intro y s' hlookup
          -- y is in S' = eraseAll argNames (insert' S fb s)
          -- so y ∉ argNames (erased) and y is in insert' S fb s
          -- Since y ∉ argNames and bs = argNames.map .named, updateAll' doesn't touch y
          have hy_notin : y ∉ argNames := by
            intro hmem
            have := SpecMap.eraseAll_lookup_none hmem (S := S.insert' fb s)
            rw [this] at hlookup; exact absurd hlookup (by simp)
          have hlen_nv : argNames.length = vs.length := by
            have := htyped_args.length_eq; simp at this; omega
          have hγ_body_y : γ_body y = (γ.update' fb fval) y := by
            show ((γ.update' fb fval).updateAll' bs vs) y = _
            simp only [bs, hbs_eq]
            rw [TinyML.Subst.updateAll'_eq _ _ _ _ (by simp; omega)]
            rw [findVal_none_of_not_mem argNames vs y (by omega) hy_notin]
          -- Now case split on whether y = fb name
          have hlookup' : (S.insert' fb s).lookup y = some s' := by
            rwa [← SpecMap.eraseAll_lookup_of_notin hy_notin]
          cases hfb : fb with
          | none =>
            simp [SpecMap.insert', hfb] at hlookup'
            obtain ⟨f, hγf, hprecond⟩ := hS y s' hlookup'
            refine ⟨f, ?_, hprecond⟩
            rw [hγ_body_y]; simp [TinyML.Subst.update', hfb, hγf]
          | named fx =>
            simp only [SpecMap.insert', hfb] at hlookup'
            by_cases hyfx : y = fx
            · subst hyfx
              rw [Finmap.lookup_insert] at hlookup'; simp at hlookup'; subst hlookup'
              refine ⟨fval, ?_, isPrecond⟩
              rw [hγ_body_y]; simp [TinyML.Subst.update', hfb, TinyML.Subst.update_eq]
            · rw [Finmap.lookup_insert_of_ne _ hyfx] at hlookup'
              obtain ⟨f, hγf, hprecond⟩ := hS y s' hlookup'
              refine ⟨f, ?_, hprecond⟩
              rw [hγ_body_y]
              simp [TinyML.Subst.update', hfb, TinyML.Subst.update_eq, beq_false_of_ne hyfx, hγf]
        set Γ := (argNames.zip (s.args.map Prod.snd)).foldl (fun ctx (x : String × TinyML.Type_) => ctx.extend x.1 x.2) TinyML.TyCtx.empty
        set B : Bindings := (argNames.zip argVars).reverse
        have hlen_avs : argNames.length = argVars.length := by
          have := hargVars_lookup.length_eq
          have := htyped_args.length_eq; simp at this; omega
        have hlen_vals : argNames.length = vs.length := by
          have := htyped_args.length_eq; simp at this; omega
        have hagree : Bindings.agreeOnLinked B ρ' γ_body := by
          show Bindings.agreeOnLinked (argNames.zip argVars).reverse ρ'
            ((γ.update' fb fval).updateAll' bs vs)
          simp only [bs, hbs_eq]
          exact Bindings.agreeOnLinked_zip_reverse argNames argVars vs
            (γ.update' fb fval) ρ' hlen_avs hlen_vals
            hargVars_sort hargVars_lookup
        have hbwf : Bindings.wf B st'.decls := by
          intro ⟨n, v⟩ hp
          apply hargVars_mem v
          have hmem : (n, v) ∈ (argNames.zip argVars) := List.mem_reverse.mp hp
          exact List.of_mem_zip hmem |>.2
        have hts : Bindings.typedSubst B Γ γ_body := by
          apply Bindings.typedSubst_of_agreeOnLinked hagree
          intro x x' t hmem hΓ
          show TinyML.ValHasType (ρ'.lookup .value x'.name) t
          set args' := argNames.zip (s.args.map Prod.snd)
          have hfst : args'.map Prod.fst = argNames := by
            simp [args']; exact List.map_fst_zip (by simp; omega)
          have hsnd : args'.map Prod.snd = s.args.map Prod.snd := by
            simp [args']; exact List.map_snd_zip (by simp; omega)
          exact val_typed_of_last_wins args' argVars vs ρ' TinyML.TyCtx.empty x x' t
            (by rw [hfst]; exact hlen_avs)
            (by rw [hfst]; exact hlen_vals)
            (by rw [hfst]; exact hmem)
            hΓ hargVars_lookup
            (by rw [hsnd]; exact htyped_args)
        have hcompile := VerifM.eval_bind _ _ _ _ hbody_eval
        apply compile_correct body S' B Γ st' ρ' γ_body _ P
          hcompile hagree hbwf hts hS'_sat hS'wf
        intro result ρ'' st'' retTy' se hΨ hse_wf hse_eval htyped_result
        by_cases hsub : retTy'.sub s.retTy
        · simp [hsub] at hΨ
          have hret := VerifM.eval_ret (VerifM.eval_bind _ _ _ _ hΨ)
          have hret' := VerifM.eval_ret hret
          rw [hse_eval] at hret'
          exact hret' hse_wf (TinyML.ValHasType_sub htyped_result (TinyML.Type_.sub_iff.mp hsub))
        · simp [hsub] at hΨ
          exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ hΨ)).elim)
  | _ =>
    simp only [checkSpec] at heval
    exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ heval)).elim
