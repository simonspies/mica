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



def checkSpec (S : SpecMap) (e : TinyML.Expr) (s : Spec) : VerifM Unit := do
  let (fb, argName, body) ← match e with
    | .fix fb (.named arg) (.some _) _ body => pure (fb, arg, body)
    | _ => VerifM.fatal "checkSpec: expected single-argument function"
  let S' := (S.insert' fb s).erase argName
  Spec.implement s fun argVar => do
    let (retTy, se) ← compile S' [(argName, argVar)] (TinyML.TyCtx.empty.extend argName s.argTy) body
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
  | fix fb xb argTy retTy body =>
    cases xb with
    | named arg =>
      cases argTy with
      | some at_ =>
        simp only [checkSpec] at heval
        have hbody := VerifM.eval_ret (VerifM.eval_bind _ _ _ _ heval)
        dsimp only at hbody
        let γ' := (γ.remove' fb).remove' (.named arg)
        set fval := TinyML.Val.fix fb (.named arg) (.some at_) retTy (body.subst γ')
        set S' : SpecMap := (SpecMap.insert' S fb s).erase arg
        simp only [TinyML.Expr.subst]
        apply wp.func
        intro v_arg htyped Φ happly
        set Φ_inv : (TinyML.Val → Prop) → TinyML.Val → Prop := fun P v =>
          TinyML.ValHasType v s.argTy ∧
            PredTrans.apply (fun r => TinyML.ValHasType r s.retTy → P r) s.pred
              (Env.empty.update .value s.argName v)
        suffices ∀ v P, Φ_inv P v → wp (TinyML.Expr.app (.val fval) (.val v)) P from
          this v_arg Φ ⟨htyped, happly⟩
        exact wp.fix' (.some at_) retTy (body.subst γ') Φ_inv (fun ih_rec v_arg P ⟨htyped_arg, happly_arg⟩ => by
        apply Spec.implement_correct s _ _ _ v_arg _ (wp ((body.subst γ').subst _) P) hswf hbody happly_arg
        intro argVar st' ρ' hargVar_mem hargVar_sort hargVar_val hbody_eval
        set γ_body := γ.update' fb fval |>.update' (.named arg) v_arg
        rw [TinyML.Expr.subst_fix_comp body fb arg γ fval v_arg]
        have hγ_arg : γ_body arg = some v_arg := by simp [γ_body, TinyML.Subst.update']
        have isPrecond : s.isPrecondFor fval := by
          intro v' htyped' Φ' happly'
          exact ih_rec v' Φ' ⟨htyped', happly'⟩
        have hS'_sat : S'.satisfiedBy γ_body := by
          intro y s' hlookup
          simp only [S'] at hlookup
          by_cases hya : y = arg
          · subst hya; simp [Finmap.lookup_erase] at hlookup
          · rw [Finmap.lookup_erase_ne hya] at hlookup
            cases hfb : fb with
            | none =>
              simp [SpecMap.insert', hfb] at hlookup
              obtain ⟨f, hγf, hprecond⟩ := hS y s' hlookup
              refine ⟨f, ?_, hprecond⟩
              simp [γ_body, TinyML.Subst.update', hfb, TinyML.Subst.update_eq,
                beq_false_of_ne hya, hγf]
            | named fx =>
              simp only [SpecMap.insert', hfb] at hlookup
              by_cases hyfx : y = fx
              · subst hyfx
                rw [Finmap.lookup_insert] at hlookup; simp at hlookup; subst hlookup
                refine ⟨fval, ?_, isPrecond⟩
                simp [γ_body, TinyML.Subst.update', hfb, TinyML.Subst.update_eq,
                  beq_false_of_ne hya]
              · rw [Finmap.lookup_insert_of_ne _ hyfx] at hlookup
                obtain ⟨f, hγf, hprecond⟩ := hS y s' hlookup
                refine ⟨f, ?_, hprecond⟩
                simp [γ_body, TinyML.Subst.update', hfb, TinyML.Subst.update_eq,
                  beq_false_of_ne hya, beq_false_of_ne hyfx, hγf]
        have hS'wf : S'.wfIn [] :=
          SpecMap.wfIn_erase (SpecMap.wfIn_insert' hSwf hswf)
        have hagree : Bindings.agreeOnLinked [(arg, argVar)] ρ' γ_body := by
          intro x x' hmem
          simp only [List.lookup] at hmem
          split at hmem
          · next heq =>
            have hxa : x = arg := by simpa using heq
            subst hxa; simp at hmem; subst hmem
            exact ⟨hargVar_sort, by simp [hargVar_val, hγ_arg]⟩
          · simp at hmem
        have hbwf : Bindings.wf [(arg, argVar)] st'.decls := by
          intro p hp; simp at hp; subst hp; exact hargVar_mem
        have hts : Bindings.typedSubst [(arg, argVar)]
            (TinyML.TyCtx.empty.extend arg s.argTy) γ_body := by
          intro x x' t hmem hΓ
          simp only [List.lookup] at hmem
          split at hmem
          · next heq =>
            have hxa : x = arg := by simpa using heq
            subst hxa; simp at hmem; subst hmem
            simp [TinyML.TyCtx.extend] at hΓ; subst hΓ
            exact ⟨v_arg, hγ_arg, htyped_arg⟩
          · simp at hmem
        have hcompile := VerifM.eval_bind _ _ _ _ hbody_eval
        apply compile_correct body S' [(arg, argVar)]
          (TinyML.TyCtx.empty.extend arg s.argTy) st' ρ' γ_body _ P
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
      | none =>
        simp only [checkSpec] at heval
        exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ heval)).elim
    | none =>
      simp only [checkSpec] at heval
      exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ heval)).elim
  | _ =>
    simp only [checkSpec] at heval
    exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ heval)).elim
