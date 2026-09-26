-- SUMMARY: Capture-avoiding substitution for first-order syntax and its well-formedness conditions.
import Mica.FirstOrderLogic.Terms
import Mica.FirstOrderLogic.Formulas
import Mica.Base.Fresh

/-!
# Substitution

A substitution replaces variables with terms. In a formula, it renames the
bound variables so that no binder captures a variable of a substituted term.
Substitution keeps well-formedness, and evaluating a substituted term or formula
is the same as evaluating the original in a changed environment.
-/

/-! ## Substitutions -/

def Subst := (τ : Srt) → String → Term τ

def Subst.id : Subst := fun τ x => .var τ x

def Subst.apply (σ : Subst) (τ : Srt) (x : String) : Term τ := σ τ x

def Subst.update (σ : Subst) (τ : Srt) (x : String) (s : Term τ) : Subst := fun τ' y =>
  if h : τ' = τ ∧ y = x then h.1 ▸ s else σ τ' y

def Subst.remove (σ : Subst) (x : String) : Subst := fun τ y =>
  if y = x then .var τ y else σ τ y

/-- `σ` below the binder `y`, which becomes `y'`. -/
def Subst.bind (σ : Subst) (y : String) (τ : Srt) (y' : String) : Subst :=
  (σ.remove y).update τ y (.var τ y')

private theorem Subst.apply_update_same {σ : Subst} {τ : Srt} {x : String} {t : Term τ} :
    (σ.update τ x t).apply τ x = t := by
  simp [Subst.update, Subst.apply]

theorem Subst.apply_update_ne {σ : Subst} {τ τ' : Srt} {x y : String} {t : Term τ}
    (h : y ≠ x ∨ τ' ≠ τ) : (σ.update τ x t).apply τ' y = σ.apply τ' y := by
  simp only [Subst.update, Subst.apply]
  split
  · next heq => cases h with
    | inl h => exact absurd heq.2 h
    | inr h => exact absurd heq.1 h
  · rfl

theorem Subst.apply_remove_ne {σ : Subst} {τ : Srt} {x y : String}
    (h : y ≠ x) : (σ.remove x).apply τ y = σ.apply τ y := by
  simp [Subst.remove, Subst.apply, h]

/-! ## Well-formedness -/

/-- `σ` maps each variable of `dom` to a term that is well-formed in `Δ`, and
each other variable to itself. -/
def Subst.wfIn (σ : Subst) (dom : List Var) (Δ : Signature) : Prop :=
  (∀ v ∈ dom, (σ.apply v.sort v.name).wfIn Δ) ∧
  (∀ v, v ∉ dom → σ.apply v.sort v.name = .var v.sort v.name)

theorem Subst.wfIn_mono {σ : Subst} {dom : List Var} {Δ Δ' : Signature}
    (hσ : σ.wfIn dom Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) :
    σ.wfIn dom Δ' :=
  ⟨fun v hv => Term.wfIn_mono _ (hσ.1 v hv) hsub hwf, hσ.2⟩

theorem Subst.id_wfIn {dom : List Var} {Δ : Signature} (hsub : dom ⊆ Δ.vars) (hwf : Δ.wf) :
    Subst.id.wfIn dom Δ :=
  ⟨fun v hv => by
      refine ⟨hsub hv, ?_, ?_⟩
      · intro τ' hconst
        exact Signature.wf_no_const_of_var hwf (hsub hv) hconst
      · intro τ' hv'
        exact Signature.wf_unique_var hwf (hsub hv) hv',
    fun _ _ => rfl⟩

theorem Subst.wfIn_update {σ : Subst} {dom : List Var} {τ : Srt} {x : String} {t : Term τ} {Δ : Signature}
    (hσ : σ.wfIn dom Δ) (ht : t.wfIn Δ) :
    (σ.update τ x t).wfIn (⟨x, τ⟩ :: dom) Δ := by
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩ <;> by_cases h : v.name = x ∧ v.sort = τ
  · cases v; obtain ⟨rfl, rfl⟩ := h
    simpa [Subst.apply_update_same] using ht
  · rw [Subst.apply_update_ne (not_and_or.mp h)]
    exact hσ.1 v (by cases v; simp_all)
  · cases v; obtain ⟨rfl, rfl⟩ := h; simp at hv
  · rw [Subst.apply_update_ne (not_and_or.mp h)]
    exact hσ.2 v (by simp_all)

theorem Subst.wfIn_remove {σ : Subst} {dom : List Var} {Δ : Signature} {x : String}
    (hσ : σ.wfIn dom Δ) :
    (σ.remove x).wfIn (dom.filter (fun v => v.name != x)) Δ := by
  refine ⟨?_, ?_⟩
  · intro v hv
    have hv' : v ∈ dom ∧ v.name ≠ x := by
      simpa using hv
    rw [Subst.apply_remove_ne hv'.2]
    exact hσ.1 v hv'.1
  · intro v hv
    by_cases hname : v.name = x
    · simp [Subst.remove, Subst.apply, hname]
    · rw [Subst.apply_remove_ne hname]
      apply hσ.2
      intro hvdom
      apply hv
      simp [hvdom, hname]

private theorem Subst.wfIn_bind {σ : Subst} {Δ Δ'' : Signature} {y y' : String} {τ : Srt}
    (hσ : σ.wfIn Δ.vars Δ'') (hvarwf : (Term.var τ y').wfIn Δ'') :
    (σ.bind y τ y').wfIn (Δ.declVar ⟨y, τ⟩).vars Δ'' := by
  have hσ_erase : (σ.remove y).wfIn (Δ.remove y).vars Δ'' := by
    simpa [Signature.remove] using
      (Subst.wfIn_remove (σ := σ) (dom := Δ.vars) (Δ := Δ'') (x := y) hσ)
  simpa [Subst.bind, Signature.declVar, Signature.addVar] using
    (Subst.wfIn_update (σ := σ.remove y) (dom := (Δ.remove y).vars) (x := y) hσ_erase hvarwf)

/-- The binder case of `Formula.subst`. -/
theorem Subst.wfIn_bind_fresh {σ : Subst} {Δ Δ' : Signature} {y y' : String} {τ : Srt}
    (hσ : σ.wfIn Δ.vars Δ') (hwfΔ' : Δ'.wf) (hfresh : y' ∉ Δ'.allNames) :
    (σ.bind y τ y').wfIn (Δ.declVar ⟨y, τ⟩).vars (Δ'.declVar ⟨y', τ⟩) :=
  have hwf_target : (Δ'.declVar ⟨y', τ⟩).wf := Signature.wf_declVar hwfΔ'
  Subst.wfIn_bind
    (Subst.wfIn_mono hσ (Signature.subset_declVar_of_fresh hfresh) hwf_target)
    (Term.var_wfIn_declVar hwf_target)

/-! ## Evaluation -/

/-- The environment in which each variable has the value of its image under `σ`. -/
def Subst.eval (σ : Subst) (ρ : Env) : Env :=
  { ρ with consts := fun τ x => Term.eval ρ (σ.apply τ x) }

theorem Subst.eval_lookup (σ : Subst) (ρ : Env) (τ : Srt) (x : String) :
    (σ.eval ρ).lookupConst τ x = Term.eval ρ (σ.apply τ x) := by
  simp [Subst.eval, Env.lookupConst]

@[simp] theorem Subst.id_eval (ρ : Env) : Subst.id.eval ρ = ρ := rfl

theorem Subst.eval_update (σ : Subst) (ρ : Env) (τ : Srt) (x : String) (t : Term τ) :
    (σ.update τ x t).eval ρ = (σ.eval ρ).updateConst τ x (Term.eval ρ t) := by
  refine Env.ext ?_ rfl rfl rfl rfl rfl
  funext τ' y
  simp only [Subst.eval, Subst.update, Subst.apply, Env.updateConst]
  split
  · next h => obtain ⟨rfl, rfl⟩ := h; rfl
  · rfl

/-! ## Terms -/

def Term.subst (σ : Subst) : Term τ → Term τ
  | .var τ y   => σ.apply τ y
  | .const c   => .const c
  | .unop op a => .unop op (a.subst σ)
  | .binop op a b => .binop op (a.subst σ) (b.subst σ)
  | .terop op a b c => .terop op (a.subst σ) (b.subst σ) (c.subst σ)
  | .ite c t e => .ite (c.subst σ) (t.subst σ) (e.subst σ)

theorem Term.subst_wfIn {t : Term τ} {σ : Subst} {dom : List Var} {Δ Δ' : Signature}
    (ht : t.wfIn Δ) (hσ : σ.wfIn dom Δ') (hdom : Δ.vars ⊆ dom)
    (hsymbols : Δ.SymbolSubset Δ')
    (hwf : Δ'.wf) :
    (t.subst σ).wfIn Δ' := by
  induction t generalizing Δ Δ' σ with
  | var τ x => exact hσ.1 ⟨x, τ⟩ (hdom ht.1)
  | const c => exact Const.wfIn_mono ht hsymbols hwf
  | unop op a iha => exact ⟨UnOp.wfIn_mono ht.1 hsymbols hwf, iha ht.2 hσ hdom hsymbols hwf⟩
  | binop op a b iha ihb =>
    exact ⟨BinOp.wfIn_mono ht.1 hsymbols hwf, iha ht.2.1 hσ hdom hsymbols hwf,
      ihb ht.2.2 hσ hdom hsymbols hwf⟩
  | terop op a b c iha ihb ihc =>
    exact ⟨TerOp.wfIn_mono ht.1 hsymbols hwf, iha ht.2.1 hσ hdom hsymbols hwf,
      ihb ht.2.2.1 hσ hdom hsymbols hwf, ihc ht.2.2.2 hσ hdom hsymbols hwf⟩
  | ite c t e ihc iht ihe =>
    exact ⟨ihc ht.1 hσ hdom hsymbols hwf, iht ht.2.1 hσ hdom hsymbols hwf,
      ihe ht.2.2 hσ hdom hsymbols hwf⟩

theorem Term.eval_subst {σ : Subst} {ρ : Env} {t : Term τ} {Δ Δ' : Signature}
    (ht : t.wfIn Δ) (hσ : σ.wfIn Δ.vars Δ') (hwfΔ' : Δ'.wf) :
    Term.eval ρ (t.subst σ) = Term.eval (σ.eval ρ) t := by
  induction t generalizing Δ Δ' with
  | var τ y =>
    simp [Term.subst, Term.eval, Subst.eval_lookup]
  | const c =>
    cases c with
    | uninterpreted name _ =>
      simp [Term.subst, Term.eval, Const.eval, Subst.eval, hσ.2 ⟨name, _⟩ (ht.2.1 _),
        Env.lookupConst]
    | _ => rfl
  | unop op a iha =>
    simp only [Term.subst, Term.eval]
    rw [iha ht.2 hσ hwfΔ']
    cases op <;> rfl
  | binop op a b iha ihb =>
    simp only [Term.subst, Term.eval]
    rw [iha ht.2.1 hσ hwfΔ', ihb ht.2.2 hσ hwfΔ']
    cases op <;> rfl
  | terop op a b c iha ihb ihc =>
    simp only [Term.subst, Term.eval]
    rw [iha ht.2.1 hσ hwfΔ', ihb ht.2.2.1 hσ hwfΔ', ihc ht.2.2.2 hσ hwfΔ']
    cases op <;> rfl
  | ite c t e ihc iht ihe =>
    simp [Term.subst, Term.eval, ihc ht.1 hσ hwfΔ', iht ht.2.1 hσ hwfΔ', ihe ht.2.2 hσ hwfΔ']

/-! ## Formulas -/

def Pattern.subst (σ : Subst) : Pattern → Pattern
  | .term t => .term (t.subst σ)
  | .unpred p t => .unpred p (t.subst σ)
  | .binpred p t₁ t₂ => .binpred p (t₁.subst σ) (t₂.subst σ)

/-- Each binder gets a name outside `avoid`, so that it captures no variable of
the substituted terms. -/
def Formula.subst (σ : Subst) (avoid : List String) : Formula → Formula
  | .true_  => .true_
  | .false_ => .false_
  | .eq τ a b      => .eq τ (a.subst σ) (b.subst σ)
  | .unpred p v    => .unpred p (v.subst σ)
  | .binpred p a b => .binpred p (a.subst σ) (b.subst σ)
  | .not φ         => .not (Formula.subst σ avoid φ)
  | .and φ ψ       => .and (Formula.subst σ avoid φ) (Formula.subst σ avoid ψ)
  | .or φ ψ        => .or (Formula.subst σ avoid φ) (Formula.subst σ avoid ψ)
  | .implies φ ψ   => .implies (Formula.subst σ avoid φ) (Formula.subst σ avoid ψ)
  | .forall_ y τ ps φ =>
    let y' := Fresh.freshName avoid y
    .forall_ y' τ (ps.map (Pattern.subst (σ.bind y τ y')))
      (Formula.subst (σ.bind y τ y') (y' :: avoid) φ)
  | .exists_ y τ φ =>
    let y' := Fresh.freshName avoid y
    .exists_ y' τ (Formula.subst (σ.bind y τ y') (y' :: avoid) φ)

private theorem Pattern.subst_wfIn {p : Pattern} {σ : Subst} {dom : List Var}
    {Δ Δ' : Signature}
    (hp : p.wfIn Δ) (hσ : σ.wfIn dom Δ') (hdom : Δ.vars ⊆ dom)
    (hsymbols : Δ.SymbolSubset Δ') (hwf : Δ'.wf) :
    (p.subst σ).wfIn Δ' := by
  cases p with
  | term t => exact Term.subst_wfIn hp hσ hdom hsymbols hwf
  | unpred p t =>
    exact ⟨UnPred.wfIn_mono hp.1 hsymbols hwf, Term.subst_wfIn hp.2 hσ hdom hsymbols hwf⟩
  | binpred p t₁ t₂ =>
    exact ⟨BinPred.wfIn_mono hp.1 hsymbols hwf, Term.subst_wfIn hp.2.1 hσ hdom hsymbols hwf,
      Term.subst_wfIn hp.2.2 hσ hdom hsymbols hwf⟩

private theorem Pattern.List.subst_wfIn {ps : List Pattern} {σ : Subst}
    {dom : List Var} {Δ Δ' : Signature}
    (hps : Pattern.List.wfIn ps Δ) (hσ : σ.wfIn dom Δ') (hdom : Δ.vars ⊆ dom)
    (hsymbols : Δ.SymbolSubset Δ') (hwf : Δ'.wf) :
    Pattern.List.wfIn (ps.map (Pattern.subst σ)) Δ' := by
  intro p hp
  rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
  exact Pattern.subst_wfIn (hps q hq) hσ hdom hsymbols hwf

theorem Formula.subst_wfIn {φ : Formula} {σ : Subst} {Δ Δ' : Signature}
    (hφ : φ.wfIn Δ) (hσ : σ.wfIn Δ.vars Δ')
    (hsymbols : Δ.SymbolSubset Δ')
    (hwfΔ' : Δ'.wf) :
    (φ.subst σ Δ'.allNames).wfIn Δ' := by
  induction φ generalizing σ Δ Δ' with
  | true_ | false_ => trivial
  | eq τ a b =>
    exact ⟨Term.subst_wfIn hφ.1 hσ (fun _ h => h) hsymbols hwfΔ',
      Term.subst_wfIn hφ.2 hσ (fun _ h => h) hsymbols hwfΔ'⟩
  | unpred p t =>
    exact ⟨UnPred.wfIn_mono hφ.1 hsymbols hwfΔ', Term.subst_wfIn hφ.2 hσ (fun _ h => h) hsymbols hwfΔ'⟩
  | binpred p a b =>
    exact ⟨BinPred.wfIn_mono hφ.1 hsymbols hwfΔ',
      Term.subst_wfIn hφ.2.1 hσ (fun _ h => h) hsymbols hwfΔ',
      Term.subst_wfIn hφ.2.2 hσ (fun _ h => h) hsymbols hwfΔ'⟩
  | not φ ih =>
    simpa [Formula.subst, Formula.wfIn] using ih hφ hσ hsymbols hwfΔ'
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ | implies φ ψ ihφ ihψ =>
    simpa [Formula.subst, Formula.wfIn] using
      And.intro (ihφ hφ.1 hσ hsymbols hwfΔ')
        (ihψ hφ.2 hσ hsymbols hwfΔ')
  | forall_ y τ ps φ ih =>
    have hy'_fresh := Fresh.freshName_not_in_avoid Δ'.allNames y
    have hwf' := Signature.wf_declVar (v := ⟨Fresh.freshName Δ'.allNames y, τ⟩) hwfΔ'
    have hσ' := Subst.wfIn_bind_fresh (y := y) (τ := τ) hσ hwfΔ' hy'_fresh
    have hsymbols' := Signature.SymbolSubset.declVar_fresh (y := y) (τ := τ) hsymbols hy'_fresh
    have hbody := ih hφ.2 hσ' hsymbols' hwf'
    rw [Signature.allNames_declVar_of_not_in hy'_fresh] at hbody
    exact ⟨Pattern.List.subst_wfIn hφ.1 hσ' (fun _ h => h) hsymbols' hwf', hbody⟩
  | exists_ y τ φ ih =>
    have hy'_fresh := Fresh.freshName_not_in_avoid Δ'.allNames y
    have hwf' := Signature.wf_declVar (v := ⟨Fresh.freshName Δ'.allNames y, τ⟩) hwfΔ'
    have hbody := ih hφ (Subst.wfIn_bind_fresh hσ hwfΔ' hy'_fresh)
      (Signature.SymbolSubset.declVar_fresh hsymbols hy'_fresh) hwf'
    rw [Signature.allNames_declVar_of_not_in hy'_fresh] at hbody
    exact hbody

private theorem Subst.eval_bind_agreeOn {σ : Subst} {ρ : Env} {τ : Srt} {y y' : String} {v : τ.denote}
    {Δ Δ' : Signature} (hσ : σ.wfIn Δ.vars Δ') (hsymbols : Δ.SymbolSubset Δ')
    (hwfΔ : Δ.wf) (hy'_fresh : y' ∉ Δ'.allNames) :
    Env.agreeOn (Δ.declVar ⟨y, τ⟩)
      ((σ.bind y τ y').eval (ρ.updateConst τ y' v))
      ((σ.eval ρ).updateConst τ y v) := by
  refine .intro ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)
  · intro w hw
    have hw' : w = ⟨y, τ⟩ ∨ w ∈ Δ.vars ∧ w.name ≠ y := by
      simpa using hw
    cases hw' with
    | inl hEq =>
      subst hEq
      simp [Subst.eval, Subst.bind, Env.updateConst, Env.lookupConst, Subst.apply,
        Subst.update, Subst.remove, Term.eval]
    | inr hrest =>
      change Term.eval (ρ.updateConst τ y' v) ((σ.bind y τ y').apply w.sort w.name) =
        (((σ.eval ρ).updateConst τ y v).lookupConst w.sort w.name)
      rw [Subst.bind, Subst.apply_update_ne (Or.inl hrest.2), Subst.apply_remove_ne hrest.2,
        Env.lookupConst_updateConst_ne' (Or.inl hrest.2)]
      simpa [Subst.eval, Env.updateConst, Env.lookupConst] using
        (Term.eval_update_fresh (ρ := ρ) (τ' := w.sort) (x := y') (τ := τ)
          (v := v) (Δ := Δ') (hwf := hσ.1 w hrest.1) hy'_fresh)
  · intro c hc
    have hc' : c ∈ Δ.consts ∧ c.name ≠ y := by
      simpa using hc
    have hc_not_var : ⟨c.name, c.sort⟩ ∉ Δ.vars :=
      Signature.wf_no_var_of_const hwfΔ hc'.1
    have hc_not_fresh : c.name ≠ y' := by
      intro hEq
      apply hy'_fresh
      rw [← hEq]
      exact Signature.mem_allNames_of_const (hsymbols.consts c hc'.1)
    change Term.eval (ρ.updateConst τ y' v) ((σ.bind y τ y').apply c.sort c.name) =
      (((σ.eval ρ).updateConst τ y v).lookupConst c.sort c.name)
    rw [Subst.bind, Subst.apply_update_ne (Or.inl hc'.2), Subst.apply_remove_ne hc'.2,
      Env.lookupConst_updateConst_ne' (Or.inl hc'.2), Subst.eval_lookup]
    rw [hσ.2 ⟨c.name, c.sort⟩ hc_not_var]
    simpa [Term.eval, Env.lookupConst] using
      (Env.lookupConst_updateConst_ne' (ρ := ρ) (τ := τ) (τ' := c.sort) (x := y')
        (y := c.name) (v := v) (Or.inl hc_not_fresh))

theorem Formula.eval_subst {σ : Subst} {ρ : Env} {φ : Formula} {Δ Δ' : Signature}
    (hφ : φ.wfIn Δ) (hσ : σ.wfIn Δ.vars Δ') (hsymbols : Δ.SymbolSubset Δ')
    (hwfΔ : Δ.wf) (hwfΔ' : Δ'.wf) :
    (φ.subst σ Δ'.allNames).eval ρ ↔ φ.eval (σ.eval ρ) := by
  induction φ generalizing σ Δ Δ' ρ with
  | true_ | false_ => simp [Formula.subst, Formula.eval]
  | eq τ a b =>
    simp [Formula.subst, Formula.eval, Term.eval_subst hφ.1 hσ hwfΔ', Term.eval_subst hφ.2 hσ hwfΔ']
  | unpred p t =>
    simp [Formula.subst, Formula.eval, Term.eval_subst hφ.2 hσ hwfΔ']
    cases p <;> simp [Subst.eval]
  | binpred p a b =>
    simp [Formula.subst, Formula.eval, Term.eval_subst hφ.2.1 hσ hwfΔ',
      Term.eval_subst hφ.2.2 hσ hwfΔ']
    cases p <;> simp [Subst.eval]
  | not φ ih =>
    simp [Formula.subst, Formula.eval, ih hφ hσ hsymbols hwfΔ hwfΔ']
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ | implies φ ψ ihφ ihψ =>
    simp [Formula.subst, Formula.eval, ihφ hφ.1 hσ hsymbols hwfΔ hwfΔ',
      ihψ hφ.2 hσ hsymbols hwfΔ hwfΔ']
  | forall_ y τ ps φ ih =>
    have hy'_fresh := Fresh.freshName_not_in_avoid Δ'.allNames y
    refine forall_congr' fun v => ?_
    have hbody := ih (ρ := ρ.updateConst τ (Fresh.freshName Δ'.allNames y) v) hφ.2 (Subst.wfIn_bind_fresh hσ hwfΔ' hy'_fresh)
      (Signature.SymbolSubset.declVar_fresh hsymbols hy'_fresh)
      (Signature.wf_declVar hwfΔ) (Signature.wf_declVar hwfΔ')
    rw [Signature.allNames_declVar_of_not_in hy'_fresh] at hbody
    exact hbody.trans (Formula.eval_agreeOn hφ.2 (Subst.eval_bind_agreeOn hσ hsymbols hwfΔ hy'_fresh))
  | exists_ y τ φ ih =>
    have hy'_fresh := Fresh.freshName_not_in_avoid Δ'.allNames y
    refine exists_congr fun v => ?_
    have hbody := ih (ρ := ρ.updateConst τ (Fresh.freshName Δ'.allNames y) v) hφ (Subst.wfIn_bind_fresh hσ hwfΔ' hy'_fresh)
      (Signature.SymbolSubset.declVar_fresh hsymbols hy'_fresh)
      (Signature.wf_declVar hwfΔ) (Signature.wf_declVar hwfΔ')
    rw [Signature.allNames_declVar_of_not_in hy'_fresh] at hbody
    exact hbody.trans (Formula.eval_agreeOn hφ (Subst.eval_bind_agreeOn hσ hsymbols hwfΔ hy'_fresh))
