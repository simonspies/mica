-- SUMMARY: Capture-avoiding substitution for first-order syntax and its well-formedness conditions.
import Mica.FOL.Terms
import Mica.FOL.Formulas
import Mica.Base.Fresh

def Subst := (τ : Srt) → String → Term τ

def Subst.id : Subst := fun τ x => .var τ x

def Subst.apply (σ : Subst) (τ : Srt) (x : String) : Term τ := σ τ x

def Subst.update (σ : Subst) (τ : Srt) (x : String) (s : Term τ) : Subst := fun τ' y =>
  if h : τ' = τ ∧ y = x then h.1 ▸ s else σ τ' y

def Subst.remove (σ : Subst) (x : String) : Subst := fun τ y =>
  if y = x then .var τ y else σ τ y

def Subst.bind (σ : Subst) (y : String) (τ : Srt) (y' : String) : Subst :=
  (σ.remove y).update τ y (.var τ y')

def Subst.single (τ : Srt) (x : String) (s : Term τ) : Subst :=
  Subst.id.update τ x s

def Term.subst (σ : Subst) : Term τ → Term τ
  | .var τ y   => σ.apply τ y
  | .const c   => .const c
  | .unop op a => .unop op (a.subst σ)
  | .binop op a b => .binop op (a.subst σ) (b.subst σ)
  | .ite c t e => .ite (c.subst σ) (t.subst σ) (e.subst σ)

def Subst.wfIn (σ : Subst) (dom : VarCtx) (Δ : Signature) : Prop :=
  (∀ v ∈ dom, (σ.apply v.sort v.name).wfIn Δ) ∧
  (∀ v, v ∉ dom → σ.apply v.sort v.name = .var v.sort v.name)

theorem Subst.wfIn_mono {σ : Subst} {dom : VarCtx} {Δ Δ' : Signature}
    (hσ : σ.wfIn dom Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) :
    σ.wfIn dom Δ' :=
  ⟨fun v hv => Term.wfIn_mono _ (hσ.1 v hv) hsub hwf, hσ.2⟩

theorem Subst.apply_update_same {σ : Subst} {τ : Srt} {x : String} {t : Term τ} :
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

theorem Subst.apply_remove_same {σ : Subst} {τ : Srt} {x : String} :
    (σ.remove x).apply τ x = .var τ x := by
  simp [Subst.remove, Subst.apply]

theorem Subst.apply_remove_ne {σ : Subst} {τ : Srt} {x y : String}
    (h : y ≠ x) : (σ.remove x).apply τ y = σ.apply τ y := by
  simp [Subst.remove, Subst.apply, h]

theorem Subst.wfIn_update {σ : Subst} {dom : VarCtx} {τ : Srt} {x : String} {t : Term τ} {Δ : Signature}
    (hσ : σ.wfIn dom Δ) (ht : t.wfIn Δ) :
    (σ.update τ x t).wfIn (⟨x, τ⟩ :: dom) Δ :=
  ⟨fun v hv => by
      cases hv with
      | head => simp [Subst.apply_update_same, ht]
      | tail _ hmem =>
        by_cases hname : v.name = x <;> by_cases hty : v.sort = τ
        · cases v; simp only at hname hty; subst hname hty
          simp only [Subst.apply_update_same, ht]
        · simp only [Subst.apply_update_ne (Or.inr hty), hσ.1 v hmem]
        · simp only [Subst.apply_update_ne (Or.inl hname), hσ.1 v hmem]
        · simp only [Subst.apply_update_ne (Or.inl hname), hσ.1 v hmem],
    fun v hv => by
      have hvdom : v ∉ dom := by
        intro hmem
        apply hv
        exact List.mem_cons_of_mem _ hmem
      by_cases hname : v.name = x <;> by_cases hty : v.sort = τ
      · exfalso
        apply hv
        cases v
        simp only at hname hty
        subst hname hty
        exact List.mem_cons_self
      · rw [Subst.apply_update_ne (Or.inr hty)]
        exact hσ.2 v hvdom
      · rw [Subst.apply_update_ne (Or.inl hname)]
        exact hσ.2 v hvdom
      · rw [Subst.apply_update_ne (Or.inl hname)]
        exact hσ.2 v hvdom⟩

theorem Subst.id_wfIn {dom : VarCtx} {Δ : Signature} (hsub : dom ⊆ Δ.vars) (hwf : Δ.wf) :
    Subst.id.wfIn dom Δ :=
  ⟨fun v hv => by
      refine ⟨hsub hv, ?_, ?_⟩
      · intro τ' hconst
        exact Signature.wf_no_const_of_var hwf (hsub hv) hconst
      · intro τ' hv'
        exact Signature.wf_unique_var hwf (hsub hv) hv',
    fun _ _ => rfl⟩

theorem Subst.single_wfIn {τ : Srt} {x : String} {t : Term τ} {Δ : Signature} (ht : t.wfIn Δ) :
    (Subst.single τ x t).wfIn [⟨x, τ⟩] Δ := by
  unfold Subst.single
  exact Subst.wfIn_update ⟨fun _ h => absurd h (by simp), fun _ h => rfl⟩ ht

theorem Subst.wfIn_remove {σ : Subst} {dom : VarCtx} {Δ : Signature} {x : String}
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

theorem Subst.wfIn_bind {σ : Subst} {Δ Δ'' : Signature} {y y' : String} {τ : Srt}
    (hσ : σ.wfIn Δ.vars Δ'') (hvarwf : (Term.var τ y').wfIn Δ'') :
    (σ.bind y τ y').wfIn ((Δ.remove y).addVar ⟨y, τ⟩).vars Δ'' := by
  have hσ_erase : (σ.remove y).wfIn (Δ.remove y).vars Δ'' := by
    simpa [Signature.remove] using
      (Subst.wfIn_remove (σ := σ) (dom := Δ.vars) (Δ := Δ'') (x := y) hσ)
  simpa [Subst.bind, Signature.addVar] using
    (Subst.wfIn_update (σ := σ.remove y) (dom := (Δ.remove y).vars) (x := y) hσ_erase hvarwf)

theorem Term.subst_wfIn {t : Term τ} {σ : Subst} {dom : VarCtx} {Δ Δ' : Signature}
    (ht : t.wfIn Δ) (hσ : σ.wfIn dom Δ') (hdom : Δ.vars ⊆ dom)
    (hsymbols : Δ.SymbolSubset Δ')
    (hwf : Δ'.wf) :
    (t.subst σ).wfIn Δ' := by
  induction t generalizing Δ Δ' σ with
  | var τ x => simp only [Term.subst]; exact hσ.1 ⟨x, τ⟩ (hdom ht.1)
  | const c =>
    simp only [Term.subst, Term.wfIn]
    cases c with
    | uninterpreted name τ =>
      refine ⟨hsymbols.consts _ ht.1, ?_, ?_⟩
      · intro τ' hvar
        exact Signature.wf_no_var_of_const hwf (hsymbols.consts _ ht.1) hvar
      · intro τ' hc'
        exact Signature.wf_unique_const hwf (hsymbols.consts _ ht.1) hc'
    | _ => trivial
  | unop op a iha =>
    simp only [Term.subst, Term.wfIn]
    refine ⟨?_, iha ht.2 hσ hdom hsymbols hwf⟩
    cases op with
    | uninterpreted name _ _ => exact hsymbols.unary _ ht.1
    | _ => trivial
  | binop op a b iha ihb =>
    simp only [Term.subst, Term.wfIn]
    refine ⟨?_, iha ht.2.1 hσ hdom hsymbols hwf,
      ihb ht.2.2 hσ hdom hsymbols hwf⟩
    cases op with
    | uninterpreted name _ _ _ => exact hsymbols.binary _ ht.1
    | _ => trivial
  | ite c t e ihc iht ihe =>
    simp only [Term.subst, Term.wfIn]
    exact ⟨ihc ht.1 hσ hdom hsymbols hwf,
           iht ht.2.1 hσ hdom hsymbols hwf,
           ihe ht.2.2 hσ hdom hsymbols hwf⟩

theorem Term.subst_id {t : Term τ} : t.subst Subst.id = t := by
  induction t with
  | var τ x => rfl
  | const _ => rfl
  | unop op a iha => simp [Term.subst, iha]
  | binop op a b iha ihb => simp [Term.subst, iha, ihb]
  | ite c t e ihc iht ihe => simp [Term.subst, ihc, iht, ihe]

theorem Term.apply_freeVars_subset_subst_freeVars {t : Term τ} {σ : Subst} {v : Var} :
    v ∈ t.freeVars → (σ.apply v.sort v.name).freeVars ⊆ (t.subst σ).freeVars := by
  intro hv
  induction t with
  | var τ' x =>
    simp [Term.freeVars] at hv
    subst hv
    simp [Term.subst]
  | const _  =>
    simp [Term.freeVars] at hv
  | unop op a iha =>
    simp [Term.freeVars] at hv
    simp [Term.subst, Term.freeVars]
    exact iha hv
  | binop op a b iha ihb =>
    simp [Term.freeVars, List.mem_append] at hv
    simp [Term.subst, Term.freeVars, List.subset_def, List.mem_append]
    cases hv with
    | inl ha => intro w hw; left; exact iha ha hw
    | inr hb => intro w hw; right; exact ihb hb hw
  | ite c t e ihc iht ihe =>
    simp [Term.freeVars, List.mem_append] at hv
    simp [Term.subst, Term.freeVars, List.subset_def, List.mem_append]
    cases hv with
    | inl hc => intro w hw; left; exact ihc hc hw
    | inr hv =>
      cases hv with
      | inl ht => intro w hw; right; left; exact iht ht hw
      | inr he => intro w hw; right; right; exact ihe he hw

def Subst.eval (σ : Subst) (ρ : Env) : Env :=
  { ρ with consts := fun τ x => Term.eval ρ (σ.apply τ x) }

theorem Subst.eval_lookup (σ : Subst) (ρ : Env) (τ : Srt) (x : String) :
    (σ.eval ρ).lookupConst τ x = Term.eval ρ (σ.apply τ x) := by
  simp [Subst.eval, Env.lookupConst]

theorem Subst.eval_single {τ : Srt} {x : String} {t : Term τ} {ρ : Env} :
    (Subst.single τ x t).eval ρ = ρ.updateConst τ x (t.eval ρ) := by
  apply Env.ext
  · funext τ' y
    simp [Subst.eval, Env.updateConst, Subst.apply, Subst.single, Subst.update, Subst.id]
    split
    · next h => obtain ⟨rfl, rfl⟩ := h; simp
    · next _ => simp [Term.eval, Env.lookupConst]
  all_goals rfl

theorem Term.eval_subst {σ : Subst} {ρ : Env} {t : Term τ} {Δ Δ' : Signature}
    (ht : t.wfIn Δ) (hσ : σ.wfIn Δ.vars Δ') (hwfΔ' : Δ'.wf) :
    Term.eval ρ (t.subst σ) = Term.eval (σ.eval ρ) t := by
  induction t generalizing Δ Δ' with
  | var τ y =>
    simp [Term.subst, Term.eval, Subst.eval_lookup]
  | const c =>
    simp only [Term.subst, Term.eval]
    cases c with
    | uninterpreted name _ =>
      rename_i τ1
      simp [Const.denote, Subst.eval]
      symm
      have hvar : σ.apply τ1 name = .var τ1 name := hσ.2 ⟨name, τ1⟩ (ht.2.1 τ1)
      rw [hvar]
      simp [Term.eval, Env.lookupConst]
    | _ => rfl
  | unop op a iha =>
    simp only [Term.subst, Term.eval]
    rw [iha ht.2 hσ hwfΔ']
    cases op with
    | uninterpreted name _ _ => rfl
    | _ => rfl
  | binop op a b iha ihb =>
    simp only [Term.subst, Term.eval]
    rw [iha ht.2.1 hσ hwfΔ', ihb ht.2.2 hσ hwfΔ']
    cases op with
    | uninterpreted name _ _ _ => rfl
    | _ => rfl
  | ite c t e ihc iht ihe =>
    simp [Term.subst, Term.eval, ihc ht.1 hσ hwfΔ', iht ht.2.1 hσ hwfΔ', ihe ht.2.2 hσ hwfΔ']

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
  | .forall_ y τ φ =>
    let y' := freshName avoid y
    .forall_ y' τ (Formula.subst (σ.bind y τ y') (y' :: avoid) φ)
  | .exists_ y τ φ =>
    let y' := freshName avoid y
    .exists_ y' τ (Formula.subst (σ.bind y τ y') (y' :: avoid) φ)

theorem Subst.eval_update_agreeOn {σ : Subst} {ρ : Env} {τ : Srt} {x name' : String} {v : τ.denote}
    {dom : VarCtx} {Δ : Signature} (hσ : σ.wfIn dom Δ) (hfresh : name' ∉ Δ.allNames) :
    Env.agreeOn (Signature.ofVars (⟨x, τ⟩ :: dom))
      ((σ.update τ x (.var τ name')).eval (ρ.updateConst τ name' v))
      ((σ.eval ρ).updateConst τ x v) := by
  constructor
  · intro w hw
    cases hw with
    | head =>
      simp [Subst.eval, Env.updateConst, Env.lookupConst, Subst.apply, Subst.update, Term.eval]
    | tail _ hw =>
      by_cases hname : w.name = x <;> by_cases hsort : w.sort = τ
      · cases w
        simp only at hname hsort
        subst hname hsort
        simp [Subst.eval, Env.updateConst, Env.lookupConst, Subst.apply, Subst.update, Term.eval]
      · change
          Term.eval (ρ.updateConst τ name' v) ((σ.update τ x (.var τ name')).apply w.sort w.name) =
            (((σ.eval ρ).updateConst τ x v).lookupConst w.sort w.name)
        rw [Subst.apply_update_ne (Or.inr hsort), Env.lookupConst_updateConst_ne' (Or.inr hsort)]
        simpa [Subst.eval, Env.updateConst, Env.lookupConst] using
          (Term.eval_update_fresh (ρ := ρ) (τ' := w.sort) (x := name') (τ := τ)
            (v := v) (Δ := Δ) (hwf := hσ.1 w hw) hfresh)
      · change
          Term.eval (ρ.updateConst τ name' v) ((σ.update τ x (.var τ name')).apply w.sort w.name) =
            (((σ.eval ρ).updateConst τ x v).lookupConst w.sort w.name)
        rw [Subst.apply_update_ne (Or.inl hname), Env.lookupConst_updateConst_ne' (Or.inl hname)]
        simpa [Subst.eval, Env.updateConst, Env.lookupConst] using
          (Term.eval_update_fresh (ρ := ρ) (τ' := w.sort) (x := name') (τ := τ)
            (v := v) (Δ := Δ) (hwf := hσ.1 w hw) hfresh)
      · change
          Term.eval (ρ.updateConst τ name' v) ((σ.update τ x (.var τ name')).apply w.sort w.name) =
            (((σ.eval ρ).updateConst τ x v).lookupConst w.sort w.name)
        rw [Subst.apply_update_ne (Or.inl hname), Env.lookupConst_updateConst_ne' (Or.inl hname)]
        simpa [Subst.eval, Env.updateConst, Env.lookupConst] using
          (Term.eval_update_fresh (ρ := ρ) (τ' := w.sort) (x := name') (τ := τ)
            (v := v) (Δ := Δ) (hwf := hσ.1 w hw) hfresh)
  · simp [Signature.ofVars]

theorem Subst.eval_bind_agreeOn {σ : Subst} {ρ : Env} {τ : Srt} {y y' : String} {v : τ.denote}
    {Δ Δ' : Signature} (hσ : σ.wfIn Δ.vars Δ') (hsymbols : Δ.SymbolSubset Δ')
    (hwfΔ : Δ.wf) (hy'_fresh : y' ∉ Δ'.allNames) :
    Env.agreeOn ((Δ.remove y).addVar ⟨y, τ⟩)
      ((σ.bind y τ y').eval (ρ.updateConst τ y' v))
      ((σ.eval ρ).updateConst τ y v) := by
  constructor
  · intro w hw
    have hw' : w = ⟨y, τ⟩ ∨ w ∈ Δ.vars ∧ w.name ≠ y := by
      simpa [Signature.addVar] using hw
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
  · constructor
    · intro c hc
      have hc' : c ∈ Δ.consts ∧ c.name ≠ y := by
        simpa [Signature.addVar] using hc
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
    · constructor
      · intro u hu
        rfl
      · intro b hb
        rfl

theorem Formula.eval_subst {σ : Subst} {ρ : Env} {φ : Formula} {Δ Δ' : Signature}
    (hφ : φ.wfIn Δ) (hσ : σ.wfIn Δ.vars Δ') (hsymbols : Δ.SymbolSubset Δ')
    (hwfΔ : Δ.wf) (hwfΔ' : Δ'.wf) :
    (φ.subst σ Δ'.allNames).eval ρ ↔ φ.eval (σ.eval ρ) := by
  induction φ generalizing σ Δ Δ' ρ with
  | true_ | false_ => simp [Formula.subst, Formula.eval]
  | eq τ a b =>
    simp [Formula.subst, Formula.eval, Term.eval_subst hφ.1 hσ hwfΔ', Term.eval_subst hφ.2 hσ hwfΔ']
  | unpred p t =>
    simp [Formula.subst, Formula.eval, Term.eval_subst hφ hσ hwfΔ']
  | binpred p a b =>
    simp [Formula.subst, Formula.eval, Term.eval_subst hφ.1 hσ hwfΔ', Term.eval_subst hφ.2 hσ hwfΔ']
  | not φ ih =>
    simp [Formula.subst, Formula.eval, ih hφ hσ hsymbols hwfΔ hwfΔ']
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ | implies φ ψ ihφ ihψ =>
    simp [Formula.subst, Formula.eval, ihφ hφ.1 hσ hsymbols hwfΔ hwfΔ',
      ihψ hφ.2 hσ hsymbols hwfΔ hwfΔ']
  | forall_ y τ φ ih =>
    simp only [Formula.subst, Formula.eval]
    let y' := freshName Δ'.allNames y
    have hy'_fresh : y' ∉ Δ'.allNames := freshName_not_in_avoid Δ'.allNames y
    have hremove : Δ'.remove y' = Δ' := Signature.remove_eq_of_not_in hy'_fresh
    have hwf_body : φ.wfIn ((Δ.remove y).addVar ⟨y, τ⟩) := hφ
    have hwf_body_sig : ((Δ.remove y).addVar ⟨y, τ⟩).wf := Signature.wf_remove_addVar hwfΔ
    have hwf_target : ((Δ'.remove y').addVar ⟨y', τ⟩).wf := Signature.wf_remove_addVar hwfΔ'
    have hσ_ext : σ.wfIn Δ.vars ((Δ'.remove y').addVar ⟨y', τ⟩) := by
      have hσ_add : σ.wfIn Δ.vars (Δ'.addVar ⟨y', τ⟩) :=
        Subst.wfIn_mono hσ (Signature.Subset.subset_addVar _ _) (Signature.wf_addVar hwfΔ' hy'_fresh)
      simpa [hremove] using hσ_add
    have hvarwf : (Term.var τ y').wfIn ((Δ'.remove y').addVar ⟨y', τ⟩) := by
      refine ⟨List.Mem.head _, ?_, ?_⟩
      · intro τ'' hc
        exact Signature.wf_no_const_of_var hwf_target (List.Mem.head _) hc
      · intro τ'' hv
        exact Signature.wf_unique_var hwf_target (List.Mem.head _) hv
    have hσ' :
        (σ.bind y τ y').wfIn ((Δ.remove y).addVar ⟨y, τ⟩).vars ((Δ'.remove y').addVar ⟨y', τ⟩) :=
      Subst.wfIn_bind (Δ := Δ) (Δ'' := ((Δ'.remove y').addVar ⟨y', τ⟩)) hσ_ext hvarwf
    have hsymbols_body : ((Δ.remove y).addVar ⟨y, τ⟩).SymbolSubset ((Δ'.remove y').addVar ⟨y', τ⟩) := by
      constructor
      · intro c hc
        simpa [hremove, Signature.addVar] using
          (Signature.SymbolSubset.declVar hsymbols ⟨y, τ⟩).consts c
            (by simpa [Signature.declVar, Signature.addVar] using hc)
      · intro u hu
        simpa [hremove, Signature.addVar] using
          (Signature.SymbolSubset.declVar hsymbols ⟨y, τ⟩).unary u
            (by simpa [Signature.declVar, Signature.addVar] using hu)
      · intro b hb
        simpa [hremove, Signature.addVar] using
          (Signature.SymbolSubset.declVar hsymbols ⟨y, τ⟩).binary b
            (by simpa [Signature.declVar, Signature.addVar] using hb)
    have hagree (v : τ.denote) : Env.agreeOn ((Δ.remove y).addVar ⟨y, τ⟩)
        ((σ.bind y τ y').eval (ρ.updateConst τ y' v))
        ((σ.eval ρ).updateConst τ y v) :=
      Subst.eval_bind_agreeOn (ρ := ρ) (Δ := Δ) (Δ' := Δ') hσ hsymbols hwfΔ hy'_fresh
    constructor <;> intro h v
    · have h1 := (ih (σ := σ.bind y τ y') (Δ := (Δ.remove y).addVar ⟨y, τ⟩)
          (Δ' := (Δ'.remove y').addVar ⟨y', τ⟩) (ρ := ρ.updateConst τ y' v) hwf_body hσ'
          hsymbols_body hwf_body_sig hwf_target).mp
          (by simpa [y', Signature.allNames_remove_addVar_of_not_in hy'_fresh] using h v)
      exact (Formula.eval_env_agree hwf_body (hagree v)).mp h1
    · have h1 := (Formula.eval_env_agree hwf_body (hagree v)).mpr (h v)
      exact (by
        simpa [y', Signature.allNames_remove_addVar_of_not_in hy'_fresh] using
          (ih (σ := σ.bind y τ y') (Δ := (Δ.remove y).addVar ⟨y, τ⟩)
            (Δ' := (Δ'.remove y').addVar ⟨y', τ⟩) (ρ := ρ.updateConst τ y' v) hwf_body hσ'
            hsymbols_body hwf_body_sig hwf_target).mpr h1)
  | exists_ y τ φ ih =>
    simp only [Formula.subst, Formula.eval]
    let y' := freshName Δ'.allNames y
    have hy'_fresh : y' ∉ Δ'.allNames := freshName_not_in_avoid Δ'.allNames y
    have hremove : Δ'.remove y' = Δ' := Signature.remove_eq_of_not_in hy'_fresh
    have hwf_body : φ.wfIn ((Δ.remove y).addVar ⟨y, τ⟩) := hφ
    have hwf_body_sig : ((Δ.remove y).addVar ⟨y, τ⟩).wf := Signature.wf_remove_addVar hwfΔ
    have hwf_target : ((Δ'.remove y').addVar ⟨y', τ⟩).wf := Signature.wf_remove_addVar hwfΔ'
    have hσ_ext : σ.wfIn Δ.vars ((Δ'.remove y').addVar ⟨y', τ⟩) := by
      have hσ_add : σ.wfIn Δ.vars (Δ'.addVar ⟨y', τ⟩) :=
        Subst.wfIn_mono hσ (Signature.Subset.subset_addVar _ _) (Signature.wf_addVar hwfΔ' hy'_fresh)
      simpa [hremove] using hσ_add
    have hvarwf : (Term.var τ y').wfIn ((Δ'.remove y').addVar ⟨y', τ⟩) := by
      refine ⟨List.Mem.head _, ?_, ?_⟩
      · intro τ'' hc
        exact Signature.wf_no_const_of_var hwf_target (List.Mem.head _) hc
      · intro τ'' hv
        exact Signature.wf_unique_var hwf_target (List.Mem.head _) hv
    have hσ' :
        (σ.bind y τ y').wfIn ((Δ.remove y).addVar ⟨y, τ⟩).vars ((Δ'.remove y').addVar ⟨y', τ⟩) :=
      Subst.wfIn_bind (Δ := Δ) (Δ'' := ((Δ'.remove y').addVar ⟨y', τ⟩)) hσ_ext hvarwf
    have hsymbols_body : ((Δ.remove y).addVar ⟨y, τ⟩).SymbolSubset ((Δ'.remove y').addVar ⟨y', τ⟩) := by
      constructor
      · intro c hc
        simpa [hremove, Signature.addVar] using
          (Signature.SymbolSubset.declVar hsymbols ⟨y, τ⟩).consts c
            (by simpa [Signature.declVar, Signature.addVar] using hc)
      · intro u hu
        simpa [hremove, Signature.addVar] using
          (Signature.SymbolSubset.declVar hsymbols ⟨y, τ⟩).unary u
            (by simpa [Signature.declVar, Signature.addVar] using hu)
      · intro b hb
        simpa [hremove, Signature.addVar] using
          (Signature.SymbolSubset.declVar hsymbols ⟨y, τ⟩).binary b
            (by simpa [Signature.declVar, Signature.addVar] using hb)
    have hagree (v : τ.denote) : Env.agreeOn ((Δ.remove y).addVar ⟨y, τ⟩)
        ((σ.bind y τ y').eval (ρ.updateConst τ y' v))
        ((σ.eval ρ).updateConst τ y v) :=
      Subst.eval_bind_agreeOn (ρ := ρ) (Δ := Δ) (Δ' := Δ') hσ hsymbols hwfΔ hy'_fresh
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨v, ?_⟩
      have h1 := (ih (σ := σ.bind y τ y') (Δ := (Δ.remove y).addVar ⟨y, τ⟩)
        (Δ' := (Δ'.remove y').addVar ⟨y', τ⟩) (ρ := ρ.updateConst τ y' v) hwf_body hσ'
        hsymbols_body hwf_body_sig hwf_target).mp
        (by simpa [y', Signature.allNames_remove_addVar_of_not_in hy'_fresh] using hv)
      exact (Formula.eval_env_agree hwf_body (hagree v)).mp h1
    · rintro ⟨v, hv⟩
      refine ⟨v, ?_⟩
      have h1 := (Formula.eval_env_agree hwf_body (hagree v)).mpr hv
      exact (by
        simpa [y', Signature.allNames_remove_addVar_of_not_in hy'_fresh] using
          (ih (σ := σ.bind y τ y') (Δ := (Δ.remove y).addVar ⟨y, τ⟩)
            (Δ' := (Δ'.remove y').addVar ⟨y', τ⟩) (ρ := ρ.updateConst τ y' v) hwf_body hσ'
            hsymbols_body hwf_body_sig hwf_target).mpr h1)

theorem Formula.eval_subst_single {φ : Formula} {τ : Srt} {x : String} {t : Term τ} {ρ : Env}
    {Δ : Signature} (hφ : φ.wfIn ((Δ.remove x).addVar ⟨x, τ⟩)) (ht : t.wfIn Δ) (hwfΔ : Δ.wf) :
    (φ.subst (Subst.single τ x t) Δ.allNames).eval ρ ↔ φ.eval (ρ.updateConst τ x (t.eval ρ)) := by
  have hid : Subst.id.wfIn Δ.vars Δ := by
    exact Subst.id_wfIn (by intro v hv; exact hv) hwfΔ
  have hsingle : (Subst.single τ x t).wfIn ((Δ.remove x).addVar ⟨x, τ⟩).vars Δ := by
    unfold Subst.single
    have hbase := Subst.wfIn_update (σ := Subst.id) (dom := Δ.vars) (x := x) hid ht
    refine ⟨?_, ?_⟩
    · intro v hv
      have hv' : v = ⟨x, τ⟩ ∨ v ∈ Δ.vars ∧ v.name ≠ x := by
        simpa [Signature.addVar] using hv
      cases hv' with
      | inl hEq =>
        subst hEq
        exact hbase.1 _ List.mem_cons_self
      | inr hrest =>
        exact hbase.1 _ (List.mem_cons_of_mem _ hrest.1)
    · intro v hv
      by_cases hname : v.name = x <;> by_cases hsort : v.sort = τ
      · exfalso
        apply hv
        cases v
        simp only at hname hsort
        subst hname hsort
        simp [Signature.addVar]
      · rw [Subst.apply_update_ne (σ := Subst.id) (Or.inr hsort)]
        rfl
      · rw [Subst.apply_update_ne (σ := Subst.id) (Or.inl hname)]
        rfl
      · rw [Subst.apply_update_ne (σ := Subst.id) (Or.inl hname)]
        rfl
  have hsymbols : ((Δ.remove x).addVar ⟨x, τ⟩).SymbolSubset Δ := by
    simpa [Signature.declVar] using (Signature.SymbolSubset.declVar (Signature.SymbolSubset.refl Δ) ⟨x, τ⟩)
  have hwfBody : ((Δ.remove x).addVar ⟨x, τ⟩).wf := Signature.wf_remove_addVar hwfΔ
  rw [Formula.eval_subst hφ hsingle hsymbols hwfBody hwfΔ, Subst.eval_single]

theorem Formula.subst_wfIn {φ : Formula} {σ : Subst} {Δ Δ' : Signature}
    (hwf : φ.wfIn Δ) (hσ : σ.wfIn Δ.vars Δ')
    (hsymbols : Δ.SymbolSubset Δ')
    (hwfΔ' : Δ'.wf) :
    (φ.subst σ Δ'.allNames).wfIn Δ' := by
  induction φ generalizing σ Δ Δ' with
  | true_ | false_ => trivial
  | eq τ a b =>
    simp [Formula.subst, Formula.wfIn]
    exact ⟨Term.subst_wfIn hwf.1 hσ (by intro x hx; exact hx) hsymbols hwfΔ',
      Term.subst_wfIn hwf.2 hσ (by intro x hx; exact hx) hsymbols hwfΔ'⟩
  | unpred p t =>
    simp [Formula.subst, Formula.wfIn]
    exact Term.subst_wfIn hwf hσ (by intro x hx; exact hx) hsymbols hwfΔ'
  | binpred p a b =>
    simp [Formula.subst, Formula.wfIn]
    exact ⟨Term.subst_wfIn hwf.1 hσ (by intro x hx; exact hx) hsymbols hwfΔ',
      Term.subst_wfIn hwf.2 hσ (by intro x hx; exact hx) hsymbols hwfΔ'⟩
  | not φ ih =>
    simpa [Formula.subst, Formula.wfIn] using ih hwf hσ hsymbols hwfΔ'
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ | implies φ ψ ihφ ihψ =>
    simpa [Formula.subst, Formula.wfIn] using
      And.intro (ihφ hwf.1 hσ hsymbols hwfΔ')
        (ihψ hwf.2 hσ hsymbols hwfΔ')
  | forall_ y τ φ ih | exists_ y τ φ ih =>
    simp only [Formula.subst, Formula.wfIn]
    let y' := freshName Δ'.allNames y
    have hy'_fresh : y' ∉ Δ'.allNames := freshName_not_in_avoid Δ'.allNames y
    have hremove : Δ'.remove y' = Δ' := Signature.remove_eq_of_not_in hy'_fresh
    have hwf_target : ((Δ'.remove y').addVar ⟨y', τ⟩).wf := Signature.wf_remove_addVar hwfΔ'
    have hσ_ext :
        σ.wfIn Δ.vars ((Δ'.remove y').addVar ⟨y', τ⟩) := by
      have hσ_add : σ.wfIn Δ.vars (Δ'.addVar ⟨y', τ⟩) :=
        Subst.wfIn_mono hσ (Signature.Subset.subset_addVar _ _) (Signature.wf_addVar hwfΔ' hy'_fresh)
      simpa [hremove] using hσ_add
    have hvarwf : (Term.var τ y').wfIn ((Δ'.remove y').addVar ⟨y', τ⟩) := by
      refine ⟨List.Mem.head _, ?_, ?_⟩
      · intro τ'' hc
        exact Signature.wf_no_const_of_var hwf_target (List.Mem.head _) hc
      · intro τ'' hv
        exact Signature.wf_unique_var hwf_target (List.Mem.head _) hv
    have hσ' :
        (σ.bind y τ y').wfIn ((Δ.remove y).addVar ⟨y, τ⟩).vars ((Δ'.remove y').addVar ⟨y', τ⟩) :=
      Subst.wfIn_bind (Δ := Δ) (Δ'' := ((Δ'.remove y').addVar ⟨y', τ⟩)) hσ_ext hvarwf
    have hconsts' : ((Δ.remove y).addVar ⟨y, τ⟩).consts ⊆ ((Δ'.remove y').addVar ⟨y', τ⟩).consts := by
      intro c hc
      rcases Signature.mem_remove_consts.mp hc with ⟨hc, hcy⟩
      refine Signature.mem_remove_consts.mpr ⟨hsymbols.consts _ hc, ?_⟩
      intro hceq
      exact hy'_fresh (hceq ▸ Signature.mem_allNames_of_const (hsymbols.consts _ hc))
    have hunary' : ((Δ.remove y).addVar ⟨y, τ⟩).unary ⊆ ((Δ'.remove y').addVar ⟨y', τ⟩).unary := by
      intro u hu
      rcases Signature.mem_remove_unary.mp hu with ⟨hu, huy⟩
      refine Signature.mem_remove_unary.mpr ⟨hsymbols.unary _ hu, ?_⟩
      intro hueq
      exact hy'_fresh (hueq ▸ Signature.mem_allNames_of_unary (hsymbols.unary _ hu))
    have hbinary' : ((Δ.remove y).addVar ⟨y, τ⟩).binary ⊆ ((Δ'.remove y').addVar ⟨y', τ⟩).binary := by
      intro b hb
      rcases Signature.mem_remove_binary.mp hb with ⟨hb, hby⟩
      refine Signature.mem_remove_binary.mpr ⟨hsymbols.binary _ hb, ?_⟩
      intro hbeq
      exact hy'_fresh (hbeq ▸ Signature.mem_allNames_of_binary (hsymbols.binary _ hb))
    have hsymbols' : ((Δ.remove y).addVar ⟨y, τ⟩).SymbolSubset ((Δ'.remove y').addVar ⟨y', τ⟩) :=
      ⟨hconsts', hunary', hbinary'⟩
    exact (by
      simpa [y', Signature.allNames_remove_addVar_of_not_in hy'_fresh] using
        ih hwf hσ' hsymbols' hwf_target)
