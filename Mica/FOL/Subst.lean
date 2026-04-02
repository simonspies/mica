import Mica.FOL.Terms
import Mica.FOL.Formulas
import Mica.Base.Fresh

def Subst := (τ : Srt) → String → Term τ

def Subst.id : Subst := fun τ x => .var τ x

def Subst.apply (σ : Subst) (τ : Srt) (x : String) : Term τ := σ τ x

def Subst.update (σ : Subst) (τ : Srt) (x : String) (s : Term τ) : Subst := fun τ' y =>
  if h : τ' = τ ∧ y = x then h.1 ▸ s else σ τ' y

def Subst.single (τ : Srt) (x : String) (s : Term τ) : Subst :=
  Subst.id.update τ x s

def Term.subst (σ : Subst) : Term τ → Term τ
  | .var τ y   => σ.apply τ y
  | .const c   => .const c
  | .unop op a => .unop op (a.subst σ)
  | .binop op a b => .binop op (a.subst σ) (b.subst σ)
  | .ite c t e => .ite (c.subst σ) (t.subst σ) (e.subst σ)

def Subst.wfIn (σ : Subst) (dom : VarCtx) (Δ : Signature) : Prop :=
  ∀ v ∈ dom, (σ.apply v.sort v.name).wfIn Δ

theorem Subst.wfIn_mono {σ : Subst} {dom : VarCtx} {Δ Δ' : Signature}
    (hσ : σ.wfIn dom Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) :
    σ.wfIn dom Δ' :=
  fun v hv => Term.wfIn_mono _ (hσ v hv) hsub hwf

theorem Subst.wfIn_of_subset_dom {σ : Subst} {dom dom' : VarCtx} {Δ : Signature}
    (hσ : σ.wfIn dom Δ) (hsub : dom' ⊆ dom) : σ.wfIn dom' Δ :=
  fun v hv => hσ v (hsub hv)

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

theorem Subst.wfIn_update {σ : Subst} {dom : VarCtx} {τ : Srt} {x : String} {t : Term τ} {Δ : Signature}
    (hσ : σ.wfIn dom Δ) (ht : t.wfIn Δ) :
    (σ.update τ x t).wfIn (⟨x, τ⟩ :: dom) Δ :=
  fun v hv => by
    cases hv with
    | head => simp [Subst.apply_update_same, ht]
    | tail _ hmem =>
      by_cases hname : v.name = x <;> by_cases hty : v.sort = τ
      · cases v; simp only at hname hty; subst hname hty
        simp only [Subst.apply_update_same, ht]
      · simp only [Subst.apply_update_ne (Or.inr hty), hσ v hmem]
      · simp only [Subst.apply_update_ne (Or.inl hname), hσ v hmem]
      · simp only [Subst.apply_update_ne (Or.inl hname), hσ v hmem]

theorem Subst.id_wfIn {dom : VarCtx} {Δ : Signature} (hsub : dom ⊆ Δ.vars) (hwf : Δ.wf) :
    Subst.id.wfIn dom Δ :=
  fun v hv => by
    refine ⟨hsub hv, ?_⟩
    intro τ' hconst
    exact Signature.wf_no_const_of_var hwf (hsub hv) hconst

theorem Subst.single_wfIn {τ : Srt} {x : String} {t : Term τ} {Δ : Signature} (ht : t.wfIn Δ) :
    (Subst.single τ x t).wfIn [⟨x, τ⟩] Δ := by
  unfold Subst.single
  exact Subst.wfIn_update (fun _ h => absurd h (by simp)) ht

theorem Term.subst_wfIn {t : Term τ} {σ : Subst} {dom : VarCtx} {Δ Δ' : Signature}
    (ht : t.wfIn Δ) (hσ : σ.wfIn dom Δ') (hdom : Δ.vars ⊆ dom)
    (hsymbols : Δ.SymbolSubset Δ')
    (hwf : Δ'.wf) :
    (t.subst σ).wfIn Δ' := by
  induction t generalizing Δ Δ' σ with
  | var τ x => simp only [Term.subst]; exact hσ ⟨x, τ⟩ (hdom ht.1)
  | const c =>
    simp only [Term.subst, Term.wfIn]
    cases c with
    | uninterpreted name τ =>
      refine ⟨hsymbols.consts _ ht.1, ?_⟩
      intro τ' hvar
      exact Signature.wf_no_var_of_const hwf (hsymbols.consts _ ht.1) hvar
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
  { ρ with vars := fun τ x => Term.eval ρ (σ.apply τ x) }

theorem Subst.eval_lookup (σ : Subst) (ρ : Env) (τ : Srt) (x : String) :
    (σ.eval ρ).lookup τ x = Term.eval ρ (σ.apply τ x) := by
  simp [Subst.eval, Env.lookup]

theorem Subst.eval_single {τ : Srt} {x : String} {t : Term τ} {ρ : Env} :
    (Subst.single τ x t).eval ρ = ρ.update τ x (t.eval ρ) := by
  apply Env.ext
  · funext τ' y
    simp only [Subst.eval, Env.update, Subst.apply, Subst.single, Subst.update, Subst.id]
    split
    · next h => obtain ⟨rfl, rfl⟩ := h; simp
    · next h => simp [Term.eval, Env.lookup]
  all_goals rfl

theorem Term.eval_subst {σ : Subst} {ρ : Env} {t : Term τ} :
    Term.eval ρ (t.subst σ) = Term.eval (σ.eval ρ) t := by
  induction t with
  | var τ y => simp [Term.subst, Term.eval, Subst.eval_lookup]
  | const c => simp only [Term.subst, Term.eval]; cases c <;> rfl
  | unop op a iha => simp only [Term.subst, Term.eval, iha]; cases op <;> rfl
  | binop op a b iha ihb => simp only [Term.subst, Term.eval, iha, ihb]; cases op <;> rfl
  | ite c t e ihc iht ihe => simp [Term.subst, Term.eval, ihc, iht, ihe]

def freshName (avoid : List String) (base : String) : String :=
  fresh (addPrimes base) avoid

theorem freshName_not_in_avoid (avoid : List String) (base : String) :
    freshName avoid base ∉ avoid := by
  exact fresh_not_mem (addPrimes base) avoid (addPrimes_injective base)

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
    .forall_ y' τ (Formula.subst (σ.update τ y (.var τ y')) (y' :: avoid) φ)
  | .exists_ y τ φ =>
    let y' := freshName avoid y
    .exists_ y' τ (Formula.subst (σ.update τ y (.var τ y')) (y' :: avoid) φ)

theorem Subst.eval_update_agreeOn {σ : Subst} {ρ : Env} {τ : Srt} {x name' : String} {v : τ.denote}
    {dom : VarCtx} {Δ : Signature} (hσ : σ.wfIn dom Δ) (hfresh : name' ∉ Δ.allNames) :
    Env.agreeOn (Signature.ofVars (⟨x, τ⟩ :: dom))
      ((σ.update τ x (.var τ name')).eval (ρ.update τ name' v))
      ((σ.eval ρ).update τ x v) := by
  constructor
  · intro w hw
    cases hw with
    | head =>
      simp [Subst.eval_lookup, Subst.apply_update_same, Term.eval, Env.lookup_update_same]
    | tail _ hw =>
      by_cases hname : w.name = x <;> by_cases hsort : w.sort = τ
      · cases w
        simp only at hname hsort
        subst hname hsort
        simp [Subst.eval_lookup, Subst.apply_update_same, Term.eval, Env.lookup_update_same]
      · rw [Subst.eval_lookup, Subst.apply_update_ne (Or.inr hsort), Env.lookup_update_ne (Or.inr hsort),
          Subst.eval_lookup]
        have hnotin : ⟨name', τ⟩ ∉ Δ.vars := by
          intro hmem
          exact hfresh (Signature.mem_allNames_of_var hmem)
        exact Term.eval_update_not_in_sig (ρ := ρ) (τ' := w.sort) (x := name') (τ := τ)
          (v := v) (Δ := Δ) (hwf := hσ w hw) hnotin
      · rw [Subst.eval_lookup, Subst.apply_update_ne (Or.inl hname), Env.lookup_update_ne (Or.inl hname),
          Subst.eval_lookup]
        have hnotin : ⟨name', τ⟩ ∉ Δ.vars := by
          intro hmem
          exact hfresh (Signature.mem_allNames_of_var hmem)
        exact Term.eval_update_not_in_sig (ρ := ρ) (τ' := w.sort) (x := name') (τ := τ)
          (v := v) (Δ := Δ) (hwf := hσ w hw) hnotin
      · rw [Subst.eval_lookup, Subst.apply_update_ne (Or.inl hname), Env.lookup_update_ne (Or.inl hname),
          Subst.eval_lookup]
        have hnotin : ⟨name', τ⟩ ∉ Δ.vars := by
          intro hmem
          exact hfresh (Signature.mem_allNames_of_var hmem)
        exact Term.eval_update_not_in_sig (ρ := ρ) (τ' := w.sort) (x := name') (τ := τ)
          (v := v) (Δ := Δ) (hwf := hσ w hw) hnotin
  · constructor
    · intro c hc
      cases hc
    · constructor
      · intro u hu
        cases hu
      · intro b hb
        cases hb

theorem Formula.eval_subst {σ : Subst} {ρ : Env} {φ : Formula} {Δ Δ' : Signature}
    (hφ : φ.wfIn Δ) (hσ : σ.wfIn Δ.vars Δ') (hwfΔ' : Δ'.wf) :
    (φ.subst σ Δ'.allNames).eval ρ ↔ φ.eval (σ.eval ρ) := by
  induction φ generalizing σ Δ Δ' ρ with
  | true_ | false_ => simp [Formula.subst, Formula.eval]
  | eq τ a b =>
    simp [Formula.subst, Formula.eval, Term.eval_subst]
  | unpred p t =>
    simp [Formula.subst, Formula.eval, Term.eval_subst]
  | binpred p a b =>
    simp [Formula.subst, Formula.eval, Term.eval_subst]
  | not φ ih =>
    simp [Formula.subst, Formula.eval, ih hφ hσ hwfΔ']
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ | implies φ ψ ihφ ihψ =>
    simp [Formula.subst, Formula.eval, ihφ hφ.1 hσ hwfΔ', ihψ hφ.2 hσ hwfΔ']
  | forall_ y τ φ ih =>
    simp only [Formula.subst, Formula.eval]
    let y' := freshName Δ'.allNames y
    have hy'_fresh : y' ∉ Δ'.allNames := freshName_not_in_avoid Δ'.allNames y
    have hremove : Δ'.remove y' = Δ' := Signature.remove_eq_of_not_in hy'_fresh
    have hwf_body : φ.wfIn ((Δ.remove y).addVar ⟨y, τ⟩) := hφ
    have hwf_target : ((Δ'.remove y').addVar ⟨y', τ⟩).wf := Signature.wf_remove_addVar hwfΔ'
    have hσ_ext : σ.wfIn Δ.vars ((Δ'.remove y').addVar ⟨y', τ⟩) := by
      have hσ_add : σ.wfIn Δ.vars (Δ'.addVar ⟨y', τ⟩) :=
        Subst.wfIn_mono hσ (Signature.Subset.subset_addVar _ _) (Signature.wf_addVar hwfΔ' hy'_fresh)
      simpa [hremove] using hσ_add
    have hvarwf : (Term.var τ y').wfIn ((Δ'.remove y').addVar ⟨y', τ⟩) := by
      refine ⟨List.Mem.head _, ?_⟩
      intro τ'' hc
      exact Signature.wf_no_const_of_var hwf_target (List.Mem.head _) hc
    have hσ' :
        (σ.update τ y (Term.var τ y')).wfIn ((Δ.remove y).addVar ⟨y, τ⟩).vars ((Δ'.remove y').addVar ⟨y', τ⟩) := by
      apply Subst.wfIn_of_subset_dom (Subst.wfIn_update hσ_ext hvarwf)
      simpa [Signature.addVar] using
        (Signature.Subset.mono_vars ((Signature.remove_subset Δ y).addVar ⟨y, τ⟩))
    have hagree (v : τ.denote) : Env.agreeOn ((Δ.remove y).addVar ⟨y, τ⟩)
        ((σ.update τ y (Term.var τ y')).eval (ρ.update τ y' v))
        ((σ.eval ρ).update τ y v) := by
      constructor
      · intro w hw
        exact (Subst.eval_update_agreeOn (ρ := ρ) (τ := τ) (x := y) (name' := y')
          (v := v) (dom := Δ.vars) (Δ := Δ') hσ hy'_fresh).1 w
          ((Signature.Subset.mono_vars ((Signature.remove_subset Δ y).addVar ⟨y, τ⟩)) hw)
      · exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    constructor <;> intro h v
    · have h1 := (ih (σ := σ.update τ y (Term.var τ y')) (Δ := (Δ.remove y).addVar ⟨y, τ⟩)
          (Δ' := (Δ'.remove y').addVar ⟨y', τ⟩) (ρ := ρ.update τ y' v) hwf_body hσ' hwf_target).mp
          (by simpa [y', Signature.allNames_remove_addVar_of_not_in hy'_fresh] using h v)
      exact (Formula.eval_env_agree hwf_body (hagree v)).mp h1
    · have h1 := (Formula.eval_env_agree hwf_body (hagree v)).mpr (h v)
      exact (by
        simpa [y', Signature.allNames_remove_addVar_of_not_in hy'_fresh] using
          (ih (σ := σ.update τ y (Term.var τ y')) (Δ := (Δ.remove y).addVar ⟨y, τ⟩)
            (Δ' := (Δ'.remove y').addVar ⟨y', τ⟩) (ρ := ρ.update τ y' v) hwf_body hσ' hwf_target).mpr h1)
  | exists_ y τ φ ih =>
    simp only [Formula.subst, Formula.eval]
    let y' := freshName Δ'.allNames y
    have hy'_fresh : y' ∉ Δ'.allNames := freshName_not_in_avoid Δ'.allNames y
    have hremove : Δ'.remove y' = Δ' := Signature.remove_eq_of_not_in hy'_fresh
    have hwf_body : φ.wfIn ((Δ.remove y).addVar ⟨y, τ⟩) := hφ
    have hwf_target : ((Δ'.remove y').addVar ⟨y', τ⟩).wf := Signature.wf_remove_addVar hwfΔ'
    have hσ_ext : σ.wfIn Δ.vars ((Δ'.remove y').addVar ⟨y', τ⟩) := by
      have hσ_add : σ.wfIn Δ.vars (Δ'.addVar ⟨y', τ⟩) :=
        Subst.wfIn_mono hσ (Signature.Subset.subset_addVar _ _) (Signature.wf_addVar hwfΔ' hy'_fresh)
      simpa [hremove] using hσ_add
    have hvarwf : (Term.var τ y').wfIn ((Δ'.remove y').addVar ⟨y', τ⟩) := by
      refine ⟨List.Mem.head _, ?_⟩
      intro τ'' hc
      exact Signature.wf_no_const_of_var hwf_target (List.Mem.head _) hc
    have hσ' :
        (σ.update τ y (Term.var τ y')).wfIn ((Δ.remove y).addVar ⟨y, τ⟩).vars ((Δ'.remove y').addVar ⟨y', τ⟩) := by
      apply Subst.wfIn_of_subset_dom (Subst.wfIn_update hσ_ext hvarwf)
      simpa [Signature.addVar] using
        (Signature.Subset.mono_vars ((Signature.remove_subset Δ y).addVar ⟨y, τ⟩))
    have hagree (v : τ.denote) : Env.agreeOn ((Δ.remove y).addVar ⟨y, τ⟩)
        ((σ.update τ y (Term.var τ y')).eval (ρ.update τ y' v))
        ((σ.eval ρ).update τ y v) := by
      constructor
      · intro w hw
        exact (Subst.eval_update_agreeOn (ρ := ρ) (τ := τ) (x := y) (name' := y')
          (v := v) (dom := Δ.vars) (Δ := Δ') hσ hy'_fresh).1 w
          ((Signature.Subset.mono_vars ((Signature.remove_subset Δ y).addVar ⟨y, τ⟩)) hw)
      · exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨v, ?_⟩
      have h1 := (ih (σ := σ.update τ y (Term.var τ y')) (Δ := (Δ.remove y).addVar ⟨y, τ⟩)
        (Δ' := (Δ'.remove y').addVar ⟨y', τ⟩) (ρ := ρ.update τ y' v) hwf_body hσ' hwf_target).mp
        (by simpa [y', Signature.allNames_remove_addVar_of_not_in hy'_fresh] using hv)
      exact (Formula.eval_env_agree hwf_body (hagree v)).mp h1
    · rintro ⟨v, hv⟩
      refine ⟨v, ?_⟩
      have h1 := (Formula.eval_env_agree hwf_body (hagree v)).mpr hv
      exact (by
        simpa [y', Signature.allNames_remove_addVar_of_not_in hy'_fresh] using
          (ih (σ := σ.update τ y (Term.var τ y')) (Δ := (Δ.remove y).addVar ⟨y, τ⟩)
            (Δ' := (Δ'.remove y').addVar ⟨y', τ⟩) (ρ := ρ.update τ y' v) hwf_body hσ' hwf_target).mpr h1)

theorem Formula.eval_subst_single {φ : Formula} {τ : Srt} {x : String} {t : Term τ} {ρ : Env}
    {Δ : Signature} (hφ : φ.wfIn ((Δ.remove x).addVar ⟨x, τ⟩)) (ht : t.wfIn Δ) (hwfΔ : Δ.wf) :
    (φ.subst (Subst.single τ x t) Δ.allNames).eval ρ ↔ φ.eval (ρ.update τ x (t.eval ρ)) := by
  have hid : Subst.id.wfIn Δ.vars Δ := by
    exact Subst.id_wfIn (by intro v hv; exact hv) hwfΔ
  have hsingle : (Subst.single τ x t).wfIn ((Δ.remove x).addVar ⟨x, τ⟩).vars Δ := by
    unfold Subst.single
    apply Subst.wfIn_of_subset_dom (Subst.wfIn_update hid ht)
    simpa [Signature.addVar] using
      (Signature.Subset.mono_vars ((Signature.remove_subset Δ x).addVar ⟨x, τ⟩))
  rw [Formula.eval_subst hφ hsingle hwfΔ, Subst.eval_single]

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
      refine ⟨List.Mem.head _, ?_⟩
      intro τ'' hc
      exact Signature.wf_no_const_of_var hwf_target (List.Mem.head _) hc
    have hσ' :
        (σ.update τ y (Term.var τ y')).wfIn ((Δ.remove y).addVar ⟨y, τ⟩).vars ((Δ'.remove y').addVar ⟨y', τ⟩) := by
      apply Subst.wfIn_of_subset_dom (Subst.wfIn_update hσ_ext hvarwf)
      simpa [Signature.addVar] using
        (Signature.Subset.mono_vars ((Signature.remove_subset Δ y).addVar ⟨y, τ⟩))
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
