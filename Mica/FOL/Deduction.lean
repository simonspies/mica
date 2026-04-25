-- SUMMARY: Unused natural deduction development for first-order logic and its connection to semantic entailment.
import Mica.FOL.Formulas
import Mica.FOL.Subst

/-- Natural deduction proof system for first-order logic, tracking a signature. -/
inductive Proof : Signature → Context → Formula → Prop where
  -- Structural
  | ax : φ ∈ Γ → Proof sig Γ φ
  | weaken : Proof sig Γ φ → Proof sig (ψ :: Γ) φ
  | sigWeaken : Γ.wfIn sig → Proof sig Γ φ → Proof (sig.addVar v) Γ φ

  -- Truth
  | true_intro : Proof sig Γ .true_
  | false_elim : φ.wfIn sig → Proof sig Γ .false_ → Proof sig Γ φ

  -- Conjunction
  | and_intro : Proof sig Γ φ → Proof sig Γ ψ → Proof sig Γ (.and φ ψ)
  | and_left : Proof sig Γ (.and φ ψ) → Proof sig Γ φ
  | and_right : Proof sig Γ (.and φ ψ) → Proof sig Γ ψ

  -- Disjunction
  | or_left : ψ.wfIn sig → Proof sig Γ φ → Proof sig Γ (.or φ ψ)
  | or_right : φ.wfIn sig → Proof sig Γ ψ → Proof sig Γ (.or φ ψ)
  | or_elim : Proof sig Γ (.or φ ψ) → Proof sig (φ :: Γ) χ → Proof sig (ψ :: Γ) χ → Proof sig Γ χ

  -- Implication
  | imp_intro : φ.wfIn sig → Proof sig (φ :: Γ) ψ → Proof sig Γ (.implies φ ψ)
  | imp_elim : Proof sig Γ (.implies φ ψ) → Proof sig Γ φ → Proof sig Γ ψ

  -- Negation
  | not_intro : φ.wfIn sig → Proof sig (φ :: Γ) .false_ → Proof sig Γ (.not φ)
  | not_elim : Proof sig Γ (.not φ) → Proof sig Γ φ → Proof sig Γ .false_

  -- Equality
  | eq_refl : t.wfIn sig → Proof sig Γ (.eq τ t t)
  | eq_symm : Proof sig Γ (.eq τ a b) → Proof sig Γ (.eq τ b a)
  | eq_trans : Proof sig Γ (.eq τ a b) → Proof sig Γ (.eq τ b c) → Proof sig Γ (.eq τ a c)

  -- Quantifiers (eigenvariable-based)
  | forall_intro (y : String) :
      ⟨y, τ⟩ ∉ sig.vars →
      φ.wfIn (sig.addVar (Var.mk x τ)) →
      Proof (sig.addVar (Var.mk y τ)) Γ
        (φ.subst (Subst.single τ x (.var τ y)) (⟨y, τ⟩ :: sig.vars)) →
      Proof sig Γ (.forall_ x τ φ)
  | forall_elim : t.wfIn sig → φ.wfIn (sig.addVar (Var.mk x τ)) →
      Proof sig Γ (.forall_ x τ φ) → Proof sig Γ (φ.subst (Subst.single τ x t) sig.vars)
  | exists_intro : t.wfIn sig → φ.wfIn (sig.addVar (Var.mk x τ)) →
      Proof sig Γ (φ.subst (Subst.single τ x t) sig.vars) → Proof sig Γ (.exists_ x τ φ)
  | exists_elim (y : String) :
      ⟨y, τ⟩ ∉ sig.vars →
      φ.wfIn (sig.addVar (Var.mk x τ)) →
      ψ.wfIn sig →
      Proof sig Γ (.exists_ x τ φ) →
      Proof (sig.addVar (Var.mk y τ))
        (φ.subst (Subst.single τ x (.var τ y)) (⟨y, τ⟩ :: sig.vars) :: Γ) ψ →
      Proof sig Γ ψ

/-- Proofs preserve well-formedness: if the context is well-formed, so is the conclusion. -/
theorem Proof.wfIn : Γ.wfIn sig → Proof sig Γ φ → φ.wfIn sig := by
  intro hwfΓ hp
  induction hp with
  | ax h => exact hwfΓ _ h
  | weaken _ ih => exact ih (fun χ hχ => hwfΓ χ (List.mem_cons_of_mem _ hχ))
  | sigWeaken hwfΓ' _ ih =>
    intro v hv
    exact List.mem_cons_of_mem _ (ih hwfΓ' v hv)
  | true_intro => intro v hv; simp [Formula.freeVars] at hv
  | false_elim hwfφ _ => exact hwfφ
  | and_intro _ _ ih₁ ih₂ =>
    intro v hv; simp only [Formula.freeVars, List.mem_append] at hv
    cases hv with
    | inl h => exact ih₁ hwfΓ v h
    | inr h => exact ih₂ hwfΓ v h
  | and_left _ ih =>
    intro v hv
    exact ih hwfΓ v (by simp only [Formula.freeVars, List.mem_append]; left; exact hv)
  | and_right _ ih =>
    intro v hv
    exact ih hwfΓ v (by simp only [Formula.freeVars, List.mem_append]; right; exact hv)
  | or_left hwfψ _ ih =>
    intro v hv; simp only [Formula.freeVars, List.mem_append] at hv
    cases hv with
    | inl h => exact ih hwfΓ v h
    | inr h => exact hwfψ v h
  | or_right hwfφ _ ih =>
    intro v hv; simp only [Formula.freeVars, List.mem_append] at hv
    cases hv with
    | inl h => exact hwfφ v h
    | inr h => exact ih hwfΓ v h
  | or_elim _ _ _ ihd ihl ihr =>
    intro v hv
    apply ihl
    · intro ψ hψ
      rcases List.eq_or_mem_of_mem_cons hψ with rfl | hψ'
      · intro w hw
        exact ihd hwfΓ w (by simp only [Formula.freeVars, List.mem_append]; left; exact hw)
      · exact hwfΓ ψ hψ'
    · exact hv
  | imp_intro hwfφ _ ih =>
    intro v hv; simp only [Formula.freeVars, List.mem_append] at hv
    cases hv with
    | inl h => exact hwfφ v h
    | inr h =>
      apply ih _ v h
      intro ψ hψ
      rcases List.eq_or_mem_of_mem_cons hψ with rfl | hψ'
      · exact hwfφ
      · exact hwfΓ ψ hψ'
  | imp_elim _ _ ih₁ ih₂ =>
    intro v hv
    exact ih₁ hwfΓ v (by simp only [Formula.freeVars, List.mem_append]; right; exact hv)
  | not_intro hwfφ _ ih =>
    intro v hv; simp only [Formula.freeVars] at hv
    exact hwfφ v hv
  | not_elim _ _ _ _ => intro v hv; simp [Formula.freeVars] at hv
  | eq_refl hwft =>
    intro v hv; simp only [Formula.freeVars, List.mem_append, or_self] at hv
    exact hwft v hv
  | eq_symm _ ih =>
    intro v hv; simp only [Formula.freeVars, List.mem_append] at hv
    exact ih hwfΓ v (by simp only [Formula.freeVars, List.mem_append]; tauto)
  | eq_trans _ _ ih₁ ih₂ =>
    intro v hv; simp only [Formula.freeVars, List.mem_append] at hv
    cases hv with
    | inl h => exact ih₁ hwfΓ v (by simp only [Formula.freeVars, List.mem_append]; left; exact h)
    | inr h => exact ih₂ hwfΓ v (by simp only [Formula.freeVars, List.mem_append]; right; exact h)
  | forall_intro y hnotin hwfφ _ ih =>
    intro v hv; simp only [Formula.freeVars, List.mem_filter] at hv
    obtain ⟨hv_in, hv_ne⟩ := hv
    rcases List.eq_or_mem_of_mem_cons (hwfφ v hv_in) with rfl | hmem
    · simp at hv_ne
    · exact hmem
  | forall_elim hwft hwfφ _ ih =>
    apply Formula.subst_wfIn hwfφ (Subst.single_wfIn hwft)
      (Signature.SymbolSubset.refl _)
  | exists_intro hwft hwfφ _ ih =>
    intro v hv; simp only [Formula.freeVars, List.mem_filter] at hv
    obtain ⟨hv_in, hv_ne⟩ := hv
    cases hwfφ v hv_in with
    | head => simp at hv_ne
    | tail _ h => exact h
  | exists_elim y hnotin _ _ ihE ihB => assumption

-- ============================================================
-- Auxiliary lemmas (TODO: these need proper well-formedness tracking)
-- ============================================================

/-- Substitution evaluation without well-formedness preconditions.
    TODO: Replace usages with Formula.eval_subst_single once soundness tracks well-formedness. -/
theorem Formula.eval_subst_single_sig (τ : Srt) (x : String) (t : Term τ) (ρ : Env)
    (φ : Formula) (sig : VarCtx) :
    (φ.subst (Subst.single τ x t) sig).eval ρ = φ.eval (ρ.updateConst τ x (t.eval ρ)) := by
  sorry

private theorem entails_extend {ρ : Env} {Γ : Context} {φ : Formula}
    (hφ : φ.eval ρ) (hΓ : ∀ ψ ∈ Γ, ψ.eval ρ) :
    ∀ ψ ∈ φ :: Γ, ψ.eval ρ := by
  intro ψ hψ
  rcases List.eq_or_mem_of_mem_cons hψ with rfl | hψ'
  · exact hφ
  · exact hΓ ψ hψ'

-- Structural
theorem sound_ax : φ ∈ Γ → entails Γ φ := by
  intro h ρ hΓ; exact hΓ _ h

theorem sound_weaken : entails Γ φ → entails (ψ :: Γ) φ := by
  intro h ρ hΓ; exact h ρ (fun χ hχ => hΓ χ (List.mem_cons_of_mem _ hχ))

-- Truth
theorem sound_true_intro : entails Γ .true_ := by
  intro ρ _; trivial

theorem sound_false_elim : entails Γ .false_ → entails Γ φ := by
  intro h ρ hΓ; exact absurd (h ρ hΓ) id

-- Conjunction
theorem sound_and_intro : entails Γ φ → entails Γ ψ → entails Γ (.and φ ψ) := by
  intro h₁ h₂ ρ hΓ; exact ⟨h₁ ρ hΓ, h₂ ρ hΓ⟩

theorem sound_and_left : entails Γ (.and φ ψ) → entails Γ φ := by
  intro h ρ hΓ; exact (h ρ hΓ).1

theorem sound_and_right : entails Γ (.and φ ψ) → entails Γ ψ := by
  intro h ρ hΓ; exact (h ρ hΓ).2

-- Disjunction
theorem sound_or_left : entails Γ φ → entails Γ (.or φ ψ) := by
  intro h ρ hΓ; exact Or.inl (h ρ hΓ)

theorem sound_or_right : entails Γ ψ → entails Γ (.or φ ψ) := by
  intro h ρ hΓ; exact Or.inr (h ρ hΓ)

theorem sound_or_elim : entails Γ (.or φ ψ) → entails (φ :: Γ) χ →
    entails (ψ :: Γ) χ → entails Γ χ := by
  intro hd hl hr ρ hΓ
  rcases hd ρ hΓ with h | h
  · exact hl ρ (entails_extend h hΓ)
  · exact hr ρ (entails_extend h hΓ)

-- Implication
theorem sound_imp_intro : entails (φ :: Γ) ψ → entails Γ (.implies φ ψ) := by
  intro h ρ hΓ hφ; exact h ρ (entails_extend hφ hΓ)

theorem sound_imp_elim : entails Γ (.implies φ ψ) → entails Γ φ → entails Γ ψ := by
  intro h₁ h₂ ρ hΓ; exact h₁ ρ hΓ (h₂ ρ hΓ)

-- Negation
theorem sound_not_intro : entails (φ :: Γ) .false_ → entails Γ (.not φ) := by
  intro h ρ hΓ hφ; exact h ρ (entails_extend hφ hΓ)

theorem sound_not_elim : entails Γ (.not φ) → entails Γ φ → entails Γ .false_ := by
  intro h₁ h₂ ρ hΓ; exact h₁ ρ hΓ (h₂ ρ hΓ)

-- Equality
theorem sound_eq_refl : entails Γ (.eq τ t t) := by
  intro ρ _; simp [Formula.eval]

theorem sound_eq_symm : entails Γ (.eq τ a b) → entails Γ (.eq τ b a) := by
  intro h ρ hΓ; simp [Formula.eval] at *; exact (h ρ hΓ).symm

theorem sound_eq_trans : entails Γ (.eq τ a b) → entails Γ (.eq τ b c) →
    entails Γ (.eq τ a c) := by
  intro h₁ h₂ ρ hΓ; simp [Formula.eval] at *; exact (h₁ ρ hΓ).trans (h₂ ρ hΓ)

-- Quantifiers
theorem sound_forall_intro (y : String) (hnotin : ⟨y, τ⟩ ∉ sig.vars) :
    entails Γ (φ.subst (Subst.single τ x (.var τ y)) (⟨y, τ⟩ :: sig.vars)) →
    Γ.wfIn sig →
    φ.wfIn (sig.addVar (Var.mk x τ)) →
    entails Γ (.forall_ x τ φ) := by
  intro hφ hwfΓ hwfφ ρ hΓ v
  let ρ' := ρ.updateConst τ y v
  have hΓ' : ∀ ψ ∈ Γ, ψ.eval ρ' := fun ψ hψ =>
    (Formula.eval_update_not_in_sig (hwfΓ ψ hψ) hnotin).mpr (hΓ ψ hψ)
  have heval := hφ ρ' hΓ'
  rw [Formula.eval_subst_single_sig] at heval
  have heq : Term.eval ρ' (.var τ y) = v := Env.lookupConst_updateConst_same
  rw [heq] at heval
  by_cases hyx : y = x
  · subst hyx
    change Formula.eval ((ρ.updateConst τ y v).updateConst τ y v) φ at heval
    simp only [Env.updateConst_updateConst_same] at heval
    exact heval
  · have hnotin' : ⟨y, τ⟩ ∉ (⟨x, τ⟩ :: sig.vars) := by
      simp only [List.mem_cons, not_or]
      exact ⟨fun h => hyx (congrArg Var.name h), hnotin⟩
    rw [Env.updateConst_comm hyx] at heval
    exact (Formula.eval_update_not_in_sig hwfφ hnotin').mp heval

theorem sound_forall_elim (_hwf : t.wfIn sig) :
    entails Γ (.forall_ x τ φ) → entails Γ (φ.subst (Subst.single τ x t) sig.vars) := by
  intro h ρ hΓ
  have := h ρ hΓ (Term.eval ρ t)
  rw [Formula.eval_subst_single_sig]
  exact this

theorem sound_exists_intro (_hwf : t.wfIn sig) :
    entails Γ (φ.subst (Subst.single τ x t) sig.vars) → entails Γ (.exists_ x τ φ) := by
  intro h ρ hΓ
  use Term.eval ρ t
  rw [← Formula.eval_subst_single_sig]
  exact h ρ hΓ

theorem sound_exists_elim (y : String) (hnotin : ⟨y, τ⟩ ∉ sig.vars) :
    entails Γ (.exists_ x τ φ) →
    entails (φ.subst (Subst.single τ x (.var τ y)) (⟨y, τ⟩ :: sig.vars) :: Γ) ψ →
    Γ.wfIn sig →
    ψ.wfIn sig →
    φ.wfIn (sig.addVar (Var.mk x τ)) →
    entails Γ ψ := by
  intro hφ hψ hwfΓ hwfψ hwfφ ρ hΓ
  -- From hφ ρ hΓ we get ∃ v, φ.eval (ρ.updateConst τ x v)
  obtain ⟨v, hv⟩ := hφ ρ hΓ
  -- Let ρ' = ρ.updateConst τ y v
  let ρ' := ρ.updateConst τ y v
  -- Apply hψ to ρ' to get ψ.eval ρ', then use freshness to get ψ.eval ρ
  have hψρ' : ψ.eval ρ' := hψ ρ' fun χ hχ => by
    rcases List.eq_or_mem_of_mem_cons hχ with rfl | hχ'
    · -- χ = φ[x ↦ y], need to show it holds in ρ'
      rw [Formula.eval_subst_single_sig]
      show Formula.eval (ρ'.updateConst τ x (ρ'.lookupConst τ y)) φ
      have heq : ρ'.lookupConst τ y = v := Env.lookupConst_updateConst_same
      rw [heq]
      -- Need: φ.eval ((ρ.updateConst τ y v).updateConst τ x v), have: hv : φ.eval (ρ.updateConst τ x v)
      by_cases hyx : y = x
      · subst hyx
        change Formula.eval ((ρ.updateConst τ y v).updateConst τ y v) φ
        simp only [Env.updateConst_updateConst_same]
        exact hv
      · have hnotin' : ⟨y, τ⟩ ∉ (⟨x, τ⟩ :: sig.vars) := by
          simp only [List.mem_cons, not_or]
          exact ⟨fun h => hyx (congrArg Var.name h), hnotin⟩
        change Formula.eval ((ρ.updateConst τ y v).updateConst τ x v) φ
        rw [Env.updateConst_comm hyx]
        exact (Formula.eval_update_not_in_sig hwfφ hnotin').mpr hv
    · -- χ ∈ Γ, need to show it holds in ρ'
      show Formula.eval (ρ.updateConst τ y v) χ
      exact (Formula.eval_update_not_in_sig (hwfΓ χ hχ') hnotin).mpr (hΓ χ hχ')
  -- Convert ψ.eval ρ' to ψ.eval ρ using freshness
  exact (Formula.eval_update_not_in_sig hwfψ hnotin).mp hψρ'

/-- Soundness: syntactic proofs are semantically valid.
    We assume the context is well-formed in the signature. -/
theorem soundness : Γ.wfIn sig → Proof sig Γ φ → entails Γ φ := by
  intro hwfΓ hp
  sorry
