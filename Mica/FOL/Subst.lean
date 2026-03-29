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

def Subst.wfIn (σ : Subst) (Δ Δ' : Signature) : Prop :=
  ∀ v ∈ Δ.vars, (σ.apply v.sort v.name).wfIn Δ'

theorem Subst.wfIn_mono {σ : Subst} {Δ Δ' Δ'' : Signature} (hσ : σ.wfIn Δ Δ') (hsub : Δ'.Subset Δ'') :
    σ.wfIn Δ Δ'' :=
  fun v hv => Term.wfIn_mono _ (hσ v hv) hsub

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

theorem Subst.wfIn_update {σ : Subst} {τ : Srt} {x : String} {t : Term τ} {Δ Δ' : Signature}
    (hσ : σ.wfIn Δ Δ') (ht : t.wfIn Δ') :
    (σ.update τ x t).wfIn (Δ.addVar ⟨x, τ⟩) Δ' := fun v hv => by
  cases hv with
  | head => simp [Subst.apply_update_same, ht]
  | tail _ hmem =>
    by_cases hname : v.name = x <;> by_cases hty : v.sort = τ
    · cases v; simp only at hname hty; subst hname hty
      simp only [Subst.apply_update_same, ht]
    · simp only [Subst.apply_update_ne (Or.inr hty), hσ v hmem]
    · simp only [Subst.apply_update_ne (Or.inl hname), hσ v hmem]
    · simp only [Subst.apply_update_ne (Or.inl hname), hσ v hmem]

theorem Subst.id_wfIn {Δ : Signature} : Subst.id.wfIn Δ Δ := fun v hv w hw => by
  simp only [Subst.id, Subst.apply, Term.freeVars, List.mem_singleton] at hw
  subst hw; exact hv

theorem Subst.single_wfIn {τ : Srt} {x : String} {t : Term τ} {Δ : Signature} (ht : t.wfIn Δ) :
    (Subst.single τ x t).wfIn (Δ.addVar ⟨x, τ⟩) Δ := by
  unfold Subst.single
  exact Subst.wfIn_update Subst.id_wfIn ht

def Subst.agreeOn (σ σ' : Subst) (Δ : Signature) : Prop :=
  ∀ v ∈ Δ.vars, σ.apply v.sort v.name = σ'.apply v.sort v.name

theorem Term.subst_agreeOn {t : Term τ} {σ σ' : Subst} {Δ : Signature} :
    t.wfIn Δ → σ.agreeOn σ' Δ → t.subst σ = t.subst σ' := by
  intro hwf hagree
  induction t with
  | var τ x =>
    simp [Term.subst]
    exact hagree ⟨x, τ⟩ (hwf ⟨x, τ⟩ (by simp [Term.freeVars]))
  | const _ => rfl
  | unop op a iha =>
    simp [Term.subst, iha (fun v hv => hwf v (by simp [Term.freeVars]; exact hv))]
  | binop op a b iha ihb =>
    simp [Term.subst, iha (fun v hv => hwf v (by simp [Term.freeVars]; left; exact hv)),
                       ihb (fun v hv => hwf v (by simp [Term.freeVars]; right; exact hv))]
  | ite c t e ihc iht ihe =>
    simp [Term.subst,
          ihc (fun v hv => hwf v (by simp [Term.freeVars]; left; exact hv)),
          iht (fun v hv => hwf v (by simp [Term.freeVars]; right; left; exact hv)),
          ihe (fun v hv => hwf v (by simp [Term.freeVars]; right; right; exact hv))]

theorem Term.subst_wfIn {t : Term τ} {σ : Subst} {Δ Δ' : Signature} :
    t.wfIn Δ → σ.wfIn Δ Δ' → (t.subst σ).wfIn Δ' := by
  intro hwf hσ
  induction t with
  | var τ x =>
    simp [Term.subst]
    exact hσ ⟨x, τ⟩ (hwf ⟨x, τ⟩ (by simp [Term.freeVars]))
  | const _  => simp [Term.subst, Term.wfIn, Term.freeVars]
  | unop op a iha =>
    intro v hv
    simp [Term.subst, Term.freeVars] at hv
    exact iha (fun v hv => hwf v (by simp [Term.freeVars]; exact hv)) v hv
  | binop op a b iha ihb =>
    intro v hv
    simp [Term.subst, Term.freeVars] at hv
    cases hv with
    | inl h => exact iha (fun v hv => hwf v (by simp [Term.freeVars]; left; exact hv)) v h
    | inr h => exact ihb (fun v hv => hwf v (by simp [Term.freeVars]; right; exact hv)) v h
  | ite c t e ihc iht ihe =>
    intro v hv
    simp [Term.subst, Term.freeVars] at hv
    cases hv with
    | inl h => exact ihc (fun v hv => hwf v (by simp [Term.freeVars]; left; exact hv)) v h
    | inr hv =>
      cases hv with
      | inl h => exact iht (fun v hv => hwf v (by simp [Term.freeVars]; right; left; exact hv)) v h
      | inr h => exact ihe (fun v hv => hwf v (by simp [Term.freeVars]; right; right; exact hv)) v h

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

theorem Term.wfIn_of_subst_wfIn {t : Term τ} {σ : Subst} {Δ Δ' : Signature} :
    (t.subst σ).wfIn Δ' →
    (∀ (x : String) (τ' : Srt), (σ.apply τ' x).wfIn Δ' → ⟨x, τ'⟩ ∈ Δ.vars) →
    t.wfIn Δ := by
  intro hsubst himpl v hv
  apply himpl
  intro w hw
  have hsub : (σ.apply v.sort v.name).freeVars ⊆ (t.subst σ).freeVars :=
    Term.apply_freeVars_subset_subst_freeVars hv
  exact hsubst w (hsub hw)

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
  | const _ => simp [Term.subst, Term.eval]
  | unop op a iha => simp [Term.subst, Term.eval, iha]
  | binop op a b iha ihb => simp [Term.subst, Term.eval, iha, ihb]
  | ite c t e ihc iht ihe => simp [Term.subst, Term.eval, ihc, iht, ihe]

def freshName (avoid : List Var) (base : String) : String :=
  fresh (addPrimes base) (avoid.map Var.name)

theorem freshName_not_in_avoid (avoid : List Var) (base : String) (τ : Srt) :
    ⟨freshName avoid base, τ⟩ ∉ avoid := by
  intro hmem
  have hfresh := fresh_not_mem (addPrimes base) (avoid.map Var.name) (addPrimes_injective base)
  apply hfresh; simp; exact ⟨⟨freshName avoid base, τ⟩, hmem, rfl⟩

def Formula.subst (σ : Subst) (free : List Var) : Formula → Formula
  | .true_  => .true_
  | .false_ => .false_
  | .eq τ a b      => .eq τ (a.subst σ) (b.subst σ)
  | .unpred p v    => .unpred p (v.subst σ)
  | .binpred p a b => .binpred p (a.subst σ) (b.subst σ)
  | .not φ         => .not (φ.subst σ free)
  | .and φ ψ       => .and (φ.subst σ free) (ψ.subst σ free)
  | .or φ ψ        => .or (φ.subst σ free) (ψ.subst σ free)
  | .implies φ ψ   => .implies (φ.subst σ free) (ψ.subst σ free)
  | .forall_ y τ φ =>
    let y' := freshName free y
    .forall_ y' τ (φ.subst (σ.update τ y (.var τ y')) (⟨y', τ⟩ :: free))
  | .exists_ y τ φ =>
    let y' := freshName free y
    .exists_ y' τ (φ.subst (σ.update τ y (.var τ y')) (⟨y', τ⟩ :: free))

theorem Subst.eval_update_agreeOn {σ : Subst} {ρ : Env} {τ : Srt} {x name' : String} {v : τ.denote}
    {Δ Δ' : Signature} (hσ : σ.wfIn Δ Δ') (hfresh : ⟨name', τ⟩ ∉ Δ'.vars) :
    Env.agreeOn (Δ.addVar ⟨x, τ⟩)
      ((σ.update τ x (.var τ name')).eval (ρ.update τ name' v))
      ((σ.eval ρ).update τ x v) := by
  constructor
  · intro w hw
    by_cases heq : w = ⟨x, τ⟩
    · subst heq; simp [Subst.eval, Env.lookup, Subst.apply, Subst.update, Term.eval, Env.update]
    · have hmem : w ∈ Δ.vars := by
        cases hw with
        | head => contradiction
        | tail _ h => exact h
      have hne : ¬(w.sort = τ ∧ w.name = x) := by
        intro h; obtain ⟨rfl, rfl⟩ := h; cases w; contradiction
      simp only [Subst.eval, Env.lookup, Subst.apply, Subst.update, Env.update, hne, ↓reduceDIte]
      exact Term.eval_update_fresh (fun hfv => hfresh (hσ w hmem _ hfv))
  · exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem Formula.eval_subst {σ : Subst} {ρ : Env} {φ : Formula} {Δ Δ' : Signature}
    (hφ : φ.wfIn Δ) (hσ : σ.wfIn Δ Δ') :
    (φ.subst σ Δ'.vars).eval ρ ↔ φ.eval (σ.eval ρ) := by
  induction φ generalizing σ ρ Δ Δ' with
  | true_ | false_ => rfl
  | eq _ _ _ | binpred _ _ _ | unpred _ _ => simp only [Formula.subst, Formula.eval, Term.eval_subst]
  | not φ ih => simp only [Formula.subst, Formula.eval]; exact not_congr (ih hφ hσ)
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ | implies φ ψ ihφ ihψ =>
    simp only [Formula.subst, Formula.eval]
    have hφl : φ.wfIn Δ := fun v hv => hφ v (by simp [Formula.freeVars]; left; exact hv)
    have hψr : ψ.wfIn Δ := fun v hv => hφ v (by simp [Formula.freeVars]; right; exact hv)
    first | exact and_congr (ihφ hφl hσ) (ihψ hψr hσ)
          | exact or_congr (ihφ hφl hσ) (ihψ hψr hσ)
          | exact imp_congr (ihφ hφl hσ) (ihψ hψr hσ)
  | forall_ x τ φ ih | exists_ x τ φ ih =>
    simp only [Formula.subst, Formula.eval]
    have hwfφ := Formula.wfIn_body_of_wfIn_quant hφ
    let y' := freshName Δ'.vars x
    have hfresh := freshName_not_in_avoid Δ'.vars x τ
    have hσ_mono : σ.wfIn Δ (Δ'.addVar ⟨y', τ⟩) :=
      Subst.wfIn_mono hσ (Signature.Subset.subset_addVar Δ' ⟨y', τ⟩)
    have hwfσ' : (σ.update τ x (.var τ y')).wfIn (Δ.addVar ⟨x, τ⟩) (Δ'.addVar ⟨y', τ⟩) :=
      Subst.wfIn_update hσ_mono (by intro v hv; simp [Term.freeVars] at hv; subst hv; exact List.Mem.head _)
    first
    | constructor <;> intro h v
      · exact (Formula.eval_env_agree hwfφ (Subst.eval_update_agreeOn hσ hfresh)).mp
          ((ih hwfφ hwfσ').mp (h v))
      · exact (ih hwfφ hwfσ').mpr
          ((Formula.eval_env_agree hwfφ (Subst.eval_update_agreeOn hσ hfresh)).mpr (h v))
    | constructor
      · intro ⟨v, hv⟩
        exact ⟨v, (Formula.eval_env_agree hwfφ (Subst.eval_update_agreeOn hσ hfresh)).mp
          ((ih hwfφ hwfσ').mp hv)⟩
      · intro ⟨v, hv⟩
        exact ⟨v, (ih hwfφ hwfσ').mpr
          ((Formula.eval_env_agree hwfφ (Subst.eval_update_agreeOn hσ hfresh)).mpr hv)⟩

theorem Formula.eval_subst_single {φ : Formula} {τ : Srt} {x : String} {t : Term τ} {ρ : Env}
    {Δ : Signature} (hφ : φ.wfIn (Δ.addVar ⟨x, τ⟩)) (ht : t.wfIn Δ) :
    (φ.subst (Subst.single τ x t) Δ.vars).eval ρ ↔ φ.eval (ρ.update τ x (t.eval ρ)) := by
  have hσ : (Subst.single τ x t).wfIn (Δ.addVar ⟨x, τ⟩) Δ := by
    unfold Subst.single
    apply Subst.wfIn_update
    · exact Subst.wfIn_mono Subst.id_wfIn (Signature.Subset.refl Δ)
    · exact ht
  rw [Formula.eval_subst hφ hσ, Subst.eval_single]

theorem Formula.subst_wfIn {φ : Formula} {σ : Subst} {Δ Δ' : Signature} :
    φ.wfIn Δ → σ.wfIn Δ Δ' → (φ.subst σ Δ'.vars).wfIn Δ' := by
  intro hwf hσ
  induction φ generalizing Δ Δ' σ with
  | true_ | false_ => intro v hv; cases hv
  | eq τ a b | binpred _ a b =>
    intro v hv
    simp [Formula.subst, Formula.freeVars, List.mem_append] at hv
    cases hv with
    | inl ha =>
      exact Term.subst_wfIn (fun u hu => hwf u (by simp [Formula.freeVars]; left; exact hu)) hσ v ha
    | inr hb =>
      exact Term.subst_wfIn (fun u hu => hwf u (by simp [Formula.freeVars]; right; exact hu)) hσ v hb
  | unpred _ v =>
    intro u hu
    simp [Formula.subst, Formula.freeVars] at hu
    exact Term.subst_wfIn (fun w hw => hwf w (by simp [Formula.freeVars]; exact hw)) hσ u hu
  | not φ ih =>
    simp [Formula.subst]
    exact ih hwf hσ
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ | implies φ ψ ihφ ihψ =>
    intro v hv
    simp [Formula.subst, Formula.freeVars, List.mem_append] at hv
    cases hv with
    | inl ha => exact ihφ (fun u hu => hwf u (by simp [Formula.freeVars]; left; exact hu)) hσ v ha
    | inr hb => exact ihψ (fun u hu => hwf u (by simp [Formula.freeVars]; right; exact hu)) hσ v hb
  | forall_ y τ φ ih | exists_ y τ φ ih =>
    intro v hv
    simp [Formula.subst, Formula.freeVars, List.mem_filter] at hv
    obtain ⟨hv_in, hv_ne⟩ := hv
    let y'_name := freshName Δ'.vars y
    -- Apply IH with extended context and updated substitution
    have hwf' : φ.wfIn (Δ.addVar ⟨y, τ⟩) := Formula.wfIn_body_of_wfIn_quant hwf
    have hσ_mono : σ.wfIn Δ (Δ'.addVar ⟨y'_name, τ⟩) :=
      Subst.wfIn_mono hσ (Signature.Subset.subset_addVar Δ' ⟨y'_name, τ⟩)
    have hσ' : (σ.update τ y (.var τ y'_name)).wfIn (Δ.addVar ⟨y, τ⟩) (Δ'.addVar ⟨y'_name, τ⟩) :=
      Subst.wfIn_update hσ_mono (by intro v hv; simp [Term.freeVars] at hv; subst hv; exact List.Mem.head _)
    have := ih (σ := σ.update τ y (.var τ y'_name)) hwf' hσ' v hv_in
    cases this with
    | head => contradiction
    | tail _ h => exact h
