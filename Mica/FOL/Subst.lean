import Mica.FOL.Terms
import Mica.FOL.Formulas
import Mica.Base.Fresh

structure Subst where
  intSubst     : String → Term .int
  boolSubst    : String → Term .bool
  valSubst     : String → Term .value
  vallistSubst : String → Term .vallist

def Subst.id : Subst where
  intSubst     := .var .int
  boolSubst    := .var .bool
  valSubst     := .var .value
  vallistSubst := .var .vallist

def Subst.apply (σ : Subst) (τ : Srt) (x : String) : Term τ :=
  match τ with
  | .int     => σ.intSubst x
  | .bool    => σ.boolSubst x
  | .value   => σ.valSubst x
  | .vallist => σ.vallistSubst x

def Subst.update (σ : Subst) (τ : Srt) (x : String) (s : Term τ) : Subst :=
  match τ with
  | .int     => { σ with intSubst     := fun y => if y == x then s else σ.intSubst y }
  | .bool    => { σ with boolSubst    := fun y => if y == x then s else σ.boolSubst y }
  | .value   => { σ with valSubst     := fun y => if y == x then s else σ.valSubst y }
  | .vallist => { σ with vallistSubst := fun y => if y == x then s else σ.vallistSubst y }

def Subst.single (τ : Srt) (x : String) (s : Term τ) : Subst :=
  Subst.id.update τ x s

def Term.subst (σ : Subst) : Term τ → Term τ
  | .var τ y   => σ.apply τ y
  | .const c   => .const c
  | .unop op a => .unop op (a.subst σ)
  | .binop op a b => .binop op (a.subst σ) (b.subst σ)
  | .ite c t e => .ite (c.subst σ) (t.subst σ) (e.subst σ)

def Subst.wfIn (σ : Subst) (Δ Δ' : VarCtx) : Prop :=
  ∀ v ∈ Δ, (σ.apply v.sort v.name).wfIn Δ'

theorem Subst.wfIn_mono {σ : Subst} {Δ Δ' Δ'' : VarCtx} (hσ : σ.wfIn Δ Δ') (hsub : Δ' ⊆ Δ'') :
    σ.wfIn Δ Δ'' :=
  fun v hv => Term.wfIn_mono _ (hσ v hv) hsub

theorem Subst.apply_update_same {σ : Subst} {τ : Srt} {x : String} {t : Term τ} :
    (σ.update τ x t).apply τ x = t := by
  cases τ <;> simp [Subst.update, Subst.apply]

theorem Subst.apply_update_ne {σ : Subst} {τ τ' : Srt} {x y : String} {t : Term τ}
    (h : y ≠ x ∨ τ' ≠ τ) : (σ.update τ x t).apply τ' y = σ.apply τ' y := by
  cases τ <;> cases τ' <;> simp [Subst.update, Subst.apply]
  all_goals (cases h with | inl h => simp [h] | inr h => exact absurd rfl h)

theorem Subst.wfIn_update {σ : Subst} {τ : Srt} {x : String} {t : Term τ} {Δ Δ' : VarCtx}
    (hσ : σ.wfIn Δ Δ') (ht : t.wfIn Δ') :
    (σ.update τ x t).wfIn (⟨x, τ⟩ :: Δ) Δ' := fun v hv => by
  simp only [List.mem_cons] at hv
  cases hv with
  | inl heq => subst heq; simp only [Subst.apply_update_same, ht]
  | inr hmem =>
    by_cases hname : v.name = x <;> by_cases hty : v.sort = τ
    · cases v; simp only at hname hty; subst hname hty
      simp only [Subst.apply_update_same, ht]
    · simp only [Subst.apply_update_ne (Or.inr hty), hσ v hmem]
    · simp only [Subst.apply_update_ne (Or.inl hname), hσ v hmem]
    · simp only [Subst.apply_update_ne (Or.inl hname), hσ v hmem]

theorem Subst.id_wfIn {Δ : VarCtx} : Subst.id.wfIn Δ Δ := fun v hv w hw => by
  obtain ⟨vname, vty⟩ := v
  cases vty <;> simp only [Subst.id, Subst.apply, Term.freeVars, List.mem_singleton] at hw
  all_goals (subst hw; exact hv)

theorem Subst.single_wfIn {τ : Srt} {x : String} {t : Term τ} {Δ : VarCtx} (ht : t.wfIn Δ) :
    (Subst.single τ x t).wfIn (⟨x, τ⟩ :: Δ) Δ := by
  unfold Subst.single
  exact Subst.wfIn_update Subst.id_wfIn ht

def Subst.agreeOn (σ σ' : Subst) (Δ : VarCtx) : Prop :=
  ∀ v ∈ Δ, σ.apply v.sort v.name = σ'.apply v.sort v.name

theorem Term.subst_agreeOn {t : Term τ} {σ σ' : Subst} {Δ : VarCtx} :
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

theorem Term.subst_wfIn {t : Term τ} {σ : Subst} {Δ Δ' : VarCtx} :
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
  | var τ x => cases τ <;> rfl
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

theorem Term.wfIn_of_subst_wfIn {t : Term τ} {σ : Subst} {Δ Δ' : VarCtx} :
    (t.subst σ).wfIn Δ' →
    (∀ (x : String) (τ' : Srt), (σ.apply τ' x).wfIn Δ' → ⟨x, τ'⟩ ∈ Δ) →
    t.wfIn Δ := by
  intro hsubst himpl v hv
  apply himpl
  intro w hw
  have hsub : (σ.apply v.sort v.name).freeVars ⊆ (t.subst σ).freeVars :=
    Term.apply_freeVars_subset_subst_freeVars hv
  exact hsubst w (hsub hw)

def Subst.eval (σ : Subst) (ρ : Env) : Env := fun τ x =>
  Term.eval ρ (σ.apply τ x)

theorem Subst.eval_lookup (σ : Subst) (ρ : Env) (τ : Srt) (x : String) :
    (σ.eval ρ).lookup τ x = Term.eval ρ (σ.apply τ x) := by
  simp [Subst.eval, Env.lookup]

theorem Subst.eval_single {τ : Srt} {x : String} {t : Term τ} {ρ : Env} :
    (Subst.single τ x t).eval ρ = ρ.update τ x (t.eval ρ) := by
  funext τ' y; simp only [Subst.eval, Env.update, Subst.apply]
  cases τ <;> cases τ' <;> simp [Subst.single, Subst.id, Subst.update, Term.eval, Env.lookup]
  all_goals split <;> simp_all [Term.eval, Env.lookup]

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
    {Δ Δ' : VarCtx} (hσ : σ.wfIn Δ Δ') (hfresh : ⟨name', τ⟩ ∉ Δ') :
    Env.agreeOn (⟨x, τ⟩ :: Δ)
      ((σ.update τ x (.var τ name')).eval (ρ.update τ name' v))
      ((σ.eval ρ).update τ x v) := fun w hw => by
  simp only [List.mem_cons] at hw
  by_cases heq : w = ⟨x, τ⟩
  · subst heq; simp [Subst.eval_lookup, Subst.apply_update_same, Term.eval, Env.lookup_update_same]
  · have hmem : w ∈ Δ := hw.resolve_left heq
    have hne : w.name ≠ x ∨ w.sort ≠ τ := by
      by_contra h; push_neg at h; exact heq (by cases w; simp_all)
    simp only [Subst.eval_lookup, Subst.apply_update_ne hne, Env.lookup_update_ne hne]
    exact Term.eval_update_fresh (fun hfv => hfresh (hσ w hmem _ hfv))

theorem Formula.eval_subst {σ : Subst} {ρ : Env} {φ : Formula} {Δ Δ' : VarCtx}
    (hφ : φ.wfIn Δ) (hσ : σ.wfIn Δ Δ') :
    (φ.subst σ Δ').eval ρ ↔ φ.eval (σ.eval ρ) := by
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
    have hfresh := freshName_not_in_avoid Δ' x τ
    have hwfσ' : (σ.update τ x (.var τ (freshName Δ' x))).wfIn (⟨x, τ⟩ :: Δ) (⟨freshName Δ' x, τ⟩ :: Δ') :=
      Subst.wfIn_update (Subst.wfIn_mono hσ (by grind)) (by simp [Term.wfIn, Term.freeVars])
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
    {Δ : VarCtx} (hφ : φ.wfIn (⟨x, τ⟩ :: Δ)) (ht : t.wfIn Δ) :
    (φ.subst (Subst.single τ x t) Δ).eval ρ ↔ φ.eval (ρ.update τ x (t.eval ρ)) := by
  rw [Formula.eval_subst hφ (Subst.single_wfIn ht), Subst.eval_single]

theorem Formula.subst_wfIn {φ : Formula} {σ : Subst} {Δ Δ' : VarCtx} :
    φ.wfIn Δ → σ.wfIn Δ Δ' → (φ.subst σ Δ').wfIn Δ' := by
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
    set y' := freshName Δ' y
    -- Apply IH with extended context and updated substitution
    have hwf' : φ.wfIn (⟨y, τ⟩ :: Δ) := Formula.wfIn_body_of_wfIn_quant hwf
    have hσ' : (σ.update τ y (.var τ y')).wfIn (⟨y, τ⟩ :: Δ) (⟨y', τ⟩ :: Δ') :=
      Subst.wfIn_update (Subst.wfIn_mono hσ (by intro w hw; right; exact hw)) (by simp [Term.wfIn, Term.freeVars])
    have := ih (σ := σ.update τ y (.var τ y')) hwf' hσ' v hv_in
    cases this with
    | head => exact absurd hv_ne (by simp)
    | tail _ h => exact h
