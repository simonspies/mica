import Mica.FOL.Terms
import Mica.Base.Fresh

inductive UnPred : Srt → Type where
  | isInt   : UnPred .value
  | isBool  : UnPred .value
  | isTuple : UnPred .value
  deriving DecidableEq, Repr

inductive BinPred : Srt → Srt → Type where
  | lt : BinPred .int .int
  | le : BinPred .int .int
  deriving DecidableEq, Repr

inductive Formula where
  | true_ : Formula
  | false_ : Formula
  | eq      : (τ : Srt) → Term τ → Term τ → Formula
  | unpred  : UnPred τ → Term τ → Formula
  | binpred : BinPred τ₁ τ₂ → Term τ₁ → Term τ₂ → Formula
  | not     : Formula → Formula
  | and     : Formula → Formula → Formula
  | or      : Formula → Formula → Formula
  | implies : Formula → Formula → Formula
  | forall_ : String → Srt → Formula → Formula
  | exists_ : String → Srt → Formula → Formula
  deriving DecidableEq

def Formula.freeVars : Formula → List Var
  | .true_ => []
  | .false_ => []
  | .eq _τ a b    => a.freeVars ++ b.freeVars
  | .unpred _ v   => v.freeVars
  | .binpred _ a b => a.freeVars ++ b.freeVars
  | .not φ        => φ.freeVars
  | .and φ ψ      => φ.freeVars ++ ψ.freeVars
  | .or φ ψ       => φ.freeVars ++ ψ.freeVars
  | .implies φ ψ  => φ.freeVars ++ ψ.freeVars
  | .forall_ y τ φ => φ.freeVars.filter (· != ⟨y, τ⟩)
  | .exists_ y τ φ => φ.freeVars.filter (· != ⟨y, τ⟩)

def Formula.wfIn (φ : Formula) (Δ : VarCtx) : Prop :=
  ∀ v ∈ φ.freeVars, v ∈ Δ

def Formula.checkWf (φ : Formula) (Δ : VarCtx) : Except String Unit :=
  match φ.freeVars.find? (· ∉ Δ) with
  | some v => .error s!"variable {repr v.name} : {repr v.sort} not in scope"
  | none => .ok ()

theorem Formula.checkWf_ok {φ : Formula} {Δ : VarCtx} (h : φ.checkWf Δ = .ok ()) : φ.wfIn Δ := by
  simp only [Formula.checkWf] at h
  split at h <;> simp at h
  rename_i heq
  intro v hv
  have := List.find?_eq_none.mp heq v hv
  simp at this
  exact this

theorem Formula.wfIn_freeVars (φ : Formula) : φ.wfIn φ.freeVars :=
  fun _ hv => hv

theorem Formula.wfIn_mono (φ : Formula) (h : φ.wfIn Δ) (hsub : Δ ⊆ Δ') : φ.wfIn Δ' :=
  fun v hv => hsub (h v hv)

theorem Formula.wfIn_body_of_wfIn_quant {φ : Formula} {x : String} {τ : Srt} {Δ : VarCtx}
    (hwf : (∀ v ∈ φ.freeVars.filter (· != ⟨x, τ⟩), v ∈ Δ)) : φ.wfIn (⟨x, τ⟩ :: Δ) := fun w hw => by
  by_cases heq : w = ⟨x, τ⟩
  · simp [heq]
  · right; exact hwf w (List.mem_filter.mpr ⟨hw, by simp [bne_iff_ne, heq]⟩)

abbrev Context := List Formula
abbrev Signature := VarCtx

def Context.wfIn (Γ : Context) (Δ : VarCtx) : Prop :=
  ∀ φ ∈ Γ, φ.wfIn Δ

theorem Context.wfIn_mono (Γ : Context) (h : Γ.wfIn Δ) (hsub : Δ ⊆ Δ') : Γ.wfIn Δ' :=
  fun φ hφ => Formula.wfIn_mono φ (h φ hφ) hsub

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

@[simp] def UnPred.eval : UnPred τ → τ.denote → Prop
  | .isInt,   v => match v with | .int _ => True | _ => False
  | .isBool,  v => match v with | .bool _ => True | _ => False
  | .isTuple, v => match v with | .tuple _ => True | _ => False

@[simp] def BinPred.eval : BinPred τ₁ τ₂ → τ₁.denote → τ₂.denote → Prop
  | .lt, a, b => a < b
  | .le, a, b => a ≤ b

def Formula.eval (ρ : Env) : Formula → Prop
  | .true_         => True
  | .false_        => False
  | .eq _τ a b     => a.eval ρ = b.eval ρ
  | .unpred p v    => p.eval (v.eval ρ)
  | .binpred p a b => p.eval (a.eval ρ) (b.eval ρ)
  | .not φ         => ¬ φ.eval ρ
  | .and φ ψ       => φ.eval ρ ∧ ψ.eval ρ
  | .or φ ψ        => φ.eval ρ ∨ ψ.eval ρ
  | .implies φ ψ   => φ.eval ρ → ψ.eval ρ
  | .forall_ x τ φ => ∀ v : τ.denote, φ.eval (ρ.update τ x v)
  | .exists_ x τ φ => ∃ v : τ.denote, φ.eval (ρ.update τ x v)

def entails (Γ : Context) (φ : Formula) : Prop :=
  ∀ ρ : Env, (∀ ψ ∈ Γ, ψ.eval ρ) → φ.eval ρ

theorem Formula.eval_env_agree {φ : Formula} {ρ ρ' : Env} {Δ : VarCtx} :
    φ.wfIn Δ → Env.agreeOn Δ ρ ρ' → (φ.eval ρ ↔ φ.eval ρ') := by
  intro hwf hagree
  induction φ generalizing Δ ρ ρ' with
  | true_ | false_ => rfl
  | eq τ a b =>
    simp only [Formula.eval]
    have ha : a.wfIn Δ := fun v hv => hwf v (by simp [Formula.freeVars]; left; exact hv)
    have hb : b.wfIn Δ := fun v hv => hwf v (by simp [Formula.freeVars]; right; exact hv)
    rw [Term.eval_env_agree ha hagree, Term.eval_env_agree hb hagree]
  | unpred p v =>
    simp only [Formula.eval]
    have hwf' : v.wfIn Δ := fun u hu => hwf u (by simp [Formula.freeVars]; exact hu)
    rw [Term.eval_env_agree hwf' hagree]
  | binpred p a b =>
    simp only [Formula.eval]
    have ha : a.wfIn Δ := fun v hv => hwf v (by simp [Formula.freeVars]; left; exact hv)
    have hb : b.wfIn Δ := fun v hv => hwf v (by simp [Formula.freeVars]; right; exact hv)
    rw [Term.eval_env_agree ha hagree, Term.eval_env_agree hb hagree]
  | not φ ih =>
    simp only [Formula.eval]; rw [ih hwf hagree]
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ | implies φ ψ ihφ ihψ =>
    simp only [Formula.eval]
    have hφ : φ.wfIn Δ := fun v hv => hwf v (by simp [Formula.freeVars]; left; exact hv)
    have hψ : ψ.wfIn Δ := fun v hv => hwf v (by simp [Formula.freeVars]; right; exact hv)
    rw [ihφ hφ hagree, ihψ hψ hagree]
  | forall_ x τ φ ih =>
    simp only [Formula.eval]
    have hwf' := Formula.wfIn_body_of_wfIn_quant hwf
    constructor <;> intro h v
    · exact (ih hwf' (Env.agreeOn_update hagree)).mp (h v)
    · exact (ih hwf' (Env.agreeOn_update hagree)).mpr (h v)
  | exists_ x τ φ ih =>
    simp only [Formula.eval]
    have hwf' := Formula.wfIn_body_of_wfIn_quant hwf
    constructor
    · intro ⟨v, hv⟩; exact ⟨v, (ih hwf' (Env.agreeOn_update hagree)).mp hv⟩
    · intro ⟨v, hv⟩; exact ⟨v, (ih hwf' (Env.agreeOn_update hagree)).mpr hv⟩

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

theorem Formula.eval_update_not_in_sig {φ : Formula} {x : String} {τ : Srt} {v : τ.denote} {ρ : Env}
    {sig : VarCtx} (hwf : φ.wfIn sig) (hnotin : ⟨x, τ⟩ ∉ sig) :
    (φ.eval (ρ.update τ x v) ↔ φ.eval ρ) :=
  Formula.eval_env_agree hwf (fun w hw => by
    by_cases heq : w = ⟨x, τ⟩
    · subst heq; exact absurd hw hnotin
    · have hne : w.name ≠ x ∨ w.sort ≠ τ := by
        by_contra h; push_neg at h; exact heq (by cases w; simp_all)
      simp [Env.lookup_update_ne hne])

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

/-- A predicate with one named bound variable: `λ x -> body`. -/
def Pred α      := String × α

/-- A predicate with zero or more named bound variables: `λ x₁ x₂ … -> body`. -/
def MultiPred α := List String × α
