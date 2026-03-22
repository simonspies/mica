import Mica.FOL.Terms

inductive UnPred : Srt → Type where
  | isInt   : UnPred .value
  | isBool  : UnPred .value
  | isTuple : UnPred .value
  | isInj (tag : Nat) (arity : Nat) : UnPred .value
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

@[simp] def UnPred.eval : UnPred τ → τ.denote → Prop
  | .isInt,   v => match v with | .int _ => True | _ => False
  | .isBool,  v => match v with | .bool _ => True | _ => False
  | .isTuple, v => match v with | .tuple _ => True | _ => False
  | .isInj tag arity, v => match v with | .inj t a _ => t = tag ∧ a = arity | _ => False

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


theorem Formula.eval_update_not_in_sig {φ : Formula} {x : String} {τ : Srt} {v : τ.denote} {ρ : Env}
    {sig : VarCtx} (hwf : φ.wfIn sig) (hnotin : ⟨x, τ⟩ ∉ sig) :
    (φ.eval (ρ.update τ x v) ↔ φ.eval ρ) :=
  Formula.eval_env_agree hwf fun w hw => by
    by_cases heq : w = ⟨x, τ⟩
    · subst heq; exact absurd hw hnotin
    · have hne : w.name ≠ x ∨ w.sort ≠ τ := by
        obtain ⟨wname, wtype⟩ := w
        by_cases h : wname = x <;> by_cases ht : wtype = τ
        · exfalso; apply heq; simp [h, ht]
        · exact Or.inr ht
        · exact Or.inl h
        · exact Or.inl h
      exact Env.lookup_update_ne hne


/-- A predicate with one named bound variable: `λ x -> body`. -/
def Pred α      := String × α

/-- A predicate with zero or more named bound variables: `λ x₁ x₂ … -> body`. -/
def MultiPred α := List String × α
