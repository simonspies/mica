import Mica.TinyML.Expr

-- ---------------------------------------------------------------------------
-- Sorts
-- ---------------------------------------------------------------------------

inductive Srt where
  | int
  | bool
  | value
  | vallist
  deriving DecidableEq, Repr

@[reducible] def Srt.denote : Srt → Type
  | .int => Int
  | .bool => Bool
  | .value => TinyML.Val
  | .vallist => List TinyML.Val

instance : DecidableEq (Srt.denote τ) := by
  cases τ <;> simp [Srt.denote] <;> infer_instance

instance : Inhabited (Srt.denote τ) := by
  cases τ <;> simp [Srt.denote] <;> infer_instance

-- ---------------------------------------------------------------------------
-- Variables and Contexts
-- ---------------------------------------------------------------------------

structure Var where
  name : String
  sort : Srt
  deriving DecidableEq, Repr

abbrev VarCtx := List Var

def VarCtx.disjoint (C : VarCtx) :=
  ∀ x x' t t', ⟨x, t⟩ ∈ C → ⟨x', t'⟩ ∈ C → x = x' → t = t'


-- ---------------------------------------------------------------------------
-- Environments
-- ---------------------------------------------------------------------------

def Env := (τ : Srt) → String → τ.denote

def Env.lookup (ρ : Env) (τ : Srt) (x : String) : τ.denote := ρ τ x

def Env.update (ρ : Env) (τ : Srt) (x : String) (v : τ.denote) : Env := fun τ' y =>
  if h : τ' = τ ∧ y = x then h.1 ▸ v else ρ τ' y

def Env.empty : Env := fun _ _ => default

instance : Inhabited Env := { default := Env.empty }

@[simp] theorem Env.lookup_update_same {ρ : Env} {τ : Srt} {x : String} {v : τ.denote} :
    (ρ.update τ x v).lookup τ x = v := by
  simp [Env.update, Env.lookup]

@[simp] theorem Env.lookup_update_ne' {ρ : Env} {τ : Srt} {x y : String} {v : τ.denote} (h : y ≠ x) :
    (Env.update ρ τ x v).lookup τ y = ρ.lookup τ y := by
  simp [Env.update, Env.lookup, h]

theorem Env.lookup_update_ne {ρ : Env} {τ τ' : Srt} {x y : String} {v : τ.denote}
    (h : y ≠ x ∨ τ' ≠ τ) : (ρ.update τ x v).lookup τ' y = ρ.lookup τ' y := by
  simp only [Env.update, Env.lookup]
  split
  · next heq => cases h with
    | inl h => exact absurd heq.2 h
    | inr h => exact absurd heq.1 h
  · rfl

def Env.agreeOn (Δ : VarCtx) (ρ ρ' : Env) : Prop :=
  ∀ v ∈ Δ, ρ.lookup v.sort v.name = ρ'.lookup v.sort v.name

theorem Env.agreeOn_refl : Env.agreeOn Δ ρ ρ := fun _ _ => rfl

theorem Env.agreeOn_mono {Δ₁ Δ₂ : VarCtx} (hsub : ∀ x ∈ Δ₁, x ∈ Δ₂)
    (h : Env.agreeOn Δ₂ ρ ρ') : Env.agreeOn Δ₁ ρ ρ' :=
  fun x hx => h x (hsub x hx)

theorem Env.agreeOn_symm {Δ : VarCtx} {ρ ρ' : Env} (h : Env.agreeOn Δ ρ ρ') : Env.agreeOn Δ ρ' ρ :=
  fun v hv => (h v hv).symm

theorem Env.agreeOn_trans {Δ : VarCtx}
    (h₁₂ : Env.agreeOn Δ ρ₁ ρ₂) (h₂₃ : Env.agreeOn Δ ρ₂ ρ₃) : Env.agreeOn Δ ρ₁ ρ₃ :=
  fun x hx => (h₁₂ x hx).trans (h₂₃ x hx)

theorem Env.agreeOn_update {ρ ρ' : Env} {Δ : VarCtx} {τ : Srt} {x : String} {v : τ.denote} :
    Env.agreeOn Δ ρ ρ' → Env.agreeOn (⟨x, τ⟩ :: Δ) (ρ.update τ x v) (ρ'.update τ x v) := fun hagree w hw => by
  cases hw with
  | head => simp [Env.lookup_update_same]
  | tail _ hw =>
    by_cases hn : w.name = x <;> by_cases ht : w.sort = τ
    · cases w; simp only at hn ht; subst hn ht
      simp only [Env.lookup_update_same]
    · simp only [Env.lookup_update_ne (Or.inr ht), hagree w hw]
    · simp only [Env.lookup_update_ne (Or.inl hn), hagree w hw]
    · simp only [Env.lookup_update_ne (Or.inl hn), hagree w hw]

/-- Double update with the same variable - second update wins. -/
@[simp] theorem Env.update_update_same {ρ : Env} {τ : Srt} {x : String} {v w : τ.denote} :
    (ρ.update τ x v).update τ x w = ρ.update τ x w := by
  funext τ' y; simp only [Env.update]
  split
  · simp
  · simp

/-- Updates to different variables commute. -/
theorem Env.update_comm {ρ : Env} {τ : Srt} {x y : String} {v w : τ.denote}
    (h : x ≠ y) : (ρ.update τ x v).update τ y w = (ρ.update τ y w).update τ x v := by
  funext τ' z; simp only [Env.update]
  split <;> split <;> simp_all
  · next h1 h2 => exact absurd (h2.2 ▸ h1.2) h
