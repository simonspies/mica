import Mica.TinyML.RuntimeExpr

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
  | .value => Runtime.Val
  | .vallist => List Runtime.Val

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
-- Signature: extends VarCtx with named function symbols
-- ---------------------------------------------------------------------------

namespace FOL

structure Const where
  name : String
  sort : Srt
  deriving DecidableEq, Repr

structure Unary where
  name : String
  arg  : Srt
  ret  : Srt
  deriving DecidableEq, Repr

structure Binary where
  name : String
  arg1 : Srt
  arg2 : Srt
  ret  : Srt
  deriving DecidableEq, Repr

end FOL

structure Signature where
  vars   : VarCtx
  consts : List FOL.Const
  unary  : List FOL.Unary
  binary : List FOL.Binary

namespace Signature

def empty : Signature := ⟨[], [], [], []⟩

@[simp] theorem empty_vars    : (empty : Signature).vars   = [] := rfl
@[simp] theorem empty_consts  : (empty : Signature).consts = [] := rfl
@[simp] theorem empty_unary   : (empty : Signature).unary  = [] := rfl
@[simp] theorem empty_binary  : (empty : Signature).binary = [] := rfl

def addVar (Δ : Signature) (v : Var) : Signature := { Δ with vars := v :: Δ.vars }
def addVars (Δ : Signature) (vs : List Var) : Signature := { Δ with vars := vs ++ Δ.vars }

def addConst (Δ : Signature) (c : FOL.Const) : Signature := { Δ with consts := c :: Δ.consts }
def addUnary (Δ : Signature) (u : FOL.Unary) : Signature := { Δ with unary := u :: Δ.unary }
def addBinary (Δ : Signature) (b : FOL.Binary) : Signature := { Δ with binary := b :: Δ.binary }

def ofVars (vars : VarCtx) : Signature := ⟨vars, [], [], []⟩

@[simp] theorem ofVars_vars (vars : VarCtx) : (ofVars vars).vars = vars := rfl

@[simp] theorem eta (s : Signature) :
    ⟨s.vars, s.consts, s.unary, s.binary⟩ = s := by cases s; rfl

structure Subset (Δ₁ Δ₂ : Signature) : Prop where
  vars   : ∀ x ∈ Δ₁.vars, x ∈ Δ₂.vars
  consts : ∀ c ∈ Δ₁.consts, c ∈ Δ₂.consts
  unary  : ∀ u ∈ Δ₁.unary, u ∈ Δ₂.unary
  binary : ∀ b ∈ Δ₁.binary, b ∈ Δ₂.binary

theorem Subset.refl (Δ : Signature) : Δ.Subset Δ :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem Subset.addVar {Δ Δ' : Signature} (h : Δ.Subset Δ') (v : Var) :
    (Δ.addVar v).Subset (Δ'.addVar v) :=
  ⟨fun x hx => by cases hx with | head => left | tail _ hmem => right; exact h.vars x hmem,
   h.consts, h.unary, h.binary⟩

theorem Subset.addVars {Δ Δ' : Signature} (h : Δ.Subset Δ') (vs : List Var) :
    (Δ.addVars vs).Subset (Δ'.addVars vs) :=
  ⟨fun x hx => by
    cases List.mem_append.mp hx with
    | inl hmem => exact List.mem_append_left _ hmem
    | inr hmem => exact List.mem_append_right _ (h.vars x hmem),
   h.consts, h.unary, h.binary⟩

theorem Subset.subset_addVar (Δ : Signature) (v : Var) :
    Δ.Subset (Δ.addVar v) :=
  ⟨fun _ hx => List.mem_cons_of_mem _ hx, fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem Subset.subset_addVars (Δ : Signature) (vs : List Var) :
    Δ.Subset (Δ.addVars vs) :=
  ⟨fun _ hx => List.mem_append_right _ hx, fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem Subset.addVars_cons (Δ : Signature) (v : Var) (vs : List Var) :
    (Δ.addVars (v :: vs)).Subset ((Δ.addVar v).addVars vs) := by
  constructor
  · intro x hx
    change x ∈ (v :: vs) ++ Δ.vars at hx
    change x ∈ vs ++ (v :: Δ.vars)
    simp only [List.mem_cons, List.mem_append, or_assoc] at hx ⊢
    rcases hx with rfl | hx | hx
    · right; left; rfl
    · left; exact hx
    · right; right; exact hx
  · intro c hc; exact hc
  · intro u hu; exact hu
  · intro b hb; exact hb

theorem Subset.addVar_addVars (Δ : Signature) (v : Var) (vs : List Var) :
    ((Δ.addVar v).addVars vs).Subset (Δ.addVars (v :: vs)) := by
  constructor
  · intro x hx
    change x ∈ vs ++ (v :: Δ.vars) at hx
    change x ∈ (v :: vs) ++ Δ.vars
    simp only [List.mem_cons, List.mem_append, or_assoc] at hx ⊢
    rcases hx with hx | rfl | hx
    · right; left; exact hx
    · left; rfl
    · right; right; exact hx
  · intro c hc; exact hc
  · intro u hu; exact hu
  · intro b hb; exact hb

theorem Subset.of_vars_subset_ofVars {vars vars' : VarCtx} (h : vars ⊆ vars') :
    (Signature.ofVars vars).Subset (Signature.ofVars vars') :=
  ⟨h, fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem Subset.trans {Δ₁ Δ₂ Δ₃ : Signature} (h₁₂ : Δ₁.Subset Δ₂) (h₂₃ : Δ₂.Subset Δ₃) :
    Δ₁.Subset Δ₃ :=
  ⟨fun x hx => h₂₃.vars x (h₁₂.vars x hx),
   fun c hc => h₂₃.consts c (h₁₂.consts c hc),
   fun u hu => h₂₃.unary u (h₁₂.unary u hu),
   fun b hb => h₂₃.binary b (h₁₂.binary b hb)⟩

theorem Subset.mono_vars {Δ Δ' : Signature} (h : Δ.Subset Δ') : Δ.vars ⊆ Δ'.vars :=
  h.vars

end Signature

-- ---------------------------------------------------------------------------
-- Environments
-- ---------------------------------------------------------------------------

structure Env where
  vars   : (τ : Srt) → String → τ.denote
  consts : (τ : Srt) → String → τ.denote
  unary  : (τ₁ τ₂ : Srt) → String → τ₁.denote → τ₂.denote
  binary : (τ₁ τ₂ τ₃ : Srt) → String → τ₁.denote → τ₂.denote → τ₃.denote

theorem Env.ext {e1 e2 : Env}
    (h1 : e1.vars = e2.vars) (h2 : e1.consts = e2.consts)
    (h3 : e1.unary = e2.unary) (h4 : e1.binary = e2.binary) : e1 = e2 := by
  cases e1; cases e2; congr

def Env.lookup (ρ : Env) (τ : Srt) (x : String) : τ.denote := ρ.vars τ x

def Env.update (ρ : Env) (τ : Srt) (x : String) (v : τ.denote) : Env :=
  { ρ with vars := fun τ' y => if h : τ' = τ ∧ y = x then h.1 ▸ v else ρ.vars τ' y }

def Env.updateConst (ρ : Env) (τ : Srt) (x : String) (v : τ.denote) : Env :=
  { ρ with consts := fun τ' y => if h : τ' = τ ∧ y = x then h.1 ▸ v else ρ.consts τ' y }

def Env.updateUnary (ρ : Env) (τ₁ τ₂ : Srt) (x : String) (f : τ₁.denote → τ₂.denote) : Env :=
  { ρ with unary := fun τ₁' τ₂' y =>
    if h : τ₁' = τ₁ ∧ τ₂' = τ₂ ∧ y = x then h.1 ▸ h.2.1 ▸ f else ρ.unary τ₁' τ₂' y }

def Env.updateBinary (ρ : Env) (τ₁ τ₂ τ₃ : Srt) (x : String)
    (f : τ₁.denote → τ₂.denote → τ₃.denote) : Env :=
  { ρ with binary := fun τ₁' τ₂' τ₃' y =>
    if h : τ₁' = τ₁ ∧ τ₂' = τ₂ ∧ τ₃' = τ₃ ∧ y = x then h.1 ▸ h.2.1 ▸ h.2.2.1 ▸ f
    else ρ.binary τ₁' τ₂' τ₃' y }

def Env.empty : Env :=
  ⟨fun _ _ => default, fun _ _ => default, fun _ _ _ _ => default, fun _ _ _ _ _ => default⟩

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

def Env.agreeOn (Δ : Signature) (ρ ρ' : Env) : Prop :=
  (∀ v ∈ Δ.vars, ρ.lookup v.sort v.name = ρ'.lookup v.sort v.name) ∧
  (∀ c ∈ Δ.consts, ρ.consts c.sort c.name = ρ'.consts c.sort c.name) ∧
  (∀ u ∈ Δ.unary, ρ.unary u.arg u.ret u.name = ρ'.unary u.arg u.ret u.name) ∧
  (∀ b ∈ Δ.binary, ρ.binary b.arg1 b.arg2 b.ret b.name = ρ'.binary b.arg1 b.arg2 b.ret b.name)

theorem Env.agreeOn_refl : Env.agreeOn Δ ρ ρ :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem Env.agreeOn_mono {Δ₁ Δ₂ : Signature} (hsub : Δ₁.Subset Δ₂)
    (h : Env.agreeOn Δ₂ ρ ρ') : Env.agreeOn Δ₁ ρ ρ' :=
  ⟨fun x hx => h.1 x (hsub.vars x hx),
   fun c hc => h.2.1 c (hsub.consts c hc),
   fun u hu => h.2.2.1 u (hsub.unary u hu),
   fun b hb => h.2.2.2 b (hsub.binary b hb)⟩

theorem Env.agreeOn_symm {Δ : Signature} {ρ ρ' : Env} (h : Env.agreeOn Δ ρ ρ') : Env.agreeOn Δ ρ' ρ :=
  ⟨fun v hv => (h.1 v hv).symm,
   fun c hc => (h.2.1 c hc).symm,
   fun u hu => (h.2.2.1 u hu).symm,
   fun b hb => (h.2.2.2 b hb).symm⟩

theorem Env.agreeOn_trans {Δ : Signature}
    (h₁₂ : Env.agreeOn Δ ρ₁ ρ₂) (h₂₃ : Env.agreeOn Δ ρ₂ ρ₃) : Env.agreeOn Δ ρ₁ ρ₃ :=
  ⟨fun x hx => (h₁₂.1 x hx).trans (h₂₃.1 x hx),
   fun c hc => (h₁₂.2.1 c hc).trans (h₂₃.2.1 c hc),
   fun u hu => (h₁₂.2.2.1 u hu).trans (h₂₃.2.2.1 u hu),
   fun b hb => (h₁₂.2.2.2 b hb).trans (h₂₃.2.2.2 b hb)⟩

theorem Env.agreeOn_addVars_cons (Δ : Signature) (v : Var) (vs : List Var) (ρ ρ' : Env) :
    Env.agreeOn (Δ.addVars (v :: vs)) ρ ρ' ↔ Env.agreeOn ((Δ.addVar v).addVars vs) ρ ρ' :=
  ⟨Env.agreeOn_mono (Signature.Subset.addVar_addVars Δ v vs), Env.agreeOn_mono (Signature.Subset.addVars_cons Δ v vs)⟩

theorem Env.agreeOn_update {ρ ρ' : Env} {Δ : Signature} {τ : Srt} {x : String} {v : τ.denote} :
    Env.agreeOn Δ ρ ρ' →
    Env.agreeOn (Δ.addVar ⟨x, τ⟩) (ρ.update τ x v) (ρ'.update τ x v) :=
  fun hagree =>
  ⟨fun w hw => by
    cases hw with
    | head => simp [Env.lookup_update_same]
    | tail _ hw =>
      by_cases hn : w.name = x <;> by_cases ht : w.sort = τ
      · cases w; simp only at hn ht; subst hn ht
        simp only [Env.lookup_update_same]
      · simp only [Env.lookup_update_ne (Or.inr ht), hagree.1 w hw]
      · simp only [Env.lookup_update_ne (Or.inl hn), hagree.1 w hw]
      · simp only [Env.lookup_update_ne (Or.inl hn), hagree.1 w hw],
   fun c hc => by simp [Env.update]; exact hagree.2.1 c hc,
   fun u hu => by simp [Env.update]; exact hagree.2.2.1 u hu,
   fun b hb => by simp [Env.update]; exact hagree.2.2.2 b hb⟩

/-- Double update with the same variable - second update wins. -/
@[simp] theorem Env.update_update_same {ρ : Env} {τ : Srt} {x : String} {v w : τ.denote} :
    (ρ.update τ x v).update τ x w = ρ.update τ x w := by
  apply Env.ext
  · funext τ' y
    simp only [Env.update]
    split
    · simp
    · simp
  all_goals rfl

/-- Updates to different variables commute. -/
theorem Env.update_comm {ρ : Env} {τ : Srt} {x y : String} {v w : τ.denote}
    (h : x ≠ y) : (ρ.update τ x v).update τ y w = (ρ.update τ y w).update τ x v := by
  apply Env.ext
  · funext τ' z
    simp only [Env.update]
    split <;> split <;> simp_all
    · next h1 h2 => exact absurd (h2.2 ▸ h1.2) h
  all_goals rfl
