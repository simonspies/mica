import Mica.TinyML.Expr

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

structure Var where
  name : String
  sort : Srt
  deriving DecidableEq, Repr

abbrev VarCtx := List Var

def VarCtx.disjoint (C : VarCtx) :=
  ∀ x x' t t', ⟨x, t⟩ ∈ C → ⟨x', t'⟩ ∈ C → x = x' → t = t'

inductive UnOp : Srt → Srt → Type where
  | ofInt      : UnOp .int     .value
  | ofBool     : UnOp .bool    .value
  | toInt      : UnOp .value   .int
  | toBool     : UnOp .value   .bool
  | neg        : UnOp .int     .int
  | not        : UnOp .bool    .bool
  | ofValList  : UnOp .vallist .value
  | toValList  : UnOp .value   .vallist
  | vhead      : UnOp .vallist .value
  | vtail      : UnOp .vallist .vallist
  | visnil     : UnOp .vallist .bool
  deriving DecidableEq, Repr

inductive BinOp : Srt → Srt → Srt → Type where
  | add  : BinOp .int   .int     .int
  | sub  : BinOp .int   .int     .int
  | mul  : BinOp .int   .int     .int
  | div  : BinOp .int   .int     .int
  | mod  : BinOp .int   .int     .int
  | less : BinOp .int   .int     .bool
  | gt   : BinOp .int   .int     .bool
  | ge   : BinOp .int   .int     .bool
  | eq   : BinOp τ      τ        .bool
  | vcons : BinOp .value .vallist .vallist
  deriving DecidableEq, Repr

inductive Const : Srt → Type where
  | i    : Int  → Const .int
  | b    : Bool → Const .bool
  | unit : Const .value
  | vnil : Const .vallist
  deriving DecidableEq, Repr

@[simp] def Const.denote : Const τ → τ.denote
  | .i n  => n
  | .b v  => v
  | .unit => TinyML.Val.unit
  | .vnil => []

inductive Term : Srt → Type where
  | var   : (τ : Srt) → String → Term τ
  | const : Const τ → Term τ
  | unop  : UnOp τ₁ τ₂ → Term τ₁ → Term τ₂
  | binop : BinOp τ₁ τ₂ τ₃ → Term τ₁ → Term τ₂ → Term τ₃
  | ite   : Term .bool → Term τ → Term τ → Term τ
  deriving DecidableEq

def Term.freeVars : Term τ → List Var
  | .var τ y   => [⟨y, τ⟩]
  | .const _   => []
  | .unop _ a  => a.freeVars
  | .binop _ a b => a.freeVars ++ b.freeVars
  | .ite c t e => c.freeVars ++ t.freeVars ++ e.freeVars

def Term.wfIn (t : Term τ) (Δ : VarCtx) : Prop :=
  ∀ v ∈ t.freeVars, v ∈ Δ

def Term.checkWf (t : Term τ) (Δ : VarCtx) : Except String Unit :=
  match t.freeVars.find? (· ∉ Δ) with
  | some v => .error s!"variable {repr v.name} : {repr v.sort} not in scope"
  | none => .ok ()

theorem Term.checkWf_ok {t : Term τ} {Δ : VarCtx} (h : t.checkWf Δ = .ok ()) : t.wfIn Δ := by
  simp only [Term.checkWf] at h
  split at h <;> simp at h
  rename_i heq
  intro v hv
  have := List.find?_eq_none.mp heq v hv
  simp at this
  exact this

theorem Term.wfIn_freeVars (t : Term τ) : t.wfIn t.freeVars := by
  intro v hv
  exact hv

theorem Term.wfIn_mono (t : Term τ) (h : t.wfIn Δ) (hsub : Δ ⊆ Δ') : t.wfIn Δ' := by
  intro v hv
  exact hsub (h v hv)


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

structure Env where
  intEnv     : String → Int
  boolEnv    : String → Bool
  valEnv     : String → TinyML.Val
  vallistEnv : String → List TinyML.Val

def Env.lookup (ρ : Env) (τ : Srt) (x : String) : τ.denote :=
  match τ with
  | .int     => ρ.intEnv x
  | .bool    => ρ.boolEnv x
  | .value   => ρ.valEnv x
  | .vallist => ρ.vallistEnv x

def Env.update (ρ : Env) (τ : Srt) (x : String) (v : τ.denote) : Env :=
  match τ with
  | .int     => { ρ with intEnv     := fun y => if y == x then v else ρ.intEnv y }
  | .bool    => { ρ with boolEnv    := fun y => if y == x then v else ρ.boolEnv y }
  | .value   => { ρ with valEnv     := fun y => if y == x then v else ρ.valEnv y }
  | .vallist => { ρ with vallistEnv := fun y => if y == x then v else ρ.vallistEnv y }

def Env.empty : Env :=
  { intEnv := λ _ => default, boolEnv := λ _ => default, valEnv := λ _ => default,
    vallistEnv := λ _ => default }

instance : Inhabited Env :=  { default := Env.empty }

@[simp] theorem Env.lookup_update_same {ρ : Env} {τ : Srt} {x : String} {v : τ.denote} :
    (ρ.update τ x v).lookup τ x = v := by
  cases τ <;> simp [Env.update, Env.lookup]

@[simp] theorem Env.lookup_update_ne' {ρ : Env} {τ : Srt} {x y : String} {v : τ.denote} (h : y ≠ x) :
    (Env.update ρ τ x v).lookup τ y = ρ.lookup τ y := by
  cases τ <;> simp [Env.update, Env.lookup, h]

theorem Env.lookup_update_ne {ρ : Env} {τ τ' : Srt} {x y : String} {v : τ.denote}
    (h : y ≠ x ∨ τ' ≠ τ) : (ρ.update τ x v).lookup τ' y = ρ.lookup τ' y := by
  cases τ <;> cases τ' <;> simp [Env.update, Env.lookup]
  all_goals (cases h with | inl h => simp [h] | inr h => exact absurd rfl h)

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
  cases τ <;> simp only [Env.update]
  · congr 1; funext y; simp only [beq_iff_eq]; split <;> rfl
  · congr 1; funext y; simp only [beq_iff_eq]; split <;> rfl
  · congr 1; funext y; simp only [beq_iff_eq]; split <;> rfl
  · congr 1; funext y; simp only [beq_iff_eq]; split <;> rfl

/-- Updates to different variables commute. -/
theorem Env.update_comm {ρ : Env} {τ : Srt} {x y : String} {v w : τ.denote}
    (h : x ≠ y) : (ρ.update τ x v).update τ y w = (ρ.update τ y w).update τ x v := by
  cases τ <;> simp only [Env.update]
  all_goals
    congr 1; funext z; simp only [beq_iff_eq]
    by_cases hzx : z = x <;> by_cases hzy : z = y <;> simp_all

@[simp] def UnOp.eval : UnOp τ₁ τ₂ → τ₁.denote → τ₂.denote
  | .ofInt,   n  => TinyML.Val.int n
  | .ofBool,  b  => TinyML.Val.bool b
  | .toInt,   v  => match v with | .int n => n | _ => 0
  | .toBool,  v  => match v with | .bool b => b | _ => false
  | .neg,     n  => -n
  | .not,     b  => !b
  | .ofValList, vs => TinyML.Val.tuple vs
  | .toValList, v  => match v with | .tuple vs => vs | _ => []
  | .vhead,   vs => vs.headD .unit
  | .vtail,   vs => vs.tail
  | .visnil,  vs => vs.isEmpty

@[simp] def BinOp.eval : BinOp τ₁ τ₂ τ₃ → τ₁.denote → τ₂.denote → τ₃.denote
  | .add,   a, b  => a + b
  | .sub,   a, b  => a - b
  | .mul,   a, b  => a * b
  | .div,   a, b  => a / b
  | .mod,   a, b  => a % b
  | .less,  a, b  => decide (a < b)
  | .gt,    a, b  => decide (a > b)
  | .ge,    a, b  => decide (a ≥ b)
  | .eq,    a, b  => decide (a = b)
  | .vcons, v, vs => v :: vs

def Term.eval (ρ : Env) : Term τ → τ.denote
  | .var τ y      => ρ.lookup τ y
  | .const c      => c.denote
  | .unop op a    => op.eval (Term.eval ρ a)
  | .binop op a b => op.eval (Term.eval ρ a) (Term.eval ρ b)
  | .ite c t e    => bif Term.eval ρ c then Term.eval ρ t else Term.eval ρ e

def Subst.eval (σ : Subst) (ρ : Env) : Env where
  intEnv x     := Term.eval ρ (σ.intSubst x)
  boolEnv x    := Term.eval ρ (σ.boolSubst x)
  valEnv x     := Term.eval ρ (σ.valSubst x)
  vallistEnv x := Term.eval ρ (σ.vallistSubst x)

theorem Subst.eval_lookup (σ : Subst) (ρ : Env) (τ : Srt) (x : String) :
    (σ.eval ρ).lookup τ x = Term.eval ρ (σ.apply τ x) := by
  cases τ <;> simp [Subst.eval, Env.lookup, Subst.apply]

theorem Subst.eval_single {τ : Srt} {x : String} {t : Term τ} {ρ : Env} :
    (Subst.single τ x t).eval ρ = ρ.update τ x (t.eval ρ) := by
  cases τ <;> simp only [Subst.eval, Subst.single, Subst.id, Subst.update, Env.update] <;>
    (congr 1; funext y; split <;> simp [Term.eval, Env.lookup])

theorem Term.eval_subst {σ : Subst} {ρ : Env} {t : Term τ} :
    Term.eval ρ (t.subst σ) = Term.eval (σ.eval ρ) t := by
  induction t with
  | var τ y => simp [Term.subst, Term.eval, Subst.eval_lookup]
  | const _ => simp [Term.subst, Term.eval]
  | unop op a iha => simp [Term.subst, Term.eval, iha]
  | binop op a b iha ihb => simp [Term.subst, Term.eval, iha, ihb]
  | ite c t e ihc iht ihe => simp [Term.subst, Term.eval, ihc, iht, ihe]

theorem Term.eval_env_agree {t : Term τ} {ρ ρ' : Env} {Δ : VarCtx} :
    t.wfIn Δ → Env.agreeOn Δ ρ ρ' → Term.eval ρ t = Term.eval ρ' t := by
  intro hwf hagree
  induction t with
  | var τ y =>
    simp [Term.eval]
    exact hagree ⟨y, τ⟩ (hwf ⟨y, τ⟩ (by simp [Term.freeVars]))
  | const _ => rfl
  | unop op a iha =>
    simp only [Term.eval]
    rw [iha (fun v hv => hwf v (by simp [Term.freeVars]; exact hv))]
  | binop op a b iha ihb =>
    simp only [Term.eval]
    rw [iha (fun v hv => hwf v (by simp [Term.freeVars]; left; exact hv))]
    rw [ihb (fun v hv => hwf v (by simp [Term.freeVars]; right; exact hv))]
  | ite c t e ihc iht ihe =>
    simp [Term.eval]
    rw [ihc (fun v hv => hwf v (by simp [Term.freeVars]; left; exact hv))]
    rw [iht (fun v hv => hwf v (by simp [Term.freeVars]; right; left; exact hv))]
    rw [ihe (fun v hv => hwf v (by simp [Term.freeVars]; right; right; exact hv))]

theorem Term.eval_update_fresh {t : Term τ'} {x : String} {τ : Srt} {v : τ.denote} {ρ : Env} :
    ⟨x, τ⟩ ∉ t.freeVars → Term.eval (ρ.update τ x v) t = Term.eval ρ t := by
  intro hfree
  symm
  apply Term.eval_env_agree t.wfIn_freeVars
  intro w hw
  by_cases ht : w.sort = τ
  · subst ht
    by_cases hn : w.name = x
    · subst hn; cases w; simp_all
    · exact (Env.lookup_update_ne' hn).symm
  · cases w; rename_i wn wt
    cases wt <;> cases τ <;> simp only [Env.lookup, Env.update] <;> try (exfalso; exact ht rfl)
