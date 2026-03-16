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
