import Mica.FOL.Variables

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
  | mkInj (tag : Nat) (arity : Nat) : UnOp .value .value
  | tagOf                           : UnOp .value .int
  | arityOf                         : UnOp .value .int
  | payloadOf                       : UnOp .value .value
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
  | .unit => Runtime.Val.unit
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

@[simp] def UnOp.eval : UnOp τ₁ τ₂ → τ₁.denote → τ₂.denote
  | .ofInt,   n  => Runtime.Val.int n
  | .ofBool,  b  => Runtime.Val.bool b
  | .toInt,   v  => match v with | .int n => n | _ => 0
  | .toBool,  v  => match v with | .bool b => b | _ => false
  | .neg,     n  => -n
  | .not,     b  => !b
  | .ofValList, vs => Runtime.Val.tuple vs
  | .toValList, v  => match v with | .tuple vs => vs | _ => []
  | .vhead,   vs => vs.headD .unit
  | .vtail,   vs => vs.tail
  | .visnil,  vs => vs.isEmpty
  | .mkInj tag arity, v => Runtime.Val.inj tag arity v
  | .tagOf,   v => match v with | .inj tag _ _ => (tag : Int) | _ => 0
  | .arityOf, v => match v with | .inj _ arity _ => (arity : Int) | _ => 0
  | .payloadOf, v => match v with | .inj _ _ payload => payload | _ => Runtime.Val.unit

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
  · exact (Env.lookup_update_ne (Or.inr ht)).symm
