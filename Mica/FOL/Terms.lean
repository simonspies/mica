import Mica.FOL.Variables
import Mica.Base.Except

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

@[simp] def Const.denote : Env → Const τ → τ.denote
  | _, .i n  => n
  | _, .b v  => v
  | _, .unit => Runtime.Val.unit
  | _, .vnil => []

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

def Term.wfIn : Term τ → Signature → Prop
  | .var τ x, Δ    => ⟨x, τ⟩ ∈ Δ.vars
  | .const _, _    => True
  | .unop _ a, Δ   => a.wfIn Δ
  | .binop _ a b, Δ => a.wfIn Δ ∧ b.wfIn Δ
  | .ite c t e, Δ  => c.wfIn Δ ∧ t.wfIn Δ ∧ e.wfIn Δ

def Term.checkWf : Term τ → Signature → Except String Unit
  | .var τ x, Δ    => if ⟨x, τ⟩ ∈ Δ.vars then .ok () else .error s!"variable {repr x} not in scope"
  | .const _, _    => .ok ()
  | .unop _ a, Δ   => a.checkWf Δ
  | .binop _ a b, Δ => do a.checkWf Δ; b.checkWf Δ
  | .ite c t e, Δ  => do c.checkWf Δ; t.checkWf Δ; e.checkWf Δ

theorem Term.checkWf_ok {t : Term τ} {Δ : Signature} (h : t.checkWf Δ = .ok ()) : t.wfIn Δ := by
  induction t generalizing Δ with
  | var τ x =>
    simp only [Term.checkWf] at h
    split at h
    · assumption
    · simp at h
  | const _ => trivial
  | unop _ a iha => exact iha h
  | binop _ a b iha ihb =>
    simp only [Term.checkWf] at h
    have ⟨h1, h2⟩ := bind_ok h
    exact ⟨iha h1, ihb h2⟩
  | ite c t e ihc iht ihe =>
    simp only [Term.checkWf] at h
    have ⟨h1, h23⟩ := bind_ok h
    have ⟨h2, h3⟩ := bind_ok h23
    exact ⟨ihc h1, iht h2, ihe h3⟩

theorem Term.wfIn_mono (t : Term τ) (h : t.wfIn Δ) (hsub : Δ.Subset Δ') : t.wfIn Δ' := by
  induction t generalizing Δ Δ' with
  | var τ x => exact hsub.vars _ h
  | const _ => trivial
  | unop _ a iha => exact iha h hsub
  | binop _ a b iha ihb => exact ⟨iha h.1 hsub, ihb h.2 hsub⟩
  | ite c t e ihc iht ihe => exact ⟨ihc h.1 hsub, iht h.2.1 hsub, ihe h.2.2 hsub⟩

@[simp] def UnOp.eval : Env → UnOp τ₁ τ₂ → τ₁.denote → τ₂.denote
  | _, .ofInt,   n  => Runtime.Val.int n
  | _, .ofBool,  b  => Runtime.Val.bool b
  | _, .toInt,   v  => match v with | .int n => n | _ => 0
  | _, .toBool,  v  => match v with | .bool b => b | _ => false
  | _, .neg,     n  => -n
  | _, .not,     b  => !b
  | _, .ofValList, vs => Runtime.Val.tuple vs
  | _, .toValList, v  => match v with | .tuple vs => vs | _ => []
  | _, .vhead,   vs => vs.headD .unit
  | _, .vtail,   vs => vs.tail
  | _, .visnil,  vs => vs.isEmpty
  | _, .mkInj tag arity, v => Runtime.Val.inj tag arity v
  | _, .tagOf,   v => match v with | .inj tag _ _ => (tag : Int) | _ => 0
  | _, .arityOf, v => match v with | .inj _ arity _ => (arity : Int) | _ => 0
  | _, .payloadOf, v => match v with | .inj _ _ payload => payload | _ => Runtime.Val.unit

@[simp] def BinOp.eval : Env → BinOp τ₁ τ₂ τ₃ → τ₁.denote → τ₂.denote → τ₃.denote
  | _, .add,   a, b  => a + b
  | _, .sub,   a, b  => a - b
  | _, .mul,   a, b  => a * b
  | _, .div,   a, b  => a / b
  | _, .mod,   a, b  => a % b
  | _, .less,  a, b  => decide (a < b)
  | _, .gt,    a, b  => decide (a > b)
  | _, .ge,    a, b  => decide (a ≥ b)
  | _, .eq,    a, b  => decide (a = b)
  | _, .vcons, v, vs => v :: vs

def Term.eval (ρ : Env) : Term τ → τ.denote
  | .var τ y      => ρ.lookup τ y
  | .const c      => c.denote ρ
  | .unop op a    => op.eval ρ (Term.eval ρ a)
  | .binop op a b => op.eval ρ (Term.eval ρ a) (Term.eval ρ b)
  | .ite c t e    => bif Term.eval ρ c then Term.eval ρ t else Term.eval ρ e

theorem Term.eval_env_agree {t : Term τ} {ρ ρ' : Env} {Δ : Signature} :
    t.wfIn Δ → Env.agreeOn Δ ρ ρ' → Term.eval ρ t = Term.eval ρ' t := by
  intro hwf hagree
  induction t with
  | var τ y => simp [Term.eval, Env.lookup]; exact hagree.1 ⟨y, τ⟩ hwf
  | const c => simp only [Term.eval]; cases c <;> rfl
  | unop op a iha => simp only [Term.eval]; rw [iha hwf]; cases op <;> rfl
  | binop op a b iha ihb =>
    simp only [Term.eval]
    rw [iha hwf.1, ihb hwf.2]; cases op <;> rfl
  | ite c t e ihc iht ihe =>
    simp [Term.eval]
    rw [ihc hwf.1, iht hwf.2.1, ihe hwf.2.2]

theorem Term.eval_update_not_in_sig {t : Term τ'} {x : String} {τ : Srt} {v : τ.denote} {ρ : Env}
    {Δ : Signature} (hwf : t.wfIn Δ) (hnotin : ⟨x, τ⟩ ∉ Δ.vars) :
    Term.eval (ρ.update τ x v) t = Term.eval ρ t :=
  Term.eval_env_agree hwf
    ⟨fun w hw => by
      by_cases heq : w = ⟨x, τ⟩
      · subst heq; exact absurd hw hnotin
      · have hne : w.name ≠ x ∨ w.sort ≠ τ := by
          obtain ⟨wname, wtype⟩ := w
          by_cases h : wname = x <;> by_cases ht : wtype = τ
          · exfalso; apply heq; simp [h, ht]
          · exact Or.inr ht
          · exact Or.inl h
          · exact Or.inl h
        exact Env.lookup_update_ne hne,
     fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem Term.eval_update_fresh {t : Term τ'} {x : String} {τ : Srt} {v : τ.denote} {ρ : Env} :
    ⟨x, τ⟩ ∉ t.freeVars → Term.eval (ρ.update τ x v) t = Term.eval ρ t := by
  intro hfree
  induction t with
  | var τ_v y =>
    simp only [Term.freeVars, List.mem_singleton] at hfree
    simp only [Term.eval]
    by_cases h1 : y = x
    · by_cases h2 : τ_v = τ
      · subst h1; subst h2; exact absurd rfl hfree
      · exact Env.lookup_update_ne (Or.inr h2)
    · exact Env.lookup_update_ne (Or.inl h1)
  | const c => simp only [Term.eval]; cases c <;> rfl
  | unop op a iha =>
    simp only [Term.freeVars] at hfree
    simp only [Term.eval, iha hfree]; cases op <;> rfl
  | binop op a b iha ihb =>
    simp only [Term.freeVars, List.mem_append, not_or] at hfree
    simp only [Term.eval, iha hfree.1, ihb hfree.2]; cases op <;> rfl
  | ite c t e ihc iht ihe =>
    simp only [Term.freeVars, List.mem_append, not_or] at hfree
    obtain ⟨⟨hc, ht'⟩, he⟩ := hfree
    simp only [Term.eval, ihc hc, iht ht', ihe he]
