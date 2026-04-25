-- SUMMARY: Typed first-order terms, their Tarski semantics, and their well-formedness conditions.
import Mica.FOL.Variables
import Mica.Base.Except
import Batteries.Data.List.Basic

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
  | uninterpreted : String → (τ₁ τ₂ : Srt) → UnOp τ₁ τ₂
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
  | uninterpreted : String → (τ₁ τ₂ τ₃ : Srt) → BinOp τ₁ τ₂ τ₃
  deriving DecidableEq, Repr

inductive Const : Srt → Type where
  | i    : Int  → Const .int
  | b    : Bool → Const .bool
  | unit : Const .value
  | vnil : Const .vallist
  | uninterpreted : String → (τ : Srt) → Const τ
  deriving DecidableEq, Repr

@[simp] def Const.denote : Env → Const τ → τ.denote
  | _, .i n  => n
  | _, .b v  => v
  | _, .unit => Runtime.Val.unit
  | _, .vnil => []
  | ρ, .uninterpreted name _ => ρ.consts τ name

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

def Const.wfIn : Const τ → Signature → Prop
  | .uninterpreted name τ, Δ => ⟨name, τ⟩ ∈ Δ.consts
                               ∧ (∀ τ', ⟨name, τ'⟩ ∉ Δ.vars)
                               ∧ (∀ τ', ⟨name, τ'⟩ ∈ Δ.consts → τ' = τ)
  | _, _                     => True

def UnOp.wfIn : UnOp τ₁ τ₂ → Signature → Prop
  | .uninterpreted name τ₁ τ₂, Δ => ⟨name, τ₁, τ₂⟩ ∈ Δ.unary
  | _, _                          => True

def BinOp.wfIn : BinOp τ₁ τ₂ τ₃ → Signature → Prop
  | .uninterpreted name τ₁ τ₂ τ₃, Δ => ⟨name, τ₁, τ₂, τ₃⟩ ∈ Δ.binary
  | _, _                              => True

def Const.checkWf : Const τ → Signature → Except String Unit
  | .uninterpreted name τ, Δ =>
    if ⟨name, τ⟩ ∈ Δ.consts then
      if name ∈ Δ.vars.map Var.name then .error s!"constant {name} conflicts with a variable"
      else if Δ.consts.any (fun c => c.name == name && c.sort != τ) then
        .error s!"constant {name} has multiple sorts in signature"
      else .ok ()
    else .error s!"constant {name} not in signature"
  | _, _ => .ok ()

def UnOp.checkWf : UnOp τ₁ τ₂ → Signature → Except String Unit
  | .uninterpreted name τ₁ τ₂, Δ =>
    if ⟨name, τ₁, τ₂⟩ ∈ Δ.unary then .ok () else .error s!"unary op {name} not in signature"
  | _, _ => .ok ()

def BinOp.checkWf : BinOp τ₁ τ₂ τ₃ → Signature → Except String Unit
  | .uninterpreted name τ₁ τ₂ τ₃, Δ =>
    if ⟨name, τ₁, τ₂, τ₃⟩ ∈ Δ.binary then .ok () else .error s!"binary op {name} not in signature"
  | _, _ => .ok ()

def Term.wfIn : Term τ → Signature → Prop
  | .var τ x, Δ     => ⟨x, τ⟩ ∈ Δ.vars
                     ∧ (∀ τ', ⟨x, τ'⟩ ∉ Δ.consts)
                     ∧ (∀ τ', ⟨x, τ'⟩ ∈ Δ.vars → τ' = τ)
  | .const c, Δ     => c.wfIn Δ
  | .unop op a, Δ   => op.wfIn Δ ∧ a.wfIn Δ
  | .binop op a b, Δ => op.wfIn Δ ∧ a.wfIn Δ ∧ b.wfIn Δ
  | .ite c t e, Δ   => c.wfIn Δ ∧ t.wfIn Δ ∧ e.wfIn Δ

def Term.checkWf : Term τ → Signature → Except String Unit
  | .var τ x, Δ     =>
    if ⟨x, τ⟩ ∈ Δ.vars then
      if x ∈ Δ.consts.map FOL.Const.name then .error s!"variable {repr x} conflicts with a constant"
      else if Δ.vars.any (fun v => v.name == x && v.sort != τ) then
        .error s!"variable {repr x} has multiple sorts in scope"
      else .ok ()
    else .error s!"variable {repr x} not in scope"
  | .const c, Δ     => c.checkWf Δ
  | .unop op a, Δ   => do op.checkWf Δ; a.checkWf Δ
  | .binop op a b, Δ => do op.checkWf Δ; a.checkWf Δ; b.checkWf Δ
  | .ite c t e, Δ   => do c.checkWf Δ; t.checkWf Δ; e.checkWf Δ

private theorem Const.checkWf_ok {c : Const τ} {Δ : Signature} (h : c.checkWf Δ = .ok ()) :
    c.wfIn Δ := by
  cases c with
  | uninterpreted name τ =>
    simp only [Const.checkWf] at h
    split at h
    · rename_i hmem
      split at h
      · simp at h
      · rename_i hvar
        split at h
        · simp at h
        · rename_i hdup
          refine ⟨hmem, ?_, ?_⟩
          · intro τ' hv
            exact hvar (List.mem_map_of_mem hv)
          · intro τ' hc'
            rcases decEq τ' τ with hne | h
            · exfalso; apply hdup; apply List.any_eq_true.mpr
              refine ⟨⟨name, τ'⟩, hc', ?_⟩; simp [hne]
            · exact h
    · simp at h
  | _ => trivial

private theorem UnOp.checkWf_ok {op : UnOp τ₁ τ₂} {Δ : Signature} (h : op.checkWf Δ = .ok ()) :
    op.wfIn Δ := by
  cases op with
  | uninterpreted name τ₁ τ₂ =>
    simp only [UnOp.checkWf] at h; split at h; assumption; simp at h
  | _ => trivial

private theorem BinOp.checkWf_ok {op : BinOp τ₁ τ₂ τ₃} {Δ : Signature}
    (h : op.checkWf Δ = .ok ()) : op.wfIn Δ := by
  cases op with
  | uninterpreted name τ₁ τ₂ τ₃ =>
    simp only [BinOp.checkWf] at h; split at h; assumption; simp at h
  | _ => trivial

theorem Term.checkWf_ok {t : Term τ} {Δ : Signature} (h : t.checkWf Δ = .ok ()) : t.wfIn Δ := by
  induction t generalizing Δ with
  | var τ x =>
    simp only [Term.checkWf] at h
    split at h
    · rename_i hmem
      split at h
      · simp at h
      · rename_i hconst
        split at h
        · simp at h
        · rename_i hdup
          refine ⟨hmem, ?_, ?_⟩
          · intro τ' hc
            exact hconst (List.mem_map_of_mem hc)
          · intro τ' hv'
            rcases decEq τ' τ with hne | h
            · exfalso; apply hdup; apply List.any_eq_true.mpr
              refine ⟨⟨x, τ'⟩, hv', ?_⟩; simp [hne]
            · exact h
    · simp at h
  | const c =>
    simpa [Term.checkWf] using (Const.checkWf_ok h)
  | unop op a iha =>
    simp only [Term.checkWf] at h
    have ⟨h1, h2⟩ := bind_ok h
    exact ⟨UnOp.checkWf_ok h1, iha h2⟩
  | binop op a b iha ihb =>
    simp only [Term.checkWf] at h
    have ⟨h1, h23⟩ := bind_ok h
    have ⟨h2, h3⟩ := bind_ok h23
    exact ⟨BinOp.checkWf_ok h1, iha h2, ihb h3⟩
  | ite c t e ihc iht ihe =>
    simp only [Term.checkWf] at h
    have ⟨h1, h23⟩ := bind_ok h
    have ⟨h2, h3⟩ := bind_ok h23
    exact ⟨ihc h1, iht h2, ihe h3⟩

private theorem Const.wfIn_mono {c : Const τ} {Δ Δ' : Signature} (h : c.wfIn Δ)
    (hsub : Δ.Subset Δ') (hwf : Δ'.wf) : c.wfIn Δ' := by
  cases c with
  | uninterpreted name τ =>
    refine ⟨hsub.consts _ h.1, ?_, ?_⟩
    · intro τ' hvar
      exact Signature.wf_no_var_of_const hwf (hsub.consts _ h.1) hvar
    · intro τ' hc'
      exact Signature.wf_unique_const hwf (hsub.consts _ h.1) hc'
  | _ => trivial

private theorem UnOp.wfIn_mono {op : UnOp τ₁ τ₂} {Δ Δ' : Signature} (h : op.wfIn Δ)
    (hsub : Δ.Subset Δ') : op.wfIn Δ' := by
  cases op with
  | uninterpreted name τ₁ τ₂ => exact hsub.unary _ h
  | _ => trivial

private theorem BinOp.wfIn_mono {op : BinOp τ₁ τ₂ τ₃} {Δ Δ' : Signature} (h : op.wfIn Δ)
    (hsub : Δ.Subset Δ') : op.wfIn Δ' := by
  cases op with
  | uninterpreted name τ₁ τ₂ τ₃ => exact hsub.binary _ h
  | _ => trivial

theorem Term.wfIn_mono (t : Term τ) (h : t.wfIn Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) : t.wfIn Δ' := by
  induction t generalizing Δ Δ' with
  | var τ x =>
    refine ⟨hsub.vars _ h.1, ?_, ?_⟩
    · intro τ' hconst
      exact Signature.wf_no_const_of_var hwf (hsub.vars _ h.1) hconst
    · intro τ' hv'
      exact Signature.wf_unique_var hwf (hsub.vars _ h.1) hv'
  | const c => exact Const.wfIn_mono h hsub hwf
  | unop op a iha => exact ⟨UnOp.wfIn_mono h.1 hsub, iha h.2 hsub hwf⟩
  | binop op a b iha ihb => exact ⟨BinOp.wfIn_mono h.1 hsub, iha h.2.1 hsub hwf, ihb h.2.2 hsub hwf⟩
  | ite c t e ihc iht ihe => exact ⟨ihc h.1 hsub hwf, iht h.2.1 hsub hwf, ihe h.2.2 hsub hwf⟩

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
  | ρ, .uninterpreted name _ _, x => ρ.unary τ₁ τ₂ name x

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
  | ρ, .uninterpreted name _ _ _, x, y => ρ.binary τ₁ τ₂ τ₃ name x y

def Term.eval (ρ : Env) : Term τ → τ.denote
  | .var τ y      => ρ.lookupConst τ y
  | .const c      => c.denote ρ
  | .unop op a    => op.eval ρ (Term.eval ρ a)
  | .binop op a b => op.eval ρ (Term.eval ρ a) (Term.eval ρ b)
  | .ite c t e    => bif Term.eval ρ c then Term.eval ρ t else Term.eval ρ e

theorem Term.eval_env_agree {t : Term τ} {ρ ρ' : Env} {Δ : Signature} :
    t.wfIn Δ → Env.agreeOn Δ ρ ρ' → Term.eval ρ t = Term.eval ρ' t := by
  intro hwf hagree
  induction t with
  | var τ y => simp [Term.eval, Env.lookupConst]; exact hagree.1 ⟨y, τ⟩ hwf.1
  | const c =>
    simp only [Term.eval]
    cases c with
    | uninterpreted name _ => exact hagree.2.1 ⟨name, _⟩ hwf.1
    | _ => rfl
  | unop op a iha =>
    simp only [Term.eval]
    rw [iha hwf.2]
    cases op with
    | uninterpreted name _ _ =>
      simp only [UnOp.eval]
      exact congrFun (hagree.2.2.1 ⟨name, _, _⟩ hwf.1) _
    | _ => rfl
  | binop op a b iha ihb =>
    simp only [Term.eval]
    rw [iha hwf.2.1, ihb hwf.2.2]
    cases op with
    | uninterpreted name _ _ _ =>
      simp only [BinOp.eval]
      exact congrFun (congrFun (hagree.2.2.2 ⟨name, _, _, _⟩ hwf.1) _) _
    | _ => rfl
  | ite c t e ihc iht ihe =>
    simp [Term.eval]
    rw [ihc hwf.1, iht hwf.2.1, ihe hwf.2.2]

theorem Term.eval_update_fresh {t : Term τ'} {x : String} {τ : Srt} {v : τ.denote} {ρ : Env}
    {Δ : Signature} (hwf : t.wfIn Δ) (hfresh : x ∉ Δ.allNames) :
    Term.eval (ρ.updateConst τ x v) t = Term.eval ρ t :=
  Term.eval_env_agree hwf
    ⟨fun w hw => by
      have hne : w.name ≠ x := by
        intro heq
        exact hfresh (heq ▸ Signature.mem_allNames_of_var hw)
      exact Env.lookupConst_updateConst_ne' (Or.inl hne),
     fun c hc => by
      have hne : c.name ≠ x := by
        intro heq
        exact hfresh (heq ▸ Signature.mem_allNames_of_const hc)
      exact Env.lookupConst_updateConst_ne' (Or.inl hne),
     fun _ _ => rfl, fun _ _ => rfl⟩

/-! simple helper lemmas -/

/-- A constant-term is well-formed whenever it is in the signature's consts. -/
theorem Term.const_wfIn_of_mem {Δ : Signature} {name : String} {τ : Srt}
    (hwf : Δ.wf) (hmem : ⟨name, τ⟩ ∈ Δ.consts) :
    (Term.const (.uninterpreted name τ)).wfIn Δ :=
  ⟨hmem,
    fun _ hvar => Signature.wf_no_var_of_const hwf hmem hvar,
    fun _ hc' => Signature.wf_unique_const hwf hmem hc'⟩

/-- A fresh uninterpreted constant is well-formed in a signature extended by itself. -/
theorem Term.const_wfIn_addConst_of_fresh {Δ : Signature} {c : FOL.Const}
    (hΔwf : Δ.wf) (hfresh : c.name ∉ Δ.allNames) :
    (Term.const (.uninterpreted c.name c.sort)).wfIn (Δ.addConst c) :=
  Term.const_wfIn_of_mem (Signature.wf_addConst hΔwf hfresh) (List.Mem.head _)

/-- Evaluating a constant term at an updated env yields the updated value. -/
@[simp] theorem Term.eval_const_updateConst {ρ : Env} {τ : Srt} {x : String}
    {v : τ.denote} :
    (Term.const (.uninterpreted x τ)).eval (ρ.updateConst τ x v) = v := by
  simp [Term.eval, Const.denote, Env.updateConst]

/-! ### Vallist projections -/

-- Projection helpers for repeated `vtail` and indexed `vhead` access on `vallist` terms.
/-- Apply `vtail` n times to a vallist term. -/
def vtailN (t : Term .vallist) : Nat → Term .vallist
  | 0     => t
  | n + 1 => .unop .vtail (vtailN t n)

@[simp] theorem vtailN_freeVars (t : Term .vallist) (n : Nat) :
    (vtailN t n).freeVars = t.freeVars := by
  induction n with
  | zero => simp [vtailN]
  | succ n ih => simp [vtailN, Term.freeVars, ih]

theorem vtailN_wfIn {t : Term .vallist} {Δ : Signature} (ht : t.wfIn Δ) (n : Nat) :
    (vtailN t n).wfIn Δ := by
  induction n with
  | zero => simpa [vtailN]
  | succ n ih => simp only [vtailN, Term.wfIn]; exact ⟨trivial, ih⟩

@[simp] theorem vtailN_eval (t : Term .vallist) (ρ : Env) :
    ∀ n, (vtailN t n).eval ρ = List.drop n (t.eval ρ)
  | 0 => by simp [vtailN]
  | n + 1 => by
    simp only [vtailN, Term.eval, UnOp.eval, vtailN_eval t ρ n]
    rw [List.tail_drop]

theorem vhead_vtailN_eval {vs : List Runtime.Val} {w : Runtime.Val} {n : Nat}
    (h : vs[n]? = some w) (t : Term .vallist) (ρ : Env) (ht : t.eval ρ = vs) :
    (Term.unop .vhead (vtailN t n)).eval ρ = w := by
  simp [Term.eval, UnOp.eval, ht, h]

/-! ### Lists of value terms -/

/-- Pack a list of value-sorted terms into a `vallist`-sorted term using
    `.vcons` and `.vnil`. -/
def Terms.toValList : List (Term .value) → Term .vallist
  | [] => .const .vnil
  | t :: ts => .binop .vcons t (toValList ts)

@[simp] theorem Terms.toValList_nil : toValList [] = .const .vnil := rfl
@[simp] theorem Terms.toValList_cons (t : Term .value) (ts : List (Term .value)) :
    toValList (t :: ts) = .binop .vcons t (toValList ts) := rfl

/-- If all terms in `ts` are well-formed in `Δ`, then `toValList ts` is
    well-formed in `Δ`. -/
theorem Terms.toValList_wfIn {ts : List (Term .value)} {Δ : Signature}
    (h : ∀ t ∈ ts, t.wfIn Δ) : (toValList ts).wfIn Δ := by
  induction ts with
  | nil => trivial
  | cons t ts ih =>
    simp only [toValList, Term.wfIn]
    exact ⟨trivial, h t (.head _), ih (fun q hq => h q (.tail _ hq))⟩

/-- A list of terms evaluates to a list of values. -/
def Terms.Eval (ρ : Env) (ts : List (Term .value)) (vs : List Runtime.Val) : Prop :=
  List.Forall₂ (fun t v => t.eval ρ = v) ts vs

theorem Terms.Eval.map_eval {ρ : Env} {ts : List (Term .value)} {vs : List Runtime.Val}
    (h : Terms.Eval ρ ts vs) : ts.map (fun t => t.eval ρ) = vs := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [h, ih]

theorem Terms.toValList_eval {ρ : Env} {ts : List (Term .value)} {vs : List Runtime.Val}
    (h : Terms.Eval ρ ts vs) : (Terms.toValList ts).eval ρ = vs := by
  induction h with
  | nil => simp [Terms.toValList, Term.eval, Const.denote]
  | cons hhead _ ih => simp [Terms.toValList, Term.eval, BinOp.eval, hhead, ih]

theorem Terms.Eval.env_agree {ρ ρ' : Env} {Δ : Signature}
    {ts : List (Term .value)} {vs : List Runtime.Val}
    (hwf : ∀ t ∈ ts, t.wfIn Δ)
    (hagree : Env.agreeOn Δ ρ ρ')
    (h : Terms.Eval ρ ts vs) : Terms.Eval ρ' ts vs := by
  induction h with
  | nil => exact .nil
  | @cons t v ts' vs' htv _ ih =>
    constructor
    · rw [Term.eval_env_agree (hwf t (.head _)) (Env.agreeOn_symm hagree)]; exact htv
    · exact ih (fun q hq => hwf q (.tail _ hq))

theorem Terms.Eval.cons {ρ : Env} {t : Term .value} {v : Runtime.Val}
    {ts : List (Term .value)} {vs : List Runtime.Val}
    (hhead : t.eval ρ = v)
    (htail : Terms.Eval ρ ts vs) :
    Terms.Eval ρ (t :: ts) (v :: vs) :=
  List.Forall₂.cons hhead htail

theorem Terms.Eval.of_pairs {ρ : Env} {pairs : List (α × Term .value)} {vs : List Runtime.Val}
    (h : List.Forall₂ (fun p v => p.2.eval ρ = v) pairs vs) :
    Terms.Eval ρ (pairs.map Prod.snd) vs := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons h ih

theorem Terms.Eval.lookup_var {ρ : Env} {avs : List Var} {vs : List Runtime.Val}
    (h : Terms.Eval ρ (avs.map (fun av => .var .value av.name)) vs) :
    List.Forall₂ (fun av val => ρ.lookupConst .value av.name = val) avs vs := by
  generalize hts : avs.map (fun av => Term.var .value av.name) = ts at h
  induction h generalizing avs with
  | nil =>
    cases avs with
    | nil => exact .nil
    | cons _ _ => simp at hts
  | cons hhead htail ih =>
    cases avs with
    | nil => simp at hts
    | cons av avs' =>
      simp only [List.map_cons, List.cons.injEq] at hts
      obtain ⟨rfl, rfl⟩ := hts
      constructor
      · exact hhead
      · exact ih rfl

theorem Terms.Eval.lookup_const {ρ : Env} {avs : List FOL.Const} {vs : List Runtime.Val}
    (h : Terms.Eval ρ (avs.map (fun av => .const (.uninterpreted av.name .value))) vs) :
    List.Forall₂ (fun av val => ρ.consts .value av.name = val) avs vs := by
  generalize hts : avs.map (fun av => Term.const (.uninterpreted av.name .value)) = ts at h
  induction h generalizing avs with
  | nil =>
    cases avs with
    | nil => exact .nil
    | cons _ _ => simp at hts
  | cons hhead htail ih =>
    cases avs with
    | nil => simp at hts
    | cons av avs' =>
      simp only [List.map_cons, List.cons.injEq] at hts
      obtain ⟨rfl, rfl⟩ := hts
      constructor
      · simp [Term.eval, Const.denote] at hhead; exact hhead
      · exact ih rfl
