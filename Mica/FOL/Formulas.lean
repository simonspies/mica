-- SUMMARY: First-order formulas together with their Tarski semantics and well-formedness conditions.
import Mica.FOL.Terms
import Mica.Base.Except

inductive UnPred : Srt → Type where
  | isInt   : UnPred .value
  | isBool  : UnPred .value
  | isLoc   : UnPred .value
  | isTuple : UnPred .value
  | isInj (tag : Nat) (arity : Nat) : UnPred .value
  | uninterpreted : String → (τ : Srt) → UnPred τ
  deriving DecidableEq, Repr

inductive BinPred : Srt → Srt → Type where
  | lt : BinPred .int .int
  | le : BinPred .int .int
  | uninterpreted : String → (τ₁ τ₂ : Srt) → BinPred τ₁ τ₂
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

def UnPred.wfIn : UnPred τ → Signature → Prop
  | .uninterpreted name τ, Δ => ⟨name, τ⟩ ∈ Δ.unaryRel
  | _, _                      => True

def BinPred.wfIn : BinPred τ₁ τ₂ → Signature → Prop
  | .uninterpreted name τ₁ τ₂, Δ => ⟨name, τ₁, τ₂⟩ ∈ Δ.binaryRel
  | _, _                          => True

def UnPred.checkWf : UnPred τ → Signature → Except String Unit
  | .uninterpreted name τ, Δ =>
    if ⟨name, τ⟩ ∈ Δ.unaryRel then .ok () else .error s!"unary predicate {name} not in signature"
  | _, _ => .ok ()

def BinPred.checkWf : BinPred τ₁ τ₂ → Signature → Except String Unit
  | .uninterpreted name τ₁ τ₂, Δ =>
    if ⟨name, τ₁, τ₂⟩ ∈ Δ.binaryRel then .ok () else .error s!"binary predicate {name} not in signature"
  | _, _ => .ok ()

def Formula.wfIn : Formula → Signature → Prop
  | .true_, _            => True
  | .false_, _           => True
  | .eq _ t₁ t₂, Δ      => t₁.wfIn Δ ∧ t₂.wfIn Δ
  | .unpred p t, Δ       => p.wfIn Δ ∧ t.wfIn Δ
  | .binpred p t₁ t₂, Δ => p.wfIn Δ ∧ t₁.wfIn Δ ∧ t₂.wfIn Δ
  | .not φ, Δ            => φ.wfIn Δ
  | .and φ ψ, Δ          => φ.wfIn Δ ∧ ψ.wfIn Δ
  | .or φ ψ, Δ           => φ.wfIn Δ ∧ ψ.wfIn Δ
  | .implies φ ψ, Δ      => φ.wfIn Δ ∧ ψ.wfIn Δ
  | .forall_ x τ φ, Δ    => φ.wfIn (Δ.declVar ⟨x, τ⟩)
  | .exists_ x τ φ, Δ    => φ.wfIn (Δ.declVar ⟨x, τ⟩)

def Formula.checkWf : Formula → Signature → Except String Unit
  | .true_, _            => .ok ()
  | .false_, _           => .ok ()
  | .eq _ t₁ t₂, Δ      => do t₁.checkWf Δ; t₂.checkWf Δ
  | .unpred p t, Δ       => do p.checkWf Δ; t.checkWf Δ
  | .binpred p t₁ t₂, Δ => do p.checkWf Δ; t₁.checkWf Δ; t₂.checkWf Δ
  | .not φ, Δ            => φ.checkWf Δ
  | .and φ ψ, Δ          => do φ.checkWf Δ; ψ.checkWf Δ
  | .or φ ψ, Δ           => do φ.checkWf Δ; ψ.checkWf Δ
  | .implies φ ψ, Δ      => do φ.checkWf Δ; ψ.checkWf Δ
  | .forall_ x τ φ, Δ    => φ.checkWf (Δ.declVar ⟨x, τ⟩)
  | .exists_ x τ φ, Δ    => φ.checkWf (Δ.declVar ⟨x, τ⟩)

private theorem UnPred.checkWf_ok {p : UnPred τ} {Δ : Signature}
    (h : p.checkWf Δ = .ok ()) : p.wfIn Δ := by
  cases p with
  | uninterpreted name τ =>
    simp only [UnPred.checkWf] at h
    split at h
    · assumption
    · simp at h
  | _ => trivial

private theorem BinPred.checkWf_ok {p : BinPred τ₁ τ₂} {Δ : Signature}
    (h : p.checkWf Δ = .ok ()) : p.wfIn Δ := by
  cases p with
  | uninterpreted name τ₁ τ₂ =>
    simp only [BinPred.checkWf] at h
    split at h
    · assumption
    · simp at h
  | _ => trivial

theorem Formula.checkWf_ok {φ : Formula} {Δ : Signature} (h : φ.checkWf Δ = .ok ()) : φ.wfIn Δ := by
  induction φ generalizing Δ with
  | true_ | false_ => trivial
  | eq _ t₁ t₂ =>
    simp only [Formula.checkWf] at h
    have ⟨_, h1, h2⟩ := Except.bind_ok h
    exact ⟨Term.checkWf_ok h1, Term.checkWf_ok h2⟩
  | unpred p t =>
    simp only [Formula.checkWf] at h
    have ⟨_, hp, ht⟩ := Except.bind_ok h
    exact ⟨UnPred.checkWf_ok hp, Term.checkWf_ok ht⟩
  | binpred p t₁ t₂ =>
    simp only [Formula.checkWf] at h
    have ⟨_, hp, h12⟩ := Except.bind_ok h
    have ⟨_, h1, h2⟩ := Except.bind_ok h12
    exact ⟨BinPred.checkWf_ok hp, Term.checkWf_ok h1, Term.checkWf_ok h2⟩
  | not φ ih => exact ih h
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ | implies φ ψ ihφ ihψ =>
    simp only [Formula.checkWf] at h
    have ⟨_, h1, h2⟩ := Except.bind_ok h
    exact ⟨ihφ h1, ihψ h2⟩
  | forall_ x τ φ ih | exists_ x τ φ ih =>
    simp only [Formula.checkWf] at h
    exact ih h

private theorem UnPred.wfIn_mono {p : UnPred τ} {Δ Δ' : Signature}
    (h : p.wfIn Δ) (hsub : Δ.Subset Δ') : p.wfIn Δ' := by
  cases p with
  | uninterpreted name τ => exact hsub.unaryRel _ h
  | _ => trivial

private theorem BinPred.wfIn_mono {p : BinPred τ₁ τ₂} {Δ Δ' : Signature}
    (h : p.wfIn Δ) (hsub : Δ.Subset Δ') : p.wfIn Δ' := by
  cases p with
  | uninterpreted name τ₁ τ₂ => exact hsub.binaryRel _ h
  | _ => trivial

theorem Formula.wfIn_mono (φ : Formula) (h : φ.wfIn Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) : φ.wfIn Δ' := by
  induction φ generalizing Δ Δ' with
  | true_ | false_ => trivial
  | eq _ t₁ t₂ => exact ⟨Term.wfIn_mono t₁ h.1 hsub hwf, Term.wfIn_mono t₂ h.2 hsub hwf⟩
  | unpred p t => exact ⟨UnPred.wfIn_mono h.1 hsub, Term.wfIn_mono t h.2 hsub hwf⟩
  | binpred p t₁ t₂ =>
    exact ⟨BinPred.wfIn_mono h.1 hsub, Term.wfIn_mono t₁ h.2.1 hsub hwf, Term.wfIn_mono t₂ h.2.2 hsub hwf⟩
  | not φ ih => exact ih h hsub hwf
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ | implies φ ψ ihφ ihψ =>
    exact ⟨ihφ h.1 hsub hwf, ihψ h.2 hsub hwf⟩
  | forall_ x τ φ ih | exists_ x τ φ ih =>
    simp only [Formula.wfIn]
    exact ih h (Signature.Subset.declVar hsub ⟨x, τ⟩) (Signature.wf_declVar hwf)

abbrev Context := List Formula

def Context.wfIn (Γ : Context) (Δ : Signature) : Prop :=
  ∀ φ ∈ Γ, φ.wfIn Δ

theorem Context.wfIn_mono (Γ : Context) (h : Γ.wfIn Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) : Γ.wfIn Δ' :=
  fun φ hφ => Formula.wfIn_mono φ (h φ hφ) hsub hwf

@[simp] def UnPred.eval : Env → UnPred τ → τ.denote → Prop
  | _, .isInt,   v => match v with | .int _ => True | _ => False
  | _, .isBool,  v => match v with | .bool _ => True | _ => False
  | _, .isLoc,   v => match v with | .loc _ => True | _ => False
  | _, .isTuple, v => match v with | .tuple _ => True | _ => False
  | _, .isInj tag arity, v => match v with | .inj t a _ => t = tag ∧ a = arity | _ => False
  | ρ, .uninterpreted name _, v => ρ.unaryRel τ name v

@[simp] def BinPred.eval : Env → BinPred τ₁ τ₂ → τ₁.denote → τ₂.denote → Prop
  | _, .lt, a, b => a < b
  | _, .le, a, b => a ≤ b
  | ρ, .uninterpreted name _ _, a, b => ρ.binaryRel τ₁ τ₂ name a b

def Formula.eval (ρ : Env) : Formula → Prop
  | .true_         => True
  | .false_        => False
  | .eq _τ a b     => a.eval ρ = b.eval ρ
  | .unpred p v    => p.eval ρ (v.eval ρ)
  | .binpred p a b => p.eval ρ (a.eval ρ) (b.eval ρ)
  | .not φ         => ¬ φ.eval ρ
  | .and φ ψ       => φ.eval ρ ∧ ψ.eval ρ
  | .or φ ψ        => φ.eval ρ ∨ ψ.eval ρ
  | .implies φ ψ   => φ.eval ρ → ψ.eval ρ
  | .forall_ x τ φ => ∀ v : τ.denote, φ.eval (ρ.updateConst τ x v)
  | .exists_ x τ φ => ∃ v : τ.denote, φ.eval (ρ.updateConst τ x v)

def entails (Γ : Context) (φ : Formula) : Prop :=
  ∀ ρ : Env, (∀ ψ ∈ Γ, ψ.eval ρ) → φ.eval ρ

theorem Formula.eval_env_agree {φ : Formula} {ρ ρ' : Env} {Δ : Signature} :
    φ.wfIn Δ → Env.agreeOn Δ ρ ρ' → (φ.eval ρ ↔ φ.eval ρ') := by
  intro hwf hagree
  induction φ generalizing Δ ρ ρ' with
  | true_ | false_ => rfl
  | eq τ a b =>
    simp only [Formula.eval]
    rw [Term.eval_env_agree hwf.1 hagree, Term.eval_env_agree hwf.2 hagree]
  | unpred p v =>
    simp only [Formula.eval]
    rw [Term.eval_env_agree hwf.2 hagree]
    cases p with
    | uninterpreted name τ =>
      simp only [UnPred.eval]
      have hrel := hagree.2.2.2.2.1 ⟨name, _⟩ hwf.1
      simp [hrel]
    | _ => rfl
  | binpred p a b =>
    simp only [Formula.eval]
    rw [Term.eval_env_agree hwf.2.1 hagree, Term.eval_env_agree hwf.2.2 hagree]
    cases p with
    | uninterpreted name τ₁ τ₂ =>
      simp only [BinPred.eval]
      have hrel := hagree.2.2.2.2.2 ⟨name, _, _⟩ hwf.1
      simp [hrel]
    | _ => rfl
  | not φ ih =>
    simp only [Formula.eval]; rw [ih hwf hagree]
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ | implies φ ψ ihφ ihψ =>
    simp only [Formula.eval]
    rw [ihφ hwf.1 hagree, ihψ hwf.2 hagree]
  | forall_ x τ φ ih =>
    simp only [Formula.eval]
    constructor <;> intro h v
    · exact (ih hwf (Env.agreeOn_declVar hagree)).mp (h v)
    · exact (ih hwf (Env.agreeOn_declVar hagree)).mpr (h v)
  | exists_ x τ φ ih =>
    simp only [Formula.eval]
    constructor
    · intro ⟨v, hv⟩; exact ⟨v, (ih hwf (Env.agreeOn_declVar hagree)).mp hv⟩
    · intro ⟨v, hv⟩; exact ⟨v, (ih hwf (Env.agreeOn_declVar hagree)).mpr hv⟩

/-- If `t` is wf in `Δ` and `c` is fresh for `Δ`, then `c = t` is wf in `Δ.addConst c`. -/
theorem Formula.eq_wfIn_addConst_of_fresh {Δ : Signature} {c : FOL.Const}
    {t : Term c.sort} (hΔwf : Δ.wf) (ht : t.wfIn Δ)
    (hfresh : c.name ∉ Δ.allNames) :
    (Formula.eq c.sort (.const (.uninterpreted c.name c.sort)) t).wfIn (Δ.addConst c) :=
  ⟨Term.const_wfIn_addConst_of_fresh hΔwf hfresh,
   Term.wfIn_mono t ht (Signature.Subset.subset_addConst _ _)
     (Signature.wf_addConst hΔwf hfresh)⟩

/-- Updating the env at a fresh name makes the equality `c = t` hold. -/
theorem Formula.eq_eval_updateConst_of_fresh {Δ : Signature} {ρ : Env}
    {c : FOL.Const} {t : Term c.sort} (ht : t.wfIn Δ)
    (hfresh : c.name ∉ Δ.allNames) :
    (Formula.eq c.sort (.const (.uninterpreted c.name c.sort)) t).eval
      (ρ.updateConst c.sort c.name (t.eval ρ)) := by
  simp only [Formula.eval, Term.eval_const_updateConst]
  exact Term.eval_env_agree ht (Env.agreeOn_update_fresh_const hfresh)


/-- A single-argument named predicate, represented as `(argName, body)`.

Used by the verifier's predicate-transformer layer to carry binder names for
human-readable output while keeping the body representation generic over `α`. -/
def Pred α      := String × α

/-- A multi-argument named predicate, represented as `(argNames, body)`.

This is the n-ary generalization of `Pred`, used for specification predicates
whose printed form is `λ x₁ x₂ … -> body`. -/
def MultiPred α := List String × α
