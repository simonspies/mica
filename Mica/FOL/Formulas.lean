-- SUMMARY: First-order formulas together with their Tarski semantics and well-formedness conditions.
import Mica.FOL.Terms
import Mica.Base.Except

/-!
# Formulas

A formula states a property of terms. It is built from equations and
predicates with the connectives and the quantifiers of first-order logic. A
formula is well-formed in a signature when its terms are.
-/

/-! ## Syntax -/

inductive UnPred : Srt → Type where
  | isInt   : UnPred .value
  | isBool  : UnPred .value
  | isInt32 : UnPred .value
  | isInt64 : UnPred .value
  | isChar  : UnPred .value
  | isStr   : UnPred .value
  | isFloat : UnPred .value
  | isLoc   : UnPred .value
  | isTuple : UnPred .value
  | isOfInj : UnPred .value
  | isVec   : UnPred .value
  | uninterpreted : String → (τ : Srt) → UnPred τ
  deriving DecidableEq, Repr

inductive BinPred : Srt → Srt → Type where
  | lt : BinPred .int .int
  | le : BinPred .int .int
  | uninterpreted : String → (τ₁ τ₂ : Srt) → BinPred τ₁ τ₂
  deriving DecidableEq, Repr

/-- A trigger for the solver on a universal quantifier. Well-formedness and
substitution treat a pattern as syntax, but evaluation ignores it. -/
inductive Pattern where
  | term    : Term τ → Pattern
  | unpred  : UnPred τ → Term τ → Pattern
  | binpred : BinPred τ₁ τ₂ → Term τ₁ → Term τ₂ → Pattern
  deriving DecidableEq

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
  | forall_ : String → Srt → List Pattern → Formula → Formula
  | exists_ : String → Srt → Formula → Formula
  deriving DecidableEq

/-! ## Derived forms -/

/-- Universal quantifier without SMT triggers. -/
@[simp]
def Formula.all (x : String) (τ : Srt) (body : Formula) : Formula :=
  .forall_ x τ [] body

@[simp]
def Formula.iff (φ ψ : Formula) : Formula :=
  .and (.implies φ ψ) (.implies ψ φ)

/-- Case split on a boolean condition, as two guarded implications. -/
def Formula.iteBool (cond : Term .bool) (φ ψ : Formula) : Formula :=
  .and (.implies (.eq .bool cond (.const (.b true)))  φ)
       (.implies (.eq .bool cond (.const (.b false))) ψ)

@[simp]
def Term.isTrue (t : Term .value) : Formula :=
  .eq .value t (.unop .ofBool (.const (.b true)))

@[simp]
def Term.isFalse (t : Term .value) : Formula :=
  .eq .value t (.unop .ofBool (.const (.b false)))

/-- The definition of the constant `c` as `t`. -/
def Formula.define (c : Decl.Const) (t : Term c.sort) : Formula :=
  .eq c.sort (.const (.uninterpreted c.name c.sort)) t

/-! ## Free variables -/

def Pattern.freeVars : Pattern → List Var
  | .term t => t.freeVars
  | .unpred _ t => t.freeVars
  | .binpred _ a b => a.freeVars ++ b.freeVars

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
  | .forall_ y τ ps φ => (ps.flatMap Pattern.freeVars ++ φ.freeVars).filter (· != ⟨y, τ⟩)
  | .exists_ y τ φ => φ.freeVars.filter (· != ⟨y, τ⟩)

/-! ## Well-formedness -/

def UnPred.wfIn : UnPred τ → Signature → Prop
  | .uninterpreted name τ, Δ => ⟨name, τ⟩ ∈ Δ.unaryRel
                                   ∧ (∀ τ₁ τ₂, ⟨name, τ₁, τ₂⟩ ∉ Δ.unary)
                                   ∧ (∀ τ', ⟨name, τ'⟩ ∈ Δ.unaryRel → τ' = τ)
  | _, _                      => True

def BinPred.wfIn : BinPred τ₁ τ₂ → Signature → Prop
  | .uninterpreted name τ₁ τ₂, Δ => ⟨name, τ₁, τ₂⟩ ∈ Δ.binaryRel
                                      ∧ (∀ τ₁' τ₂' τ₃', ⟨name, τ₁', τ₂', τ₃'⟩ ∉ Δ.binary)
                                      ∧ (∀ τ₁' τ₂', ⟨name, τ₁', τ₂'⟩ ∈ Δ.binaryRel →
                                          τ₁' = τ₁ ∧ τ₂' = τ₂)
  | _, _                          => True

def Pattern.wfIn : Pattern → Signature → Prop
  | .term t, Δ => t.wfIn Δ
  | .unpred p t, Δ => p.wfIn Δ ∧ t.wfIn Δ
  | .binpred p t₁ t₂, Δ => p.wfIn Δ ∧ t₁.wfIn Δ ∧ t₂.wfIn Δ

def Pattern.List.wfIn (ps : List Pattern) (Δ : Signature) : Prop :=
  ∀ p ∈ ps, p.wfIn Δ

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
  | .forall_ x τ ps φ, Δ => Pattern.List.wfIn ps (Δ.declVar ⟨x, τ⟩) ∧ φ.wfIn (Δ.declVar ⟨x, τ⟩)
  | .exists_ x τ φ, Δ    => φ.wfIn (Δ.declVar ⟨x, τ⟩)

theorem UnPred.wfIn_mono {p : UnPred τ} {Δ Δ' : Signature}
    (h : p.wfIn Δ) (hsub : Δ.SymbolSubset Δ') (hwf : Δ'.wf) : p.wfIn Δ' := by
  cases p with
  | uninterpreted name τ =>
    refine ⟨hsub.unaryRel _ h.1, ?_, ?_⟩
    · intro τ₁ τ₂ hu
      exact Signature.wf_no_unaryRel_of_unary hwf hu (hsub.unaryRel _ h.1)
    · intro τ' hu'
      exact Signature.wf_unique_unaryRel hwf (hsub.unaryRel _ h.1) hu'
  | _ => trivial

theorem BinPred.wfIn_mono {p : BinPred τ₁ τ₂} {Δ Δ' : Signature}
    (h : p.wfIn Δ) (hsub : Δ.SymbolSubset Δ') (hwf : Δ'.wf) : p.wfIn Δ' := by
  cases p with
  | uninterpreted name τ₁ τ₂ =>
    refine ⟨hsub.binaryRel _ h.1, ?_, ?_⟩
    · intro τ₁' τ₂' τ₃' hb
      exact Signature.wf_no_binaryRel_of_binary hwf hb (hsub.binaryRel _ h.1)
    · intro τ₁' τ₂' hb'
      exact Signature.wf_unique_binaryRel hwf (hsub.binaryRel _ h.1) hb'
  | _ => trivial

private theorem Pattern.wfIn_mono {p : Pattern} {Δ Δ' : Signature}
    (h : p.wfIn Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) : p.wfIn Δ' := by
  cases p with
  | term t =>
    exact Term.wfIn_mono t h hsub hwf
  | unpred p t =>
    exact ⟨UnPred.wfIn_mono h.1 hsub.symbolSubset hwf, Term.wfIn_mono t h.2 hsub hwf⟩
  | binpred p t₁ t₂ =>
    exact ⟨BinPred.wfIn_mono h.1 hsub.symbolSubset hwf,
      Term.wfIn_mono t₁ h.2.1 hsub hwf,
      Term.wfIn_mono t₂ h.2.2 hsub hwf⟩

private theorem Pattern.List.wfIn_mono {ps : List Pattern} {Δ Δ' : Signature}
    (h : Pattern.List.wfIn ps Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) :
    Pattern.List.wfIn ps Δ' :=
  fun p hp => Pattern.wfIn_mono (h p hp) hsub hwf

theorem Formula.wfIn_mono (φ : Formula) (h : φ.wfIn Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) : φ.wfIn Δ' := by
  induction φ generalizing Δ Δ' with
  | true_ | false_ => trivial
  | eq _ t₁ t₂ => exact ⟨Term.wfIn_mono t₁ h.1 hsub hwf, Term.wfIn_mono t₂ h.2 hsub hwf⟩
  | unpred p t => exact ⟨UnPred.wfIn_mono h.1 hsub.symbolSubset hwf, Term.wfIn_mono t h.2 hsub hwf⟩
  | binpred p t₁ t₂ =>
    exact ⟨BinPred.wfIn_mono h.1 hsub.symbolSubset hwf, Term.wfIn_mono t₁ h.2.1 hsub hwf, Term.wfIn_mono t₂ h.2.2 hsub hwf⟩
  | not φ ih => exact ih h hsub hwf
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ | implies φ ψ ihφ ihψ =>
    exact ⟨ihφ h.1 hsub hwf, ihψ h.2 hsub hwf⟩
  | forall_ x τ ps φ ih =>
    exact ⟨Pattern.List.wfIn_mono h.1 (Signature.Subset.declVar hsub ⟨x, τ⟩) (Signature.wf_declVar hwf),
      ih h.2 (Signature.Subset.declVar hsub ⟨x, τ⟩) (Signature.wf_declVar hwf)⟩
  | exists_ x τ φ ih =>
    exact ih h (Signature.Subset.declVar hsub ⟨x, τ⟩) (Signature.wf_declVar hwf)

theorem Formula.iteBool_wfIn {cond : Term .bool} {φ ψ : Formula} {Δ : Signature}
    (hc : cond.wfIn Δ) (hφ : φ.wfIn Δ) (hψ : ψ.wfIn Δ) :
    (Formula.iteBool cond φ ψ).wfIn Δ := by
  simp [Formula.iteBool, Formula.wfIn, Term.wfIn, Const.wfIn, hc, hφ, hψ]

/-- The definition `c = t` of a constant `c` that is fresh for `Δ` is
well-formed after `c` is declared. -/
theorem Formula.define_wfIn {Δ : Signature} {c : Decl.Const}
    {t : Term c.sort} (hΔwf : Δ.wf) (ht : t.wfIn Δ)
    (hfresh : c.name ∉ Δ.allNames) :
    (Formula.define c t).wfIn (Δ.addConst c) :=
  ⟨Term.const_wfIn_addConst_of_fresh hΔwf hfresh,
   Term.wfIn_mono t ht (Signature.Subset.subset_addConst _ _)
     (Signature.wf_addConst hΔwf hfresh)⟩

/-! ### Checking well-formedness

`checkWf` succeeds only on a well-formed formula (`checkWf_ok`). When it fails,
its message names the first problem that it finds. -/

def UnPred.checkWf : UnPred τ → Signature → Except String Unit
  | .uninterpreted name τ, Δ =>
    if ⟨name, τ⟩ ∈ Δ.unaryRel then
      if Δ.unary.any (·.name == name) then
        .error s!"unary predicate {name} conflicts with a unary operator"
      else if Δ.unaryRel.any (fun u => u.name == name && u.arg != τ) then
        .error s!"unary predicate {name} has multiple signatures in signature"
      else .ok ()
    else .error s!"unary predicate {name} not in signature"
  | _, _ => .ok ()

def BinPred.checkWf : BinPred τ₁ τ₂ → Signature → Except String Unit
  | .uninterpreted name τ₁ τ₂, Δ =>
    if ⟨name, τ₁, τ₂⟩ ∈ Δ.binaryRel then
      if Δ.binary.any (·.name == name) then
        .error s!"binary predicate {name} conflicts with a binary operator"
      else if Δ.binaryRel.any (fun b => b.name == name && (b.arg1 != τ₁ || b.arg2 != τ₂)) then
        .error s!"binary predicate {name} has multiple signatures in signature"
      else .ok ()
    else .error s!"binary predicate {name} not in signature"
  | _, _ => .ok ()

def Pattern.checkWf : Pattern → Signature → Except String Unit
  | .term t, Δ => t.checkWf Δ
  | .unpred p t, Δ => do p.checkWf Δ; t.checkWf Δ
  | .binpred p t₁ t₂, Δ => do p.checkWf Δ; t₁.checkWf Δ; t₂.checkWf Δ

def Pattern.List.checkWf : List Pattern → Signature → Except String Unit
  | [], _ => .ok ()
  | p :: ps, Δ => do p.checkWf Δ; checkWf ps Δ

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
  | .forall_ x τ ps φ, Δ => do Pattern.List.checkWf ps (Δ.declVar ⟨x, τ⟩); φ.checkWf (Δ.declVar ⟨x, τ⟩)
  | .exists_ x τ φ, Δ    => φ.checkWf (Δ.declVar ⟨x, τ⟩)

private theorem UnPred.checkWf_ok {p : UnPred τ} {Δ : Signature}
    (h : p.checkWf Δ = .ok ()) : p.wfIn Δ := by
  cases p with
  | uninterpreted name τ =>
    simp only [UnPred.checkWf] at h
    split_ifs at h with hmem hunary hdup
    simp at hunary hdup
    exact ⟨hmem, fun _ _ hu => hunary _ hu rfl, fun _ hu' => hdup _ hu' rfl⟩
  | _ => trivial

private theorem BinPred.checkWf_ok {p : BinPred τ₁ τ₂} {Δ : Signature}
    (h : p.checkWf Δ = .ok ()) : p.wfIn Δ := by
  cases p with
  | uninterpreted name τ₁ τ₂ =>
    simp only [BinPred.checkWf] at h
    split_ifs at h with hmem hbinary hdup
    simp at hbinary hdup
    exact ⟨hmem, fun _ _ _ hb => hbinary _ hb rfl, fun _ _ hb' => hdup _ hb' rfl⟩
  | _ => trivial

private theorem Pattern.checkWf_ok {p : Pattern} {Δ : Signature}
    (h : p.checkWf Δ = .ok ()) : p.wfIn Δ := by
  cases p with
  | term t =>
    exact Term.checkWf_ok h
  | unpred p t =>
    simp only [Pattern.checkWf] at h
    have ⟨_, hp, ht⟩ := Except.bind_ok h
    exact ⟨UnPred.checkWf_ok hp, Term.checkWf_ok ht⟩
  | binpred p t₁ t₂ =>
    simp only [Pattern.checkWf] at h
    have ⟨_, hp, h12⟩ := Except.bind_ok h
    have ⟨_, h1, h2⟩ := Except.bind_ok h12
    exact ⟨BinPred.checkWf_ok hp, Term.checkWf_ok h1, Term.checkWf_ok h2⟩

private theorem Pattern.List.checkWf_ok {ps : List Pattern} {Δ : Signature}
    (h : Pattern.List.checkWf ps Δ = .ok ()) : Pattern.List.wfIn ps Δ := by
  induction ps with
  | nil => nofun
  | cons p ps ih =>
    simp only [Pattern.List.checkWf] at h
    have ⟨_, hp, hps⟩ := Except.bind_ok h
    intro q hq
    cases hq with
    | head => exact Pattern.checkWf_ok hp
    | tail _ hmem => exact ih hps q hmem

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
  | forall_ x τ ps φ ih =>
    simp only [Formula.checkWf] at h
    have ⟨_, hps, hφ⟩ := Except.bind_ok h
    exact ⟨Pattern.List.checkWf_ok hps, ih hφ⟩
  | exists_ x τ φ ih => exact ih h

/-! ## Contexts -/

/-- The hypotheses of a proof goal. -/
abbrev Context := List Formula

def Context.wfIn (Γ : Context) (Δ : Signature) : Prop :=
  ∀ φ ∈ Γ, φ.wfIn Δ

theorem Context.wfIn_mono (Γ : Context) (h : Γ.wfIn Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) : Γ.wfIn Δ' :=
  fun φ hφ => Formula.wfIn_mono φ (h φ hφ) hsub hwf

/-! ## Evaluation -/

@[simp] def UnPred.eval : Env → UnPred τ → τ.denote → Prop
  | _, .isInt,   v => match v with | .int _ => True | _ => False
  | _, .isBool,  v => match v with | .bool _ => True | _ => False
  | _, .isInt32, v => match v with | .int32 _ => True | _ => False
  | _, .isInt64, v => match v with | .int64 _ => True | _ => False
  | _, .isChar,  v => match v with | .char _ => True | _ => False
  | _, .isStr,   v => match v with | .str _ => True | _ => False
  | _, .isFloat, v => match v with | .float _ => True | _ => False
  | _, .isLoc,   v => match v with | .loc _ => True | _ => False
  | _, .isTuple, v => match v with | .tuple _ => True | _ => False
  | _, .isOfInj, v => match v with | .inj _ _ _ => True | _ => False
  | _, .isVec,   v => match v with | .vec _ => True | _ => False
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
  | .forall_ x τ _ φ => ∀ v : τ.denote, φ.eval (ρ.updateConst τ x v)
  | .exists_ x τ φ => ∃ v : τ.denote, φ.eval (ρ.updateConst τ x v)

theorem Formula.eval_agreeOn {φ : Formula} {ρ ρ' : Env} {Δ : Signature} :
    φ.wfIn Δ → Env.agreeOn Δ ρ ρ' → (φ.eval ρ ↔ φ.eval ρ') := by
  intro hwf hagree
  induction φ generalizing Δ ρ ρ' with
  | true_ | false_ => rfl
  | eq τ a b =>
    simp only [Formula.eval]
    rw [Term.eval_agreeOn hwf.1 hagree, Term.eval_agreeOn hwf.2 hagree]
  | unpred p v =>
    simp only [Formula.eval]
    rw [Term.eval_agreeOn hwf.2 hagree]
    cases p with
    | uninterpreted name τ =>
      simp only [UnPred.eval]
      have hrel := hagree.unaryRel ⟨name, _⟩ hwf.1.1
      simp [hrel]
    | _ => rfl
  | binpred p a b =>
    simp only [Formula.eval]
    rw [Term.eval_agreeOn hwf.2.1 hagree, Term.eval_agreeOn hwf.2.2 hagree]
    cases p with
    | uninterpreted name τ₁ τ₂ =>
      simp only [BinPred.eval]
      have hrel := hagree.binaryRel ⟨name, _, _⟩ hwf.1.1
      simp [hrel]
    | _ => rfl
  | not φ ih =>
    simp only [Formula.eval]; rw [ih hwf hagree]
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ | implies φ ψ ihφ ihψ =>
    simp only [Formula.eval]
    rw [ihφ hwf.1 hagree, ihψ hwf.2 hagree]
  | forall_ x τ ps φ ih =>
    exact forall_congr' fun _ => ih hwf.2 (Env.agreeOn_declVar hagree)
  | exists_ x τ φ ih =>
    exact exists_congr fun _ => ih hwf (Env.agreeOn_declVar hagree)

/-- The definition `c = t` of a fresh constant `c` holds when `c` has the value
of `t`. -/
theorem Formula.define_eval {Δ : Signature} {ρ : Env}
    {c : Decl.Const} {t : Term c.sort} (ht : t.wfIn Δ)
    (hfresh : c.name ∉ Δ.allNames) :
    (Formula.define c t).eval (ρ.updateConst c.sort c.name (t.eval ρ)) := by
  simp only [Formula.define, Formula.eval, Term.eval_const_updateConst]
  exact Term.eval_agreeOn ht (Env.agreeOn_update_fresh_const hfresh)
