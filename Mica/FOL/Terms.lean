-- SUMMARY: Typed first-order terms, their Tarski semantics, and their well-formedness conditions.
import Mica.FOL.Env
import Mica.Base.FloatBits
import Mica.Base.Except
import Batteries.Data.List.Basic
import Mathlib.Tactic.SplitIfs

/-!
# Terms

A term is a variable, a constant, or an operation on terms. Each term has a
sort. A term is well-formed in a signature when the signature declares each
name that the term uses, with the sorts that the term uses. The value of a term
depends on an environment.
-/

/-! ## Syntax -/

inductive UnOp : Srt → Srt → Type where
  | ofInt         : UnOp .int     .value
  | ofBool        : UnOp .bool    .value
  | ofInt32       : UnOp (.bv 32) .value
  | ofInt64       : UnOp (.bv 64) .value
  | ofChar        : UnOp .char    .value
  | ofString      : UnOp .string  .value
  | ofFloat       : UnOp .float   .value
  | toInt         : UnOp .value   .int
  | toBool        : UnOp .value   .bool
  | toInt32       : UnOp .value   (.bv 32)
  | toInt64       : UnOp .value   (.bv 64)
  | toChar        : UnOp .value   .char
  | toString      : UnOp .value   .string
  | toFloat       : UnOp .value   .float
  | charToInt     : UnOp .char    .int
  | intToChar     : UnOp .int     .char
  | intToBv       : (width : Nat) → UnOp .int (.bv width)
  | bvToNat       : (width : Nat) → UnOp (.bv width) .int
  | bvNeg         : (width : Nat) → UnOp (.bv width) (.bv width)
  | bvNot         : (width : Nat) → UnOp (.bv width) (.bv width)
  | bvSignExtend  : (width result : Nat) → (le : width ≤ result) → UnOp (.bv width) (.bv result)
  | bvExtractLsb  : (width result : Nat) → (le : result ≤ width) → UnOp (.bv width) (.bv result)
  | seqLen        : UnOp .string  .int
  | fpAbs         : UnOp .float   .float
  | fpNeg         : UnOp .float   .float
  | fpSqrt        : UnOp .float   .float
  | fpIsNaN       : UnOp .float   .bool
  | fpIsInfinite  : UnOp .float   .bool
  | fpIsNegative  : UnOp .float   .bool
  | fpOfInt       : UnOp .int     .float
  | neg           : UnOp .int     .int
  | not           : UnOp .bool    .bool
  | ofValList     : UnOp .vallist .value
  | toValList     : UnOp .value   .vallist
  | arrayLen      : UnOp .value   .int
  | vhead         : UnOp .vallist .value
  | vtail         : UnOp .vallist .vallist
  | visnil        : UnOp .vallist .bool
  | ofInj         : (tag arity : Nat) → UnOp .value .value
  | tagOf         : UnOp .value   .int
  | arityOf       : UnOp .value   .int
  | payloadOf     : UnOp .value   .value
  | vecLen        : UnOp .vec     .int
  | ofVec         : UnOp .vec     .value
  | toVec         : UnOp .value   .vec
  | uninterpreted : String → (τ₁ τ₂ : Srt) → UnOp τ₁ τ₂
  deriving DecidableEq, Repr

inductive BinOp : Srt → Srt → Srt → Type where
  | add           : BinOp .int    .int     .int
  | sub           : BinOp .int    .int     .int
  | mul           : BinOp .int    .int     .int
  | div           : BinOp .int    .int     .int
  | mod           : BinOp .int    .int     .int
  | less          : BinOp .int    .int     .bool
  | gt            : BinOp .int    .int     .bool
  | ge            : BinOp .int    .int     .bool
  | eq            : BinOp τ       τ        .bool
  | bvAdd         : (width : Nat) → BinOp (.bv width) (.bv width) (.bv width)
  | bvSub         : (width : Nat) → BinOp (.bv width) (.bv width) (.bv width)
  | bvMul         : (width : Nat) → BinOp (.bv width) (.bv width) (.bv width)
  | bvSDiv        : (width : Nat) → BinOp (.bv width) (.bv width) (.bv width)
  | bvUDiv        : (width : Nat) → BinOp (.bv width) (.bv width) (.bv width)
  | bvSRem        : (width : Nat) → BinOp (.bv width) (.bv width) (.bv width)
  | bvURem        : (width : Nat) → BinOp (.bv width) (.bv width) (.bv width)
  | bvAnd         : (width : Nat) → BinOp (.bv width) (.bv width) (.bv width)
  | bvOr          : (width : Nat) → BinOp (.bv width) (.bv width) (.bv width)
  | bvXor         : (width : Nat) → BinOp (.bv width) (.bv width) (.bv width)
  | bvSLt         : (width : Nat) → BinOp (.bv width) (.bv width) .bool
  | bvULt         : (width : Nat) → BinOp (.bv width) (.bv width) .bool
  | bvShl         : (width : Nat) → BinOp (.bv width) (.bv width) (.bv width)
  | bvAShr        : (width : Nat) → BinOp (.bv width) (.bv width) (.bv width)
  | bvLShr        : (width : Nat) → BinOp (.bv width) (.bv width) (.bv width)
  | seqConcat     : BinOp .string .string  .string
  | seqNth        : BinOp .string .int     .char
  | seqPrefixOf   : BinOp .string .string  .bool
  | seqSuffixOf   : BinOp .string .string  .bool
  | fpAdd         : BinOp .float  .float   .float
  | fpSub         : BinOp .float  .float   .float
  | fpMul         : BinOp .float  .float   .float
  | fpDiv         : BinOp .float  .float   .float
  | fpEq          : BinOp .float  .float   .bool
  | fpLt          : BinOp .float  .float   .bool
  | fpLe          : BinOp .float  .float   .bool
  | vcons         : BinOp .value  .vallist .vallist
  | vecGet        : BinOp .vec    .int     .value
  | vecMake       : BinOp .int    .value   .vec
  | uninterpreted : String → (τ₁ τ₂ τ₃ : Srt) → BinOp τ₁ τ₂ τ₃
  deriving DecidableEq, Repr

inductive TerOp : Srt → Srt → Srt → Srt → Type where
  | seqExtract    : TerOp .string .int .int   .string
  | vecSet        : TerOp .vec    .int .value .vec
  | uninterpreted : String → (τ₁ τ₂ τ₃ τ₄ : Srt) → TerOp τ₁ τ₂ τ₃ τ₄
  deriving DecidableEq, Repr

inductive Const : Srt → Type where
  | i             : Int → Const .int
  | b             : Bool → Const .bool
  | bv            : BitVec width → Const (.bv width)
  | char          : UInt8 → Const .char
  | str           : List UInt8 → Const .string
  | fp            : UInt64 → Const .float
  | fpNaN         : Const .float
  | fpPosInf      : Const .float
  | fpNegInf      : Const .float
  | unit          : Const .value
  | vnil          : Const .vallist
  | uninterpreted : String → (τ : Srt) → Const τ
  deriving DecidableEq, Repr

inductive Term : Srt → Type where
  | var   : (τ : Srt) → String → Term τ
  | const : Const τ → Term τ
  | unop  : UnOp τ₁ τ₂ → Term τ₁ → Term τ₂
  | binop : BinOp τ₁ τ₂ τ₃ → Term τ₁ → Term τ₂ → Term τ₃
  | terop : TerOp τ₁ τ₂ τ₃ τ₄ → Term τ₁ → Term τ₂ → Term τ₃ → Term τ₄
  | ite   : Term .bool → Term τ → Term τ → Term τ
  deriving DecidableEq

/-! ## Names -/

def Term.freeVars : Term τ → List Var
  | .var τ y   => [⟨y, τ⟩]
  | .const _   => []
  | .unop _ a  => a.freeVars
  | .binop _ a b => a.freeVars ++ b.freeVars
  | .terop _ a b c => a.freeVars ++ b.freeVars ++ c.freeVars
  | .ite c t e => c.freeVars ++ t.freeVars ++ e.freeVars

/-- All names that the term uses, including the symbols. `freeVars` gives only
the variables. A binder with a name outside this list cannot capture a name of
the term. -/
def Term.names : Term τ → List String
  | .var _ x => [x]
  | .const (.uninterpreted name _) => [name]
  | .const _ => []
  | .unop (.uninterpreted name _ _) a => name :: a.names
  | .unop _ a => a.names
  | .binop (.uninterpreted name _ _ _) a b => name :: (a.names ++ b.names)
  | .binop _ a b => a.names ++ b.names
  | .terop (.uninterpreted name _ _ _ _) a b c => name :: (a.names ++ b.names ++ c.names)
  | .terop _ a b c => a.names ++ b.names ++ c.names
  | .ite c t e => c.names ++ t.names ++ e.names

/-! ## Well-formedness -/

def Const.wfIn : Const τ → Signature → Prop
  | .uninterpreted name τ, Δ => ⟨name, τ⟩ ∈ Δ.consts
                               ∧ (∀ τ', ⟨name, τ'⟩ ∉ Δ.vars)
                               ∧ (∀ τ', ⟨name, τ'⟩ ∈ Δ.consts → τ' = τ)
  | _, _                     => True

def UnOp.wfIn : UnOp τ₁ τ₂ → Signature → Prop
  | .uninterpreted name τ₁ τ₂, Δ => ⟨name, τ₁, τ₂⟩ ∈ Δ.unary
                                   ∧ (∀ τ', ⟨name, τ'⟩ ∉ Δ.unaryRel)
                                   ∧ (∀ τ₁' τ₂', ⟨name, τ₁', τ₂'⟩ ∈ Δ.unary →
                                       τ₁' = τ₁ ∧ τ₂' = τ₂)
  | _, _                          => True

def BinOp.wfIn : BinOp τ₁ τ₂ τ₃ → Signature → Prop
  | .uninterpreted name τ₁ τ₂ τ₃, Δ => ⟨name, τ₁, τ₂, τ₃⟩ ∈ Δ.binary
                                      ∧ (∀ τ₁' τ₂', ⟨name, τ₁', τ₂'⟩ ∉ Δ.binaryRel)
                                      ∧ (∀ τ₁' τ₂' τ₃', ⟨name, τ₁', τ₂', τ₃'⟩ ∈ Δ.binary →
                                          τ₁' = τ₁ ∧ τ₂' = τ₂ ∧ τ₃' = τ₃)
  | _, _                              => True

def TerOp.wfIn : TerOp τ₁ τ₂ τ₃ τ₄ → Signature → Prop
  | .uninterpreted name τ₁ τ₂ τ₃ τ₄, Δ =>
      ⟨name, τ₁, τ₂, τ₃, τ₄⟩ ∈ Δ.ternary
      ∧ (∀ τ₁' τ₂' τ₃' τ₄', ⟨name, τ₁', τ₂', τ₃', τ₄'⟩ ∈ Δ.ternary →
          τ₁' = τ₁ ∧ τ₂' = τ₂ ∧ τ₃' = τ₃ ∧ τ₄' = τ₄)
  | _, _ => True

def Term.wfIn : Term τ → Signature → Prop
  | .var τ x, Δ     => ⟨x, τ⟩ ∈ Δ.vars
                     ∧ (∀ τ', ⟨x, τ'⟩ ∉ Δ.consts)
                     ∧ (∀ τ', ⟨x, τ'⟩ ∈ Δ.vars → τ' = τ)
  | .const c, Δ     => c.wfIn Δ
  | .unop op a, Δ   => op.wfIn Δ ∧ a.wfIn Δ
  | .binop op a b, Δ => op.wfIn Δ ∧ a.wfIn Δ ∧ b.wfIn Δ
  | .terop op a b c, Δ => op.wfIn Δ ∧ a.wfIn Δ ∧ b.wfIn Δ ∧ c.wfIn Δ
  | .ite c t e, Δ   => c.wfIn Δ ∧ t.wfIn Δ ∧ e.wfIn Δ

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
    (hsub : Δ.Subset Δ') (hwf : Δ'.wf) : op.wfIn Δ' := by
  cases op with
  | uninterpreted name τ₁ τ₂ =>
    refine ⟨hsub.unary _ h.1, ?_, ?_⟩
    · intro τ' hrel
      exact Signature.wf_no_unaryRel_of_unary hwf (hsub.unary _ h.1) hrel
    · intro τ₁' τ₂' hu'
      exact Signature.wf_unique_unary hwf (hsub.unary _ h.1) hu'
  | _ => trivial

private theorem BinOp.wfIn_mono {op : BinOp τ₁ τ₂ τ₃} {Δ Δ' : Signature} (h : op.wfIn Δ)
    (hsub : Δ.Subset Δ') (hwf : Δ'.wf) : op.wfIn Δ' := by
  cases op with
  | uninterpreted name τ₁ τ₂ τ₃ =>
    refine ⟨hsub.binary _ h.1, ?_, ?_⟩
    · intro τ₁' τ₂' hrel
      exact Signature.wf_no_binaryRel_of_binary hwf (hsub.binary _ h.1) hrel
    · intro τ₁' τ₂' τ₃' hb'
      exact Signature.wf_unique_binary hwf (hsub.binary _ h.1) hb'
  | _ => trivial

private theorem TerOp.wfIn_mono {op : TerOp τ₁ τ₂ τ₃ τ₄} {Δ Δ' : Signature}
    (h : op.wfIn Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) : op.wfIn Δ' := by
  cases op with
  | seqExtract => trivial
  | uninterpreted name τ₁ τ₂ τ₃ τ₄ =>
    refine ⟨hsub.ternary _ h.1, ?_⟩
    intro τ₁' τ₂' τ₃' τ₄' ht'
    exact Signature.wf_unique_ternary hwf (hsub.ternary _ h.1) ht'
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
  | unop op a iha => exact ⟨UnOp.wfIn_mono h.1 hsub hwf, iha h.2 hsub hwf⟩
  | binop op a b iha ihb =>
    exact ⟨BinOp.wfIn_mono h.1 hsub hwf, iha h.2.1 hsub hwf, ihb h.2.2 hsub hwf⟩
  | terop op a b c iha ihb ihc =>
    exact ⟨TerOp.wfIn_mono h.1 hsub hwf, iha h.2.1 hsub hwf, ihb h.2.2.1 hsub hwf,
      ihc h.2.2.2 hsub hwf⟩
  | ite c t e ihc iht ihe => exact ⟨ihc h.1 hsub hwf, iht h.2.1 hsub hwf, ihe h.2.2 hsub hwf⟩

theorem Term.wfIn_declVar_of_fresh {t : Term τ} {x : String} {s : Srt}
    { Δ : Signature } (h : t.wfIn Δ) (hx : x ∉ t.names) :
    t.wfIn (Δ.declVar ⟨x, s⟩) := by
  induction t generalizing Δ with
  | var τ y =>
    have hne : y ≠ x := by simpa [Term.names, ne_eq, eq_comm] using hx
    simpa [Term.wfIn, Signature.declVar, Signature.addVar, Signature.remove, hne] using h
  | const c =>
    cases c with
    | uninterpreted name τ =>
      have hne : name ≠ x := by simpa [Term.names, ne_eq, eq_comm] using hx
      simpa [Term.wfIn, Const.wfIn, Signature.declVar, Signature.addVar,
        Signature.remove, hne] using h
    | _ => trivial
  | unop op a ih =>
    cases op with
    | uninterpreted name τ₁ τ₂ =>
      simp only [Term.names, List.mem_cons, not_or] at hx
      refine ⟨?_, ih h.2 hx.2⟩
      simpa [UnOp.wfIn, Signature.declVar, Signature.addVar, Signature.remove, Ne.symm hx.1]
        using h.1
    | _ => exact ⟨trivial, ih h.2 (by simpa [Term.names] using hx)⟩
  | binop op a b iha ihb =>
    cases op with
    | uninterpreted name τ₁ τ₂ τ₃ =>
      simp only [Term.names, List.mem_cons, List.mem_append, not_or] at hx
      refine ⟨?_, iha h.2.1 hx.2.1, ihb h.2.2 hx.2.2⟩
      simpa [BinOp.wfIn, Signature.declVar, Signature.addVar, Signature.remove, Ne.symm hx.1]
        using h.1
    | _ =>
      simp only [Term.names, List.mem_append, not_or] at hx
      exact ⟨trivial, iha h.2.1 hx.1, ihb h.2.2 hx.2⟩
  | terop op a b c iha ihb ihc =>
    cases op with
    | uninterpreted name τ₁ τ₂ τ₃ τ₄ =>
      simp only [Term.names, List.mem_cons, List.mem_append, not_or] at hx
      refine ⟨?_, iha h.2.1 hx.2.1.1, ihb h.2.2.1 hx.2.1.2, ihc h.2.2.2 hx.2.2⟩
      simpa [TerOp.wfIn, Signature.declVar, Signature.addVar, Signature.remove, Ne.symm hx.1]
        using h.1
    | _ =>
      simp only [Term.names, List.mem_append, not_or] at hx
      exact ⟨trivial, iha h.2.1 hx.1.1, ihb h.2.2.1 hx.1.2, ihc h.2.2.2 hx.2⟩
  | ite c t e ihc iht ihe =>
    simp only [Term.names, List.mem_append, not_or] at hx
    exact ⟨ihc h.1 hx.1.1, iht h.2.1 hx.1.2, ihe h.2.2 hx.2⟩

theorem Term.const_wfIn_of_mem {Δ : Signature} {name : String} {τ : Srt}
    (hwf : Δ.wf) (hmem : ⟨name, τ⟩ ∈ Δ.consts) :
    (Term.const (.uninterpreted name τ)).wfIn Δ :=
  ⟨hmem,
    fun _ hvar => Signature.wf_no_var_of_const hwf hmem hvar,
    fun _ hc' => Signature.wf_unique_const hwf hmem hc'⟩

theorem Term.var_wfIn_declVar {Δ : Signature} {x : String} {τ : Srt}
    (hwf : (Δ.declVar ⟨x, τ⟩).wf) : (Term.var τ x).wfIn (Δ.declVar ⟨x, τ⟩) :=
  ⟨Signature.var_mem_declVar Δ ⟨x, τ⟩,
   fun _ hc => Signature.wf_no_const_of_var hwf (Signature.var_mem_declVar Δ ⟨x, τ⟩) hc,
   fun _ hv => Signature.wf_unique_var hwf (Signature.var_mem_declVar Δ ⟨x, τ⟩) hv⟩

theorem Term.const_wfIn_addConst_of_fresh {Δ : Signature} {c : Decl.Const}
    (hΔwf : Δ.wf) (hfresh : c.name ∉ Δ.allNames) :
    (Term.const (.uninterpreted c.name c.sort)).wfIn (Δ.addConst c) :=
  Term.const_wfIn_of_mem (Signature.wf_addConst hΔwf hfresh) (List.Mem.head _)

/-! ### Checking well-formedness

`checkWf` succeeds only on a well-formed term (`checkWf_ok`). When it fails,
its message names the first problem that it finds. -/

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
    if ⟨name, τ₁, τ₂⟩ ∈ Δ.unary then
      if name ∈ Δ.unaryRel.map Decl.UnaryRel.name then
        .error s!"unary op {name} conflicts with a unary predicate"
      else if Δ.unary.any (fun u => u.name == name && (u.arg != τ₁ || u.ret != τ₂)) then
        .error s!"unary op {name} has multiple signatures in signature"
      else .ok ()
    else .error s!"unary op {name} not in signature"
  | _, _ => .ok ()

def BinOp.checkWf : BinOp τ₁ τ₂ τ₃ → Signature → Except String Unit
  | .uninterpreted name τ₁ τ₂ τ₃, Δ =>
    if ⟨name, τ₁, τ₂, τ₃⟩ ∈ Δ.binary then
      if name ∈ Δ.binaryRel.map Decl.BinaryRel.name then
        .error s!"binary op {name} conflicts with a binary predicate"
      else if Δ.binary.any
          (fun b => b.name == name && (b.arg1 != τ₁ || b.arg2 != τ₂ || b.ret != τ₃)) then
        .error s!"binary op {name} has multiple signatures in signature"
      else .ok ()
    else .error s!"binary op {name} not in signature"
  | _, _ => .ok ()

def TerOp.checkWf : TerOp τ₁ τ₂ τ₃ τ₄ → Signature → Except String Unit
  | .uninterpreted name τ₁ τ₂ τ₃ τ₄, Δ =>
    if ⟨name, τ₁, τ₂, τ₃, τ₄⟩ ∈ Δ.ternary then
      if Δ.ternary.any
          (fun t => t.name == name &&
            (t.arg1 != τ₁ || t.arg2 != τ₂ || t.arg3 != τ₃ || t.ret != τ₄)) then
        .error s!"ternary op {name} has multiple signatures in signature"
      else .ok ()
    else .error s!"ternary op {name} not in signature"
  | _, _ => .ok ()

def Term.checkWf : Term τ → Signature → Except String Unit
  | .var τ x, Δ     =>
    if ⟨x, τ⟩ ∈ Δ.vars then
      if x ∈ Δ.consts.map Decl.Const.name then .error s!"variable {repr x} conflicts with a constant"
      else if Δ.vars.any (fun v => v.name == x && v.sort != τ) then
        .error s!"variable {repr x} has multiple sorts in scope"
      else .ok ()
    else .error s!"variable {repr x} not in scope"
  | .const c, Δ     => c.checkWf Δ
  | .unop op a, Δ   => do op.checkWf Δ; a.checkWf Δ
  | .binop op a b, Δ => do op.checkWf Δ; a.checkWf Δ; b.checkWf Δ
  | .terop op a b c, Δ => do op.checkWf Δ; a.checkWf Δ; b.checkWf Δ; c.checkWf Δ
  | .ite c t e, Δ   => do c.checkWf Δ; t.checkWf Δ; e.checkWf Δ

private theorem Const.checkWf_ok {c : Const τ} {Δ : Signature} (h : c.checkWf Δ = .ok ()) :
    c.wfIn Δ := by
  cases c with
  | uninterpreted name τ =>
    simp only [Const.checkWf] at h
    split_ifs at h with hmem hvar hdup
    simp at hdup
    exact ⟨hmem, fun _ hv => hvar (List.mem_map_of_mem hv), fun _ hc' => hdup _ hc' rfl⟩
  | _ => trivial

private theorem UnOp.checkWf_ok {op : UnOp τ₁ τ₂} {Δ : Signature} (h : op.checkWf Δ = .ok ()) :
    op.wfIn Δ := by
  cases op with
  | uninterpreted name τ₁ τ₂ =>
    simp only [UnOp.checkWf] at h
    split_ifs at h with hmem hpred hdup
    simp at hdup
    exact ⟨hmem, fun _ hrel => hpred (List.mem_map_of_mem hrel), fun _ _ hu' => hdup _ hu' rfl⟩
  | _ => trivial

private theorem BinOp.checkWf_ok {op : BinOp τ₁ τ₂ τ₃} {Δ : Signature}
    (h : op.checkWf Δ = .ok ()) : op.wfIn Δ := by
  cases op with
  | uninterpreted name τ₁ τ₂ τ₃ =>
    simp only [BinOp.checkWf] at h
    split_ifs at h with hmem hpred hdup
    simp [and_assoc] at hdup
    exact ⟨hmem, fun _ _ hrel => hpred (List.mem_map_of_mem hrel), fun _ _ _ hb' => hdup _ hb' rfl⟩
  | _ => trivial

private theorem TerOp.checkWf_ok {op : TerOp τ₁ τ₂ τ₃ τ₄} {Δ : Signature}
    (h : op.checkWf Δ = .ok ()) : op.wfIn Δ := by
  cases op with
  | uninterpreted name τ₁ τ₂ τ₃ τ₄ =>
    simp only [TerOp.checkWf] at h
    split_ifs at h with hmem hdup
    simp [and_assoc] at hdup
    exact ⟨hmem, fun _ _ _ _ ht' => hdup _ ht' rfl⟩
  | _ => trivial

theorem Term.checkWf_ok {t : Term τ} {Δ : Signature} (h : t.checkWf Δ = .ok ()) : t.wfIn Δ := by
  induction t generalizing Δ with
  | var τ x =>
    simp only [Term.checkWf] at h
    split_ifs at h with hmem hconst hdup
    simp at hdup
    exact ⟨hmem, fun _ hc => hconst (List.mem_map_of_mem hc), fun _ hv' => hdup _ hv' rfl⟩
  | const c =>
    simpa [Term.checkWf] using (Const.checkWf_ok h)
  | unop op a iha =>
    simp only [Term.checkWf] at h
    have ⟨_, h1, h2⟩ := Except.bind_ok h
    exact ⟨UnOp.checkWf_ok h1, iha h2⟩
  | binop op a b iha ihb =>
    simp only [Term.checkWf] at h
    have ⟨_, h1, h23⟩ := Except.bind_ok h
    have ⟨_, h2, h3⟩ := Except.bind_ok h23
    exact ⟨BinOp.checkWf_ok h1, iha h2, ihb h3⟩
  | terop op a b c iha ihb ihc =>
    simp only [Term.checkWf] at h
    have ⟨_, h1, h234⟩ := Except.bind_ok h
    have ⟨_, h2, h34⟩ := Except.bind_ok h234
    have ⟨_, h3, h4⟩ := Except.bind_ok h34
    exact ⟨TerOp.checkWf_ok h1, iha h2, ihb h3, ihc h4⟩
  | ite c t e ihc iht ihe =>
    simp only [Term.checkWf] at h
    have ⟨_, h1, h23⟩ := Except.bind_ok h
    have ⟨_, h2, h3⟩ := Except.bind_ok h23
    exact ⟨ihc h1, iht h2, ihe h3⟩

/-! ## Evaluation -/

@[simp] def Const.eval : Env → Const τ → τ.denote
  | _, .i n  => n
  | _, .b v  => v
  | _, .bv bits => bits
  | _, .char c => c
  | _, .str s => s
  | _, .fp bits => bits
  | _, .fpNaN => FloatBits.nan
  | _, .fpPosInf => FloatBits.posInf
  | _, .fpNegInf => FloatBits.negInf
  | _, .unit => Runtime.Val.unit
  | _, .vnil => []
  | ρ, .uninterpreted name _ => ρ.consts τ name

/-- Evaluation is total. An operation outside its domain gives the default value
of its result sort (`0`, `false`, `[]`, `.unit`): for example, a projection of a
value of a different shape, or an index out of range. The solver leaves most of
these cases unspecified, so most defaults can be chosen freely. Where the solver
fixes a default, `SMTLIB.defaults_eval` ensures that it is the same as here. -/
@[simp] def UnOp.eval : Env → UnOp τ₁ τ₂ → τ₁.denote → τ₂.denote
  | _, .ofInt,   n  => Runtime.Val.int n
  | _, .ofBool,  b  => Runtime.Val.bool b
  | _, .ofInt32, bits => Runtime.Val.int32 bits
  | _, .ofInt64, bits => Runtime.Val.int64 bits
  | _, .ofChar,  c  => Runtime.Val.char c
  | _, .ofString, s => Runtime.Val.str s
  | _, .ofFloat, b => Runtime.Val.float b
  | _, .toInt,   v  => match v with | .int n => n | _ => 0
  | _, .toBool,  v  => match v with | .bool b => b | _ => false
  | _, .toInt32, v => match v with | .int32 bits => bits | _ => 0
  | _, .toInt64, v => match v with | .int64 bits => bits | _ => 0
  | _, .toChar,  v  => match v with | .char c => c | _ => 0
  | _, .toString, v => match v with | .str s => s | _ => []
  | _, .toFloat, v => match v with | .float b => b | _ => 0
  | _, .charToInt, c => c.toNat
  | _, .intToChar, n => UInt8.ofNat (Int.toNat (n % 256))
  | _, .intToBv width, n => BitVec.ofInt width n
  | _, .bvToNat _, bits => (bits.toNat : Int)
  | _, .bvNeg _, bits => -bits
  | _, .bvNot _, bits => ~~~bits
  | _, .bvSignExtend _ result _, bits => bits.signExtend result
  | _, .bvExtractLsb _ result _, bits => bits.extractLsb' 0 result
  | _, .seqLen, s => (s.length : Int)
  | _, .fpAbs, a => FloatBits.abs a
  | _, .fpNeg, a => FloatBits.neg a
  | _, .fpSqrt, a => FloatBits.sqrt .nearestTiesToEven a
  | _, .fpIsNaN, a => FloatBits.isNaN a
  | _, .fpIsInfinite, a => FloatBits.isInf a
  | _, .fpIsNegative, a => FloatBits.isNegative a
  | _, .fpOfInt, n => FloatBits.ofInt .nearestTiesToEven n
  | _, .neg,     n  => -n
  | _, .not,     b  => !b
  | _, .ofValList, vs => Runtime.Val.tuple vs
  | _, .toValList, v  => match v with | .tuple vs => vs | _ => []
  | _, .arrayLen, v => match v with | .array len _ => (len : Int) | _ => 0
  | _, .vhead,   vs => vs.headD .unit
  | _, .vtail,   vs => vs.tail
  | _, .visnil,  vs => vs.isEmpty
  | _, .ofInj tag arity, v => Runtime.Val.inj tag arity v
  | _, .tagOf,   v => match v with | .inj tag _ _ => (tag : Int) | _ => 0
  | _, .arityOf, v => match v with | .inj _ arity _ => (arity : Int) | _ => 0
  | _, .payloadOf, v => match v with | .inj _ _ payload => payload | _ => Runtime.Val.unit
  | _, .vecLen,  l => (l.length : Int)
  | _, .ofVec,   l => Runtime.Val.vec l
  | _, .toVec,   v => match v with | .vec l => l | _ => []
  | ρ, .uninterpreted name _ _, x => ρ.unary τ₁ τ₂ name x

/-- Outside its domain, an operation gives a default value, as in `UnOp.eval`. -/
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
  | _, .bvAdd _, a, b => a + b
  | _, .bvSub _, a, b => a - b
  | _, .bvMul _, a, b => a * b
  | _, .bvSDiv _, a, b => a.smtSDiv b
  | _, .bvUDiv _, a, b => a.smtUDiv b
  | _, .bvSRem _, a, b => a.srem b
  | _, .bvURem _, a, b => a.umod b
  | _, .bvAnd _, a, b => a &&& b
  | _, .bvOr _, a, b => a ||| b
  | _, .bvXor _, a, b => a ^^^ b
  | _, .bvSLt _, a, b => a.slt b
  | _, .bvULt _, a, b => a.ult b
  | _, .bvShl _, a, b => a <<< b
  | _, .bvAShr _, a, b => a.sshiftRight' b
  | _, .bvLShr _, a, b => a >>> b
  | _, .seqConcat, a, b => a ++ b
  | _, .seqNth, s, i => s[Int.toNat i]?.getD 0
  | _, .seqPrefixOf, a, b => a.isPrefixOf b
  | _, .seqSuffixOf, a, b => a.isSuffixOf b
  | _, .fpAdd, a, b => FloatBits.add .nearestTiesToEven a b
  | _, .fpSub, a, b => FloatBits.sub .nearestTiesToEven a b
  | _, .fpMul, a, b => FloatBits.mul .nearestTiesToEven a b
  | _, .fpDiv, a, b => FloatBits.div .nearestTiesToEven a b
  | _, .fpEq, a, b => FloatBits.eq a b
  | _, .fpLt, a, b => FloatBits.lt a b
  | _, .fpLe, a, b => FloatBits.le a b
  | _, .vcons, v, vs => v :: vs
  | _, .vecGet,  l, i => if 0 ≤ i then (l[i.toNat]?).getD .unit else .unit
  | _, .vecMake, n, x => if 0 ≤ n then List.replicate n.toNat x else []
  | ρ, .uninterpreted name _ _ _, x, y => ρ.binary τ₁ τ₂ τ₃ name x y

/-- Outside its domain, an operation gives a default value, as in `UnOp.eval`. -/
@[simp] def TerOp.eval : Env → TerOp τ₁ τ₂ τ₃ τ₄ → τ₁.denote → τ₂.denote → τ₃.denote → τ₄.denote
  | _, .seqExtract, s, pos, len => (s.drop (Int.toNat pos)).take (Int.toNat len)
  | _, .vecSet, l, i, x => if 0 ≤ i then l.set i.toNat x else l
  | ρ, .uninterpreted name _ _ _ _, x, y, z => ρ.ternary τ₁ τ₂ τ₃ τ₄ name x y z

def Term.eval (ρ : Env) : Term τ → τ.denote
  | .var τ y      => ρ.lookupConst τ y
  | .const c      => c.eval ρ
  | .unop op a    => op.eval ρ (Term.eval ρ a)
  | .binop op a b => op.eval ρ (Term.eval ρ a) (Term.eval ρ b)
  | .terop op a b c => op.eval ρ (Term.eval ρ a) (Term.eval ρ b) (Term.eval ρ c)
  | .ite c t e    => bif Term.eval ρ c then Term.eval ρ t else Term.eval ρ e

@[simp] theorem Term.eval_const_updateConst {ρ : Env} {τ : Srt} {x : String}
    {v : τ.denote} :
    (Term.const (.uninterpreted x τ)).eval (ρ.updateConst τ x v) = v := by
  simp [Term.eval, Const.eval, Env.updateConst]

theorem Term.eval_updateConst_of_fresh {t : Term τ'} {x : String} {τ : Srt}
    {v : τ.denote} {ρ : Env} (hx : x ∉ t.names) :
    Term.eval (ρ.updateConst τ x v) t = Term.eval ρ t := by
  induction t with
  | var s y =>
    have hne : y ≠ x := by simpa [Term.names, ne_eq, eq_comm] using hx
    exact Env.lookupConst_updateConst_ne' (Or.inl hne)
  | const c =>
    cases c with
    | uninterpreted name s =>
      have hne : name ≠ x := by simpa [Term.names, ne_eq, eq_comm] using hx
      exact Env.lookupConst_updateConst_ne' (Or.inl hne)
    | _ => rfl
  | unop op a ih =>
    simp only [Term.eval]
    rw [ih (by cases op <;> simp_all [Term.names])]
    cases op <;> rfl
  | binop op a b iha ihb =>
    simp only [Term.eval]
    rw [iha (by cases op <;> simp_all [Term.names]),
      ihb (by cases op <;> simp_all [Term.names])]
    cases op <;> rfl
  | terop op a b c iha ihb ihc =>
    simp only [Term.eval]
    rw [iha (by cases op <;> simp_all [Term.names]),
      ihb (by cases op <;> simp_all [Term.names]),
      ihc (by cases op <;> simp_all [Term.names])]
    cases op <;> rfl
  | ite c t e ihc iht ihe =>
    simp only [Term.names, List.mem_append, not_or] at hx
    simp [Term.eval, ihc hx.1.1, iht hx.1.2, ihe hx.2]

theorem Term.eval_le {τ : Srt} {ρ ρ' : Env} (h : Env.le ρ ρ') (t : Term τ) :
    t.eval ρ = t.eval ρ' := by
  induction t with
  | var τ y => simp [Term.eval, Env.lookupConst, h.consts]
  | const c =>
    cases c <;> simp [Term.eval, Const.eval, h.consts]
  | unop op a iha =>
    simp only [Term.eval]; rw [iha]
    cases op <;> simp [UnOp.eval, h.unary]
  | binop op a b iha ihb =>
    simp only [Term.eval]; rw [iha, ihb]
    cases op <;> simp [BinOp.eval, h.binary]
  | terop op a b c iha ihb ihc =>
    simp only [Term.eval]; rw [iha, ihb, ihc]
    cases op <;> simp [TerOp.eval, h.ternary]
  | ite c t e ihc iht ihe =>
    simp only [Term.eval]; rw [ihc, iht, ihe]

theorem Term.eval_agreeOnTerms {t : Term τ} {ρ₁ ρ₂ : Env} {Δ : Signature} :
    t.wfIn Δ → Env.agreeOnTerms Δ ρ₁ ρ₂ → Term.eval ρ₁ t = Term.eval ρ₂ t := by
  intro hwf hagree
  induction t with
  | var τ y => simp [Term.eval, Env.lookupConst]; exact hagree.vars ⟨y, τ⟩ hwf.1
  | const c =>
    simp only [Term.eval]
    cases c with
    | uninterpreted name _ => exact hagree.consts ⟨name, _⟩ hwf.1
    | _ => rfl
  | unop op a iha =>
    simp only [Term.eval]
    rw [iha hwf.2]
    cases op with
    | uninterpreted name _ _ =>
      simp only [UnOp.eval]
      exact congrFun (hagree.unary ⟨name, _, _⟩ hwf.1.1) _
    | _ => rfl
  | binop op a b iha ihb =>
    simp only [Term.eval]
    rw [iha hwf.2.1, ihb hwf.2.2]
    cases op with
    | uninterpreted name _ _ _ =>
      simp only [BinOp.eval]
      exact congrFun (congrFun (hagree.binary ⟨name, _, _, _⟩ hwf.1.1) _) _
    | _ => rfl
  | terop op a b c iha ihb ihc =>
    simp only [Term.eval]
    rw [iha hwf.2.1, ihb hwf.2.2.1, ihc hwf.2.2.2]
    cases op with
    | uninterpreted name _ _ _ _ =>
      simp only [TerOp.eval]
      exact congrFun (congrFun (congrFun (hagree.ternary ⟨name, _, _, _, _⟩ hwf.1.1) _) _) _
    | _ => rfl
  | ite c t e ihc iht ihe =>
    simp [Term.eval]
    rw [ihc hwf.1, iht hwf.2.1, ihe hwf.2.2]

theorem Term.eval_agreeOn {t : Term τ} {ρ ρ' : Env} {Δ : Signature}
    (hwf : t.wfIn Δ) (hagree : Env.agreeOn Δ ρ ρ') : Term.eval ρ t = Term.eval ρ' t :=
  Term.eval_agreeOnTerms hwf (Env.agreeOnTerms_of_agreeOn hagree)

theorem Term.eval_update_fresh {t : Term τ'} {x : String} {τ : Srt} {v : τ.denote} {ρ : Env}
    {Δ : Signature} (hwf : t.wfIn Δ) (hfresh : x ∉ Δ.allNames) :
    Term.eval (ρ.updateConst τ x v) t = Term.eval ρ t :=
  Term.eval_agreeOn hwf (.intro
    (fun w hw => by
      have hne : w.name ≠ x := by
        intro heq
        exact hfresh (heq ▸ Signature.mem_allNames_of_var hw)
      exact Env.lookupConst_updateConst_ne' (Or.inl hne))
    (fun c hc => by
      have hne : c.name ≠ x := by
        intro heq
        exact hfresh (heq ▸ Signature.mem_allNames_of_const hc)
      exact Env.lookupConst_updateConst_ne' (Or.inl hne))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl))

/-! ## Lists of value terms -/

/-- Each term of `ts` has the value at the same position in `vs`. -/
def Term.evalList (ρ : Env) (ts : List (Term .value)) (vs : List Runtime.Val) : Prop :=
  List.Forall₂ (fun t v => t.eval ρ = v) ts vs

theorem Term.evalList.cons {ρ : Env} {t : Term .value} {v : Runtime.Val}
    {ts : List (Term .value)} {vs : List Runtime.Val}
    (hhead : t.eval ρ = v)
    (htail : Term.evalList ρ ts vs) :
    Term.evalList ρ (t :: ts) (v :: vs) :=
  List.Forall₂.cons hhead htail

theorem Term.evalList.map_eval {ρ : Env} {ts : List (Term .value)} {vs : List Runtime.Val}
    (h : Term.evalList ρ ts vs) : ts.map (fun t => t.eval ρ) = vs := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [h, ih]

theorem Term.evalList_agreeOn {ρ ρ' : Env} {Δ : Signature}
    {ts : List (Term .value)} {vs : List Runtime.Val}
    (hwf : ∀ t ∈ ts, t.wfIn Δ)
    (hagree : Env.agreeOn Δ ρ ρ')
    (h : Term.evalList ρ ts vs) : Term.evalList ρ' ts vs := by
  induction h with
  | nil => exact .nil
  | @cons t v ts' vs' htv _ ih =>
    constructor
    · rw [Term.eval_agreeOn (hwf t (.head _)) (Env.agreeOn_symm hagree)]; exact htv
    · exact ih (fun q hq => hwf q (.tail _ hq))

theorem Term.evalList.lookup_const {ρ : Env} {avs : List Decl.Const} {vs : List Runtime.Val}
    (h : Term.evalList ρ (avs.map (fun av => .const (.uninterpreted av.name .value))) vs) :
    List.Forall₂ (fun av val => ρ.consts .value av.name = val) avs vs := by
  induction avs generalizing vs with
  | nil => cases h; exact .nil
  | cons av avs ih =>
    cases h with
    | cons hhead htail => exact .cons (by simpa [Term.eval] using hhead) (ih htail)

/-! ## Tuples

A tuple is a value that holds a list of values. -/

private def vtailN (t : Term .vallist) : Nat → Term .vallist
  | 0     => t
  | n + 1 => .unop .vtail (vtailN t n)

private theorem vtailN_wfIn {t : Term .vallist} {Δ : Signature} (ht : t.wfIn Δ) (n : Nat) :
    (vtailN t n).wfIn Δ := by
  induction n with
  | zero => simpa [vtailN]
  | succ n ih => simp only [vtailN, Term.wfIn]; exact ⟨trivial, ih⟩

private theorem vtailN_eval (t : Term .vallist) (ρ : Env) :
    ∀ n, (vtailN t n).eval ρ = List.drop n (t.eval ρ)
  | 0 => by simp [vtailN]
  | n + 1 => by
    simp only [vtailN, Term.eval, UnOp.eval, vtailN_eval t ρ n]
    rw [List.tail_drop]

def Term.proj (t : Term .value) (n : Nat) : Term .value :=
  .unop .vhead (vtailN (.unop .toValList t) n)

theorem Term.proj_wfIn {t : Term .value} {Δ : Signature} (ht : t.wfIn Δ) (n : Nat) :
    (t.proj n).wfIn Δ :=
  ⟨trivial, vtailN_wfIn (t := .unop .toValList t) ⟨trivial, ht⟩ n⟩

theorem Term.proj_eval {t : Term .value} {ρ : Env} {vs : List Runtime.Val} {n : Nat}
    {v : Runtime.Val} (ht : t.eval ρ = .tuple vs) (hn : vs[n]? = some v) :
    (t.proj n).eval ρ = v := by
  simp [Term.proj, Term.eval, UnOp.eval, vtailN_eval, ht, hn]

private def toValList : List (Term .value) → Term .vallist
  | [] => .const .vnil
  | t :: ts => .binop .vcons t (toValList ts)

def Term.tuple (ts : List (Term .value)) : Term .value :=
  .unop .ofValList (toValList ts)

theorem Term.tuple_wfIn {ts : List (Term .value)} {Δ : Signature}
    (h : ∀ t ∈ ts, t.wfIn Δ) : (Term.tuple ts).wfIn Δ := by
  refine ⟨trivial, ?_⟩
  induction ts with
  | nil => trivial
  | cons t ts ih =>
    exact ⟨trivial, h t (.head _), ih (fun q hq => h q (.tail _ hq))⟩

theorem Term.tuple_eval {ρ : Env} {ts : List (Term .value)} {vs : List Runtime.Val}
    (h : Term.evalList ρ ts vs) : (Term.tuple ts).eval ρ = .tuple vs := by
  suffices (toValList ts).eval ρ = vs by simp [Term.tuple, Term.eval, UnOp.eval, this]
  induction h with
  | nil => simp [toValList, Term.eval, Const.eval]
  | cons hhead _ ih => simp [toValList, Term.eval, BinOp.eval, hhead, ih]
