-- SUMMARY: Native-bitvector `Int32` and `Int64` intrinsics and their soundness instances.
import Mica.Stdlib.Combinators

open Iris Iris.BI

namespace Stdlib

open Verifier

namespace Intrinsics

/-- One fixed-width integer family: how `BitVec width` sits inside `Runtime.Val`,
    together with the FOL coercions that mirror it. `name` prefixes the
    intrinsic names and `module` is the OCaml module that holds the members. -/
private structure Fixed where
  width : Nat
  name : String
  module : String
  typ : TinyML.SchemaTyp
  isOf : UnPred .value
  inject : BitVec width → Runtime.Val
  project : Runtime.Val → BitVec width
  ofBits : Term (.bv width) → Term .value
  toBits : Term .value → Term (.bv width)

/-- The embedding of the family, spelled as a literal so that `emb.carrier`
    reduces to `BitVec fx.width` for a variable `fx`. Builder fields such as
    `Pure.Binary.f` are typed by that projection, so a width-polymorphic
    builder needs it to reduce. -/
private def Fixed.emb (fx : Fixed) : Embedding :=
  ⟨fx.typ, BitVec fx.width, fx.inject, fx.project, fun _ _ _ => iprop(emp), some fx.isOf⟩

private structure Fixed.Lawful (fx : Fixed) where
  embL : fx.emb.Lawful
  ofWf : ∀ {Δ : Signature} {bits : Term (.bv fx.width)},
    bits.wfIn Δ → (fx.ofBits bits).wfIn Δ
  toWf : ∀ {Δ : Signature} {value : Term .value},
    value.wfIn Δ → (fx.toBits value).wfIn Δ
  ofEval : ∀ ρ bits, Term.eval ρ (fx.ofBits bits) = fx.inject (Term.eval ρ bits)
  toEval : ∀ ρ value, Term.eval ρ (fx.toBits value) = fx.project (Term.eval ρ value)

private def fixed32 : Fixed where
  width := 32
  name := "int32"
  module := "Int32"
  typ := .int32
  isOf := .isInt32
  inject := .int32
  project := valInt32
  ofBits := (.unop .ofInt32 ·)
  toBits := (.unop .toInt32 ·)

private def fixed64 : Fixed where
  width := 64
  name := "int64"
  module := "Int64"
  typ := .int64
  isOf := .isInt64
  inject := .int64
  project := valInt64
  ofBits := (.unop .ofInt64 ·)
  toBits := (.unop .toInt64 ·)

private def fixed32Lawful : fixed32.Lawful where
  embL := Embedding.lawfulInt32
  ofWf h := ⟨trivial, h⟩
  toWf h := ⟨trivial, h⟩
  ofEval _ _ := rfl
  toEval ρ value := by cases h : Term.eval ρ value <;> simp [fixed32, Term.eval, UnOp.eval, valInt32, h]

private def fixed64Lawful : fixed64.Lawful where
  embL := Embedding.lawfulInt64
  ofWf h := ⟨trivial, h⟩
  toWf h := ⟨trivial, h⟩
  ofEval _ _ := rfl
  toEval ρ value := by cases h : Term.eval ρ value <;> simp [fixed64, Term.eval, UnOp.eval, valInt64, h]

/-- The signed value of a bitvector, spelled out as `BitVec.toInt` does: SMT-LIB
    offers `bv2nat` but no signed counterpart. -/
private def toIntTerm (width : Nat) (bits : Term (.bv width)) : Term .int :=
  let n : Term .int := .unop (.bvToNat width) bits
  .ite (.binop .less (.binop .mul (.const (.i 2)) n) (.const (.i (2 ^ width))))
    n (.binop .sub n (.const (.i (2 ^ width))))

private theorem toIntTerm_wf (width : Nat) :
    ∀ (Δ : Signature) (bits : Term (.bv width)), bits.wfIn Δ →
      (toIntTerm width bits).wfIn Δ := by
  intro Δ bits h
  simp [toIntTerm, Term.wfIn, Const.wfIn, UnOp.wfIn, BinOp.wfIn, h]

private theorem toIntTerm_eval (width : Nat) :
    ∀ (ρ : Env) (bits : Term (.bv width)),
      Term.eval ρ (toIntTerm width bits) = (Term.eval ρ bits).toInt := by
  intro ρ bits
  have hpow : ((2 : Int) ^ width) = ((2 ^ width : Nat) : Int) := by push_cast; ring
  have hcast : ∀ n : Nat, ((2 : Int) * (n : Int) < ((2 ^ width : Nat) : Int)) ↔
      2 * n < 2 ^ width := fun n => by
    rw [show ((2 : Int) * (n : Int)) = ((2 * n : Nat) : Int) by push_cast; ring, Nat.cast_lt]
  simp only [toIntTerm, Term.eval, UnOp.eval, BinOp.eval, Const.denote, BitVec.toInt,
    Bool.cond_eq_ite, decide_eq_true_eq, hpow]
  rcases Nat.lt_or_ge (2 * (Term.eval ρ bits).toNat) (2 ^ width) with h | h
  · rw [if_pos ((hcast _).2 h), if_pos h]
  · rw [if_neg (fun hc => absurd ((hcast _).1 hc) (Nat.not_lt.2 h)), if_neg (Nat.not_lt.2 h)]

/-! ## Direct encodings

Each family of operations gets its encoding as a plain term function, plus the
two facts the builder asks of a direct encoding: the term stays well-formed,
and it evaluates to what the carrier function computes. -/

/-- A value-level encoding from a sort-level one: unwrap each argument, apply
    the operation, wrap the result. `out`, `arg` and `encode` each come with a
    well-formedness fact and an evaluation fact, and the lemmas below chain
    them. -/
private def liftZero {σ : Srt} (out : Term σ → Term .value) (t : Term σ) :
    FOL.Direct .zero :=
  fun () => out t

private theorem liftZero_wf {σ : Srt} {out : Term σ → Term .value} {t : Term σ}
    (hout : ∀ {Δ : Signature} {u : Term σ}, u.wfIn Δ → (out u).wfIn Δ)
    (ht : ∀ Δ : Signature, t.wfIn Δ) :
    IntrinsicFOL.Lawful (.direct (liftZero out t)) :=
  fun Δ _ _ => hout (ht Δ)

private theorem liftZero_eval {σ : Srt} {out : Term σ → Term .value} {t : Term σ}
    {inject : σ.denote → Runtime.Val} {v : σ.denote}
    (hout : ∀ (ρ : Env) (u : Term σ), Term.eval ρ (out u) = inject (Term.eval ρ u))
    (ht : ∀ ρ : Env, Term.eval ρ t = v) (ρ : Env) :
    Term.eval ρ (liftZero out t ()) = inject v := by
  rw [liftZero, hout, ht]

private def liftUnary {σ τ : Srt} (out : Term σ → Term .value)
    (arg : Term .value → Term τ) (encode : Term τ → Term σ) : FOL.Direct .one :=
  fun value => out (encode (arg value))

private theorem liftUnary_wf {σ τ : Srt} {out : Term σ → Term .value}
    {arg : Term .value → Term τ} {encode : Term τ → Term σ}
    (hout : ∀ {Δ : Signature} {u : Term σ}, u.wfIn Δ → (out u).wfIn Δ)
    (harg : ∀ {Δ : Signature} {u : Term .value}, u.wfIn Δ → (arg u).wfIn Δ)
    (henc : ∀ (Δ : Signature) (u : Term τ), u.wfIn Δ → (encode u).wfIn Δ) :
    IntrinsicFOL.Lawful (.direct (liftUnary out arg encode)) :=
  fun Δ _ h => hout (henc Δ _ (harg h))

private theorem liftUnary_eval {σ τ : Srt} {out : Term σ → Term .value}
    {arg : Term .value → Term τ} {encode : Term τ → Term σ}
    {inject : σ.denote → Runtime.Val} {project : Runtime.Val → τ.denote}
    {f : τ.denote → σ.denote}
    (hout : ∀ (ρ : Env) (u : Term σ), Term.eval ρ (out u) = inject (Term.eval ρ u))
    (harg : ∀ (ρ : Env) (u : Term .value), Term.eval ρ (arg u) = project (Term.eval ρ u))
    (henc : ∀ (ρ : Env) (u : Term τ), Term.eval ρ (encode u) = f (Term.eval ρ u))
    (ρ : Env) (value : Term .value) :
    Term.eval ρ (liftUnary out arg encode value)
      = inject (f (project (Term.eval ρ value))) := by
  rw [liftUnary, hout, henc, harg]

private def liftBinary {σ τ₁ τ₂ : Srt} (out : Term σ → Term .value)
    (arg₁ : Term .value → Term τ₁) (arg₂ : Term .value → Term τ₂)
    (encode : Term τ₁ → Term τ₂ → Term σ) : FOL.Direct .two :=
  fun (a, b) => out (encode (arg₁ a) (arg₂ b))

private theorem liftBinary_wf {σ τ₁ τ₂ : Srt} {out : Term σ → Term .value}
    {arg₁ : Term .value → Term τ₁} {arg₂ : Term .value → Term τ₂}
    {encode : Term τ₁ → Term τ₂ → Term σ}
    (hout : ∀ {Δ : Signature} {u : Term σ}, u.wfIn Δ → (out u).wfIn Δ)
    (harg₁ : ∀ {Δ : Signature} {u : Term .value}, u.wfIn Δ → (arg₁ u).wfIn Δ)
    (harg₂ : ∀ {Δ : Signature} {u : Term .value}, u.wfIn Δ → (arg₂ u).wfIn Δ)
    (henc : ∀ (Δ : Signature) (u : Term τ₁) (v : Term τ₂), u.wfIn Δ → v.wfIn Δ →
      (encode u v).wfIn Δ) :
    IntrinsicFOL.Lawful (.direct (liftBinary out arg₁ arg₂ encode)) :=
  fun Δ _ h => hout (henc Δ _ _ (harg₁ h.1) (harg₂ h.2))

private theorem liftBinary_eval {σ τ₁ τ₂ : Srt} {out : Term σ → Term .value}
    {arg₁ : Term .value → Term τ₁} {arg₂ : Term .value → Term τ₂}
    {encode : Term τ₁ → Term τ₂ → Term σ}
    {inject : σ.denote → Runtime.Val} {project₁ : Runtime.Val → τ₁.denote}
    {project₂ : Runtime.Val → τ₂.denote} {f : τ₁.denote → τ₂.denote → σ.denote}
    (hout : ∀ (ρ : Env) (u : Term σ), Term.eval ρ (out u) = inject (Term.eval ρ u))
    (harg₁ : ∀ (ρ : Env) (u : Term .value), Term.eval ρ (arg₁ u) = project₁ (Term.eval ρ u))
    (harg₂ : ∀ (ρ : Env) (u : Term .value), Term.eval ρ (arg₂ u) = project₂ (Term.eval ρ u))
    (henc : ∀ (ρ : Env) (u : Term τ₁) (v : Term τ₂),
      Term.eval ρ (encode u v) = f (Term.eval ρ u) (Term.eval ρ v))
    (ρ : Env) (a b : Term .value) :
    Term.eval ρ (liftBinary out arg₁ arg₂ encode (a, b))
      = inject (f (project₁ (Term.eval ρ a)) (project₂ (Term.eval ρ b))) := by
  rw [liftBinary, hout, henc, harg₁, harg₂]

/-! The three wrappers that are not part of a `Fixed`: an integer or boolean
result read as a value, and an integer argument read from one. -/

private theorem ofInt_wf {Δ : Signature} {t : Term .int} (h : t.wfIn Δ) :
    (Term.unop .ofInt t).wfIn Δ := ⟨trivial, h⟩

private theorem ofInt_eval (ρ : Env) (t : Term .int) :
    Term.eval ρ (.unop .ofInt t) = .int (Term.eval ρ t) := rfl

private theorem ofBool_wf {Δ : Signature} {t : Term .bool} (h : t.wfIn Δ) :
    (Term.unop .ofBool t).wfIn Δ := ⟨trivial, h⟩

private theorem ofBool_eval (ρ : Env) (t : Term .bool) :
    Term.eval ρ (.unop .ofBool t) = .bool (Term.eval ρ t) := rfl

private theorem toInt_wf {Δ : Signature} {t : Term .value} (h : t.wfIn Δ) :
    (Term.unop .toInt t).wfIn Δ := ⟨trivial, h⟩

private theorem toInt_eval (ρ : Env) (t : Term .value) :
    Term.eval ρ (.unop .toInt t) = valInt (Term.eval ρ t) := rfl

inductive FixedConst where
  | zero | one | minusOne | minInt | maxInt
  deriving DecidableEq, Repr

private def FixedConst.member : FixedConst → String
  | .zero => "zero"
  | .one => "one"
  | .minusOne => "minus_one"
  | .minInt => "min_int"
  | .maxInt => "max_int"

private def FixedConst.bits (width : Nat) : FixedConst → BitVec width
  | .zero => 0
  | .one => 1
  | .minusOne => -1
  | .minInt => BitVec.ofInt width (-(2 ^ (width - 1) : Int))
  | .maxInt => BitVec.ofInt width ((2 ^ (width - 1) : Nat) - 1)

private def constB (fx : Fixed) (op : FixedConst) : Pure.Zero where
  name := fx.name ++ "_" ++ op.member
  path := some (fx.module, [op.member])
  res := fx.emb
  f := op.bits fx.width
  enc := .direct (liftZero fx.ofBits (.const (.bv (op.bits fx.width))))

def int32Const (op : FixedConst) : Intrinsic := (constB fixed32 op).toIntrinsic
def int64Const (op : FixedConst) : Intrinsic := (constB fixed64 op).toIntrinsic

@[simp] theorem int32Const_symbol (op : FixedConst) : (int32Const op).symbol = none := rfl
@[simp] theorem int64Const_symbol (op : FixedConst) : (int64Const op).symbol = none := rfl

/-- `specBaseWf` is the one obligation that does not generalize over `fx`:
    `PredTrans.checkWf` only reduces once the intrinsic name and the encoded
    term are concrete, so each width discharges it at its own `Fixed`. -/
private def constLawful {fx : Fixed} (fl : fx.Lawful) (op : FixedConst)
    (nameFresh : (constB fx op).name ≠ "ret")
    (specBaseWf : PredTrans.wfIn
      ((Intrinsic.sigOf [(constB fx op).toIntrinsic]).declVars
        (Spec.argVars (constB fx op).toIntrinsic.specArgs))
      (constB fx op).toIntrinsic.spec.pred) :
    (constB fx op).Lawful [] where
  resL := fl.embL
  nameFresh := nameFresh
  semWellTyped := fun _ _ => .rfl
  specBaseWf := specBaseWf
  encWf := liftZero_wf fl.ofWf (fun _ => trivial)
  typeWf := nofun
  encEval := liftZero_eval fl.ofEval (fun _ => rfl)

instance (op : FixedConst) : IntrinsicSound [int32Const op] (int32Const op) :=
  (constLawful fixed32Lawful op (by cases op <;> decide)
    (by cases op <;> apply PredTrans.checkWf_ok <;> rfl)).sound

instance (op : FixedConst) : IntrinsicSound [int64Const op] (int64Const op) :=
  (constLawful fixed64Lawful op (by cases op <;> decide)
    (by cases op <;> apply PredTrans.checkWf_ok <;> rfl)).sound

inductive FixedUnary where
  | neg | lognot
  deriving DecidableEq, Repr

private def FixedUnary.member : FixedUnary → String
  | .neg => "neg"
  | .lognot => "lognot"

private def FixedUnary.apply : FixedUnary → BitVec width → BitVec width
  | .neg, bits => -bits
  | .lognot, bits => ~~~bits

private def FixedUnary.term (width : Nat) : FixedUnary → Term (.bv width) → Term (.bv width)
  | .neg, bits => .unop (.bvNeg width) bits
  | .lognot, bits => .unop (.bvNot width) bits

private theorem FixedUnary.term_eval (op : FixedUnary) (width : Nat) :
    ∀ ρ bits, Term.eval ρ (op.term width bits) = op.apply (Term.eval ρ bits) := by
  cases op <;> intro ρ bits <;> rfl

private theorem FixedUnary.term_wf (op : FixedUnary) (width : Nat) :
    ∀ Δ bits, bits.wfIn Δ → (op.term width bits).wfIn Δ := by
  cases op <;> intro Δ bits h <;> exact ⟨trivial, h⟩

private def unaryB (fx : Fixed) (op : FixedUnary) : Pure.Unary where
  name := fx.name ++ "_" ++ op.member
  path := some (fx.module, [op.member])
  arg := fx.emb
  res := fx.emb
  f := op.apply
  dom := fun _ => True
  pre := none
  enc := .direct (liftUnary fx.ofBits fx.toBits (op.term fx.width))

def int32Unary (op : FixedUnary) : Intrinsic := (unaryB fixed32 op).toIntrinsic
def int64Unary (op : FixedUnary) : Intrinsic := (unaryB fixed64 op).toIntrinsic

@[simp] theorem int32Unary_symbol (op : FixedUnary) : (int32Unary op).symbol = none := rfl
@[simp] theorem int64Unary_symbol (op : FixedUnary) : (int64Unary op).symbol = none := rfl

private def unaryLawful {fx : Fixed} (fl : fx.Lawful) (op : FixedUnary)
    (specBaseWf : PredTrans.wfIn
      ((Intrinsic.sigOf [(unaryB fx op).toIntrinsic]).declVars
        (Spec.argVars (unaryB fx op).toIntrinsic.specArgs))
      (unaryB fx op).toIntrinsic.spec.pred) :
    (unaryB fx op).Lawful [] where
  argL := fl.embL
  resL := fl.embL
  domSound := fun _ _ _ _ => True.intro
  semWellTyped := fun _ _ _ _ => .rfl
  specBaseWf := specBaseWf
  encWf := liftUnary_wf fl.ofWf fl.toWf (op.term_wf fx.width)
  typeWf := nofun
  encEval := fun ρ x hx => by
    have hpi : ∀ z, fx.project (fx.inject z) = z := fl.embL.project_inject
    rw [liftUnary_eval fl.ofEval fl.toEval (op.term_eval fx.width) ρ,
      show Term.eval ρ (Term.var .value "a") = fx.inject x from hx, hpi]
    rfl

instance (op : FixedUnary) : IntrinsicSound [int32Unary op] (int32Unary op) :=
  (unaryLawful fixed32Lawful op (by cases op <;> apply PredTrans.checkWf_ok <;> rfl)).sound

instance (op : FixedUnary) : IntrinsicSound [int64Unary op] (int64Unary op) :=
  (unaryLawful fixed64Lawful op (by cases op <;> apply PredTrans.checkWf_ok <;> rfl)).sound

inductive FixedBinary where
  | add | sub | mul | div | unsignedDiv | rem | unsignedRem
  | logand | logor | logxor | min | max
  deriving DecidableEq, Repr

private def FixedBinary.member : FixedBinary → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .div => "div"
  | .unsignedDiv => "unsigned_div"
  | .rem => "rem"
  | .unsignedRem => "unsigned_rem"
  | .logand => "logand"
  | .logor => "logor"
  | .logxor => "logxor"
  | .min => "min"
  | .max => "max"

private def FixedBinary.apply : FixedBinary → BitVec width → BitVec width → BitVec width
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a.smtSDiv b
  | .unsignedDiv, a, b => a.smtUDiv b
  | .rem, a, b => a.srem b
  | .unsignedRem, a, b => a.umod b
  | .logand, a, b => a &&& b
  | .logor, a, b => a ||| b
  | .logxor, a, b => a ^^^ b
  | .min, a, b => bif a.slt b then a else b
  | .max, a, b => bif a.slt b then b else a

private def FixedBinary.term (width : Nat) :
    FixedBinary → Term (.bv width) → Term (.bv width) → Term (.bv width)
  | .add, a, b => .binop (.bvAdd width) a b
  | .sub, a, b => .binop (.bvSub width) a b
  | .mul, a, b => .binop (.bvMul width) a b
  | .div, a, b => .binop (.bvSDiv width) a b
  | .unsignedDiv, a, b => .binop (.bvUDiv width) a b
  | .rem, a, b => .binop (.bvSRem width) a b
  | .unsignedRem, a, b => .binop (.bvURem width) a b
  | .logand, a, b => .binop (.bvAnd width) a b
  | .logor, a, b => .binop (.bvOr width) a b
  | .logxor, a, b => .binop (.bvXor width) a b
  | .min, a, b => .ite (.binop (.bvSLt width) a b) a b
  | .max, a, b => .ite (.binop (.bvSLt width) a b) b a

private theorem FixedBinary.term_eval (op : FixedBinary) (width : Nat) :
    ∀ ρ a b, Term.eval ρ (op.term width a b) = op.apply (Term.eval ρ a) (Term.eval ρ b) := by
  cases op <;> intro ρ a b <;> rfl

private theorem FixedBinary.term_wf (op : FixedBinary) (width : Nat) :
    ∀ Δ a b, a.wfIn Δ → b.wfIn Δ → (op.term width a b).wfIn Δ := by
  cases op <;> intro Δ a b ha hb
  case min => exact ⟨⟨trivial, ha, hb⟩, ha, hb⟩
  case max => exact ⟨⟨trivial, ha, hb⟩, hb, ha⟩
  all_goals exact ⟨trivial, ha, hb⟩

private def divisorNonzero (fx : Fixed) (_a b : String) : Formula :=
  .not (.eq (.bv fx.width) (fx.toBits (.var .value b)) (.const (.bv 0)))

private inductive BinaryGuard where
  | divisor

private def FixedBinary.guard : FixedBinary → Option BinaryGuard
  | .div | .unsignedDiv | .rem | .unsignedRem => some .divisor
  | _ => none

private def BinaryGuard.dom (guard : BinaryGuard) (_a b : BitVec width) : Prop :=
  match guard with
  | .divisor => b ≠ 0

private def BinaryGuard.pre (guard : BinaryGuard) (fx : Fixed) : String → String → Formula :=
  match guard with
  | .divisor => divisorNonzero fx

private def FixedBinary.dom (op : FixedBinary) (_a b : BitVec width) : Prop :=
  match op.guard with
  | some guard => guard.dom _a b
  | none => True

private def FixedBinary.pre (op : FixedBinary) (fx : Fixed) :
    Option (String → String → Formula) :=
  op.guard.map (fun guard => guard.pre fx)

private def binaryB (fx : Fixed) (op : FixedBinary) : Pure.Binary where
  name := fx.name ++ "_" ++ op.member
  path := some (fx.module, [op.member])
  arg₁ := fx.emb
  arg₂ := fx.emb
  res := fx.emb
  f := op.apply
  dom := op.dom
  pre := op.pre fx
  enc := .direct (liftBinary fx.ofBits fx.toBits fx.toBits (op.term fx.width))

def int32Binary (op : FixedBinary) : Intrinsic := (binaryB fixed32 op).toIntrinsic
def int64Binary (op : FixedBinary) : Intrinsic := (binaryB fixed64 op).toIntrinsic

@[simp] theorem int32Binary_symbol (op : FixedBinary) : (int32Binary op).symbol = none := rfl
@[simp] theorem int64Binary_symbol (op : FixedBinary) : (int64Binary op).symbol = none := rfl

private theorem binaryDomSound {fx : Fixed} (fl : fx.Lawful) (op : FixedBinary) :
    ∀ (ρ : Env) (x y : BitVec fx.width),
      (∀ p, op.pre fx = some p →
        (p "a" "b").eval
          ((ρ.updateConst .value "a" (fx.inject x)).updateConst .value "b" (fx.inject y))) →
      op.dom x y := by
  have hpi : ∀ z, fx.project (fx.inject z) = z := fl.embL.project_inject
  intro ρ x y h
  cases op <;> try trivial
  all_goals
    have hp := h (divisorNonzero fx) rfl
    simp only [divisorNonzero, Formula.eval, Term.eval, fl.toEval, Const.denote,
      Env.lookupConst_updateConst_same] at hp
    simpa [FixedBinary.dom, FixedBinary.guard, BinaryGuard.dom, hpi] using hp

private def binaryLawful {fx : Fixed} (fl : fx.Lawful) (op : FixedBinary)
    (specBaseWf : PredTrans.wfIn
      ((Intrinsic.sigOf [(binaryB fx op).toIntrinsic]).declVars
        (Spec.argVars (binaryB fx op).toIntrinsic.specArgs))
      (binaryB fx op).toIntrinsic.spec.pred) :
    (binaryB fx op).Lawful [] where
  argL₁ := fl.embL
  argL₂ := fl.embL
  resL := fl.embL
  domSound := fun ρ x y _ => binaryDomSound fl op ρ x y
  semWellTyped := fun _ _ _ _ _ => sep_emp.1
  specBaseWf := specBaseWf
  encWf := liftBinary_wf fl.ofWf fl.toWf fl.toWf (op.term_wf fx.width)
  typeWf := nofun
  encEval := fun ρ x y hx hy => by
    have hpi : ∀ z, fx.project (fx.inject z) = z := fl.embL.project_inject
    rw [liftBinary_eval fl.ofEval fl.toEval fl.toEval (op.term_eval fx.width) ρ,
      show Term.eval ρ (Term.var .value "a") = fx.inject x from hx,
      show Term.eval ρ (Term.var .value "b") = fx.inject y from hy, hpi, hpi]
    rfl

instance (op : FixedBinary) : IntrinsicSound [int32Binary op] (int32Binary op) :=
  (binaryLawful fixed32Lawful op (by cases op <;> apply PredTrans.checkWf_ok <;> rfl)).sound

instance (op : FixedBinary) : IntrinsicSound [int64Binary op] (int64Binary op) :=
  (binaryLawful fixed64Lawful op (by cases op <;> apply PredTrans.checkWf_ok <;> rfl)).sound

inductive FixedCompare where
  | compare | unsignedCompare | equal
  deriving DecidableEq, Repr

private def FixedCompare.member : FixedCompare → String
  | .compare => "compare"
  | .unsignedCompare => "unsigned_compare"
  | .equal => "equal"

private def signedCompare (a b : BitVec width) : Int :=
  bif a.slt b then -1 else bif a == b then 0 else 1

private def unsignedCompare (a b : BitVec width) : Int :=
  bif a.ult b then -1 else bif a == b then 0 else 1

private inductive CompareOrder where
  | signed | unsigned

private def compareTerm (width : Nat) (order : CompareOrder)
    (a b : Term (.bv width)) : Term .int :=
  let less := match order with
    | .signed => .binop (.bvSLt width) a b
    | .unsigned => .binop (.bvULt width) a b
  .ite less (.const (.i (-1)))
    (.ite (.binop .eq a b) (.const (.i 0)) (.const (.i 1)))

private theorem compareTerm_wf (width : Nat) (order : CompareOrder) :
    ∀ Δ a b, a.wfIn Δ → b.wfIn Δ → (compareTerm width order a b).wfIn Δ := by
  intro Δ a b ha hb
  cases order <;> exact ⟨⟨trivial, ha, hb⟩, trivial, ⟨⟨trivial, ha, hb⟩, trivial, trivial⟩⟩

private theorem signedCompareTerm_eval (width : Nat) :
    ∀ ρ a b, Term.eval ρ (compareTerm width .signed a b) =
      signedCompare (Term.eval ρ a) (Term.eval ρ b) := by
  intro ρ a b
  rfl

private theorem unsignedCompareTerm_eval (width : Nat) :
    ∀ ρ a b, Term.eval ρ (compareTerm width .unsigned a b) =
      unsignedCompare (Term.eval ρ a) (Term.eval ρ b) := by
  intro ρ a b
  rfl

private def equalTerm (width : Nat) (a b : Term (.bv width)) : Term .bool :=
  .binop .eq a b

private theorem equalTerm_wf (width : Nat) :
    ∀ Δ a b, a.wfIn Δ → b.wfIn Δ → (equalTerm width a b).wfIn Δ := by
  intro Δ a b ha hb
  exact ⟨trivial, ha, hb⟩

private theorem equalTerm_eval (width : Nat) :
    ∀ ρ a b, Term.eval ρ (equalTerm width a b) = ((Term.eval ρ a) == (Term.eval ρ b)) := by
  intro ρ a b
  simp [equalTerm, Term.eval, Bool.beq_eq_decide_eq]

private def compareB (fx : Fixed) : FixedCompare → Pure.Binary
  | .compare => {
      name := fx.name ++ "_compare", path := some (fx.module, ["compare"])
      arg₁ := fx.emb, arg₂ := fx.emb, res := .int
      f := signedCompare, dom := fun _ _ => True, pre := none
      enc := .direct (liftBinary (.unop .ofInt ·) fx.toBits fx.toBits
        (compareTerm fx.width .signed)) }
  | .unsignedCompare => {
      name := fx.name ++ "_unsigned_compare", path := some (fx.module, ["unsigned_compare"])
      arg₁ := fx.emb, arg₂ := fx.emb, res := .int
      f := unsignedCompare, dom := fun _ _ => True, pre := none
      enc := .direct (liftBinary (.unop .ofInt ·) fx.toBits fx.toBits
        (compareTerm fx.width .unsigned)) }
  | .equal => {
      name := fx.name ++ "_equal", path := some (fx.module, ["equal"])
      arg₁ := fx.emb, arg₂ := fx.emb, res := .bool
      f := fun (a b : BitVec fx.width) => a == b, dom := fun _ _ => True, pre := none
      enc := .direct (liftBinary (.unop .ofBool ·) fx.toBits fx.toBits
        (equalTerm fx.width)) }

def int32Compare (op : FixedCompare) : Intrinsic := (compareB fixed32 op).toIntrinsic
def int64Compare (op : FixedCompare) : Intrinsic := (compareB fixed64 op).toIntrinsic

@[simp] theorem int32Compare_symbol (op : FixedCompare) : (int32Compare op).symbol = none := by
  cases op <;> rfl
@[simp] theorem int64Compare_symbol (op : FixedCompare) : (int64Compare op).symbol = none := by
  cases op <;> rfl

private def compareLawful {fx : Fixed} (fl : fx.Lawful) (op : FixedCompare)
    (specBaseWf : PredTrans.wfIn
      ((Intrinsic.sigOf [(compareB fx op).toIntrinsic]).declVars
        (Spec.argVars (compareB fx op).toIntrinsic.specArgs))
      (compareB fx op).toIntrinsic.spec.pred) :
    (compareB fx op).Lawful [] := by
  revert specBaseWf
  cases op
  all_goals exact fun specBaseWf => {
    argL₁ := fl.embL
    argL₂ := fl.embL
    resL := by first | exact Embedding.lawfulInt | exact Embedding.lawfulBool
    domSound := fun _ _ _ _ _ => True.intro
    semWellTyped := fun _ _ _ _ _ => sep_emp.1
    specBaseWf := specBaseWf
    encWf := by
      first
        | exact liftBinary_wf ofInt_wf fl.toWf fl.toWf (compareTerm_wf fx.width .signed)
        | exact liftBinary_wf ofInt_wf fl.toWf fl.toWf (compareTerm_wf fx.width .unsigned)
        | exact liftBinary_wf ofBool_wf fl.toWf fl.toWf (equalTerm_wf fx.width)
    typeWf := nofun
    encEval := fun ρ x y hx hy => by
      have hpi : ∀ z, fx.project (fx.inject z) = z := fl.embL.project_inject
      have hx' : Term.eval ρ (Term.var .value "a") = fx.inject x := hx
      have hy' : Term.eval ρ (Term.var .value "b") = fx.inject y := hy
      first
        | rw [liftBinary_eval ofInt_eval fl.toEval fl.toEval
            (signedCompareTerm_eval fx.width) ρ, hx', hy', hpi, hpi]
        | rw [liftBinary_eval ofInt_eval fl.toEval fl.toEval
            (unsignedCompareTerm_eval fx.width) ρ, hx', hy', hpi, hpi]
        | rw [liftBinary_eval ofBool_eval fl.toEval fl.toEval
            (equalTerm_eval fx.width) ρ, hx', hy', hpi, hpi]
      rfl }

instance (op : FixedCompare) : IntrinsicSound [int32Compare op] (int32Compare op) :=
  (compareLawful fixed32Lawful op (by cases op <;> apply PredTrans.checkWf_ok <;> rfl)).sound

instance (op : FixedCompare) : IntrinsicSound [int64Compare op] (int64Compare op) :=
  (compareLawful fixed64Lawful op (by cases op <;> apply PredTrans.checkWf_ok <;> rfl)).sound

inductive FixedShift where
  | left | right | rightLogical
  deriving DecidableEq, Repr

private def FixedShift.member : FixedShift → String
  | .left => "shift_left"
  | .right => "shift_right"
  | .rightLogical => "shift_right_logical"

private def FixedShift.apply (width : Nat) : FixedShift → BitVec width → Int → BitVec width
  | .left, bits, count => bits <<< (BitVec.ofInt width count)
  | .right, bits, count => bits.sshiftRight' (BitVec.ofInt width count)
  | .rightLogical, bits, count => bits >>> (BitVec.ofInt width count)

private def FixedShift.term (width : Nat) :
    FixedShift → Term (.bv width) → Term .int → Term (.bv width)
  | .left, bits, count => .binop (.bvShl width) bits (.unop (.intToBv width) count)
  | .right, bits, count => .binop (.bvAShr width) bits (.unop (.intToBv width) count)
  | .rightLogical, bits, count => .binop (.bvLShr width) bits (.unop (.intToBv width) count)

private theorem FixedShift.term_eval (op : FixedShift) (width : Nat) :
    ∀ ρ bits count, Term.eval ρ (op.term width bits count) =
      op.apply width (Term.eval ρ bits) (Term.eval ρ count) := by
  cases op <;> intro ρ bits count <;> rfl

private theorem FixedShift.term_wf (op : FixedShift) (width : Nat) :
    ∀ Δ bits count, bits.wfIn Δ → count.wfIn Δ →
      (op.term width bits count).wfIn Δ := by
  cases op <;> intro Δ bits count hbits hcount <;>
    exact ⟨trivial, hbits, ⟨trivial, hcount⟩⟩

private def shiftPre (width : Nat) (_bits count : String) : Formula :=
  let n := .unop .toInt (.var .value count)
  .and (.binpred .le (.const (.i 0)) n) (.binpred .lt n (.const (.i width)))

private def shiftDom (width : Nat) (_bits : BitVec width) (count : Int) : Prop :=
  0 ≤ count ∧ count < width

private def shiftB (fx : Fixed) (op : FixedShift) : Pure.Binary where
  name := fx.name ++ "_" ++ op.member
  path := some (fx.module, [op.member])
  arg₁ := fx.emb
  arg₂ := .int
  res := fx.emb
  f := op.apply fx.width
  dom := shiftDom fx.width
  pre := some (shiftPre fx.width)
  enc := .direct (liftBinary fx.ofBits fx.toBits (.unop .toInt ·) (op.term fx.width))

def int32Shift (op : FixedShift) : Intrinsic := (shiftB fixed32 op).toIntrinsic
def int64Shift (op : FixedShift) : Intrinsic := (shiftB fixed64 op).toIntrinsic

@[simp] theorem int32Shift_symbol (op : FixedShift) : (int32Shift op).symbol = none := rfl
@[simp] theorem int64Shift_symbol (op : FixedShift) : (int64Shift op).symbol = none := rfl

private theorem shiftDomSound (fx : Fixed) :
    ∀ (ρ : Env) (bits : BitVec fx.width) (count : Int),
      (∀ p, (some (shiftPre fx.width) : Option (String → String → Formula)) = some p →
        (p "a" "b").eval
          ((ρ.updateConst .value "a" (fx.inject bits)).updateConst .value "b" (.int count))) →
      shiftDom fx.width bits count := by
  intro ρ bits count h
  have hp := h (shiftPre fx.width) rfl
  simpa [shiftPre, shiftDom, Formula.eval, Term.eval,
    Env.lookupConst_updateConst_ne] using hp

private def shiftLawful {fx : Fixed} (fl : fx.Lawful) (op : FixedShift)
    (specBaseWf : PredTrans.wfIn
      ((Intrinsic.sigOf [(shiftB fx op).toIntrinsic]).declVars
        (Spec.argVars (shiftB fx op).toIntrinsic.specArgs))
      (shiftB fx op).toIntrinsic.spec.pred) :
    (shiftB fx op).Lawful [] where
  argL₁ := fl.embL
  argL₂ := Embedding.lawfulInt
  resL := fl.embL
  domSound := fun ρ x y _ => shiftDomSound fx ρ x y
  semWellTyped := fun _ _ _ _ _ => sep_emp.1
  specBaseWf := specBaseWf
  encWf := liftBinary_wf fl.ofWf fl.toWf toInt_wf (op.term_wf fx.width)
  typeWf := nofun
  encEval := fun ρ x y hx hy => by
    have hpi : ∀ z, fx.project (fx.inject z) = z := fl.embL.project_inject
    rw [liftBinary_eval fl.ofEval fl.toEval toInt_eval (op.term_eval fx.width) ρ,
      show Term.eval ρ (Term.var .value "a") = fx.inject x from hx,
      show Term.eval ρ (Term.var .value "b") = Runtime.Val.int y from hy, hpi]
    rfl

instance (op : FixedShift) : IntrinsicSound [int32Shift op] (int32Shift op) :=
  (shiftLawful fixed32Lawful op (by cases op <;> apply PredTrans.checkWf_ok <;> rfl)).sound

instance (op : FixedShift) : IntrinsicSound [int64Shift op] (int64Shift op) :=
  (shiftLawful fixed64Lawful op (by cases op <;> apply PredTrans.checkWf_ok <;> rfl)).sound

private def ofIntB (fx : Fixed) : Pure.Unary where
  name := fx.name ++ "_of_int"
  path := some (fx.module, ["of_int"])
  arg := .int
  res := fx.emb
  f := BitVec.ofInt fx.width
  dom := fun _ => True
  pre := none
  enc := .direct (liftUnary fx.ofBits (.unop .toInt ·) (.unop (.intToBv fx.width) ·))

/-- `Int32.to_int` is lossless, but OCaml's native `int` is 63 bits wide, so
    `Int64.to_int` drops the top bit. The two conversions therefore keep
    different numbers of bits, and each spells out its own term. -/
private def int32ToIntB : Pure.Unary where
  name := "int32_to_int"
  path := some ("Int32", ["to_int"])
  arg := fixed32.emb
  res := .int
  f := BitVec.toInt
  dom := fun _ => True
  pre := none
  enc := .direct (liftUnary (.unop .ofInt ·) fixed32.toBits (toIntTerm 32))

private def int64ToIntB : Pure.Unary where
  name := "int64_to_int"
  path := some ("Int64", ["to_int"])
  arg := fixed64.emb
  res := .int
  f := fun bits => (bits.extractLsb' 0 63).toInt
  dom := fun _ => True
  pre := none
  enc := .direct (liftUnary (.unop .ofInt ·) fixed64.toBits
    (fun bits => toIntTerm 63 (.unop (.bvExtractLsb 64 63 (by omega)) bits)))

private def int64OfInt32B : Pure.Unary where
  name := "int64_of_int32"
  path := some ("Int64", ["of_int32"])
  arg := fixed32.emb
  res := fixed64.emb
  f := fun bits => bits.signExtend 64
  dom := fun _ => True
  pre := none
  enc := .direct (liftUnary fixed64.ofBits fixed32.toBits
    (fun bits => .unop (.bvSignExtend 32 64 (by omega)) bits))

private def int64ToInt32B : Pure.Unary where
  name := "int64_to_int32"
  path := some ("Int64", ["to_int32"])
  arg := fixed64.emb
  res := fixed32.emb
  f := fun bits => bits.extractLsb' 0 32
  dom := fun _ => True
  pre := none
  enc := .direct (liftUnary fixed32.ofBits fixed64.toBits
    (fun bits => .unop (.bvExtractLsb 64 32 (by omega)) bits))

def int32OfInt : Intrinsic := (ofIntB fixed32).toIntrinsic
def int64OfInt : Intrinsic := (ofIntB fixed64).toIntrinsic
def int32ToInt : Intrinsic := int32ToIntB.toIntrinsic
def int64ToInt : Intrinsic := int64ToIntB.toIntrinsic
def int64OfInt32 : Intrinsic := int64OfInt32B.toIntrinsic
def int64ToInt32 : Intrinsic := int64ToInt32B.toIntrinsic

@[simp] theorem int32OfInt_symbol : int32OfInt.symbol = none := rfl
@[simp] theorem int64OfInt_symbol : int64OfInt.symbol = none := rfl
@[simp] theorem int32ToInt_symbol : int32ToInt.symbol = none := rfl
@[simp] theorem int64ToInt_symbol : int64ToInt.symbol = none := rfl
@[simp] theorem int64OfInt32_symbol : int64OfInt32.symbol = none := rfl
@[simp] theorem int64ToInt32_symbol : int64ToInt32.symbol = none := rfl

private def ofIntLawful {fx : Fixed} (fl : fx.Lawful)
    (specBaseWf : PredTrans.wfIn
      ((Intrinsic.sigOf [(ofIntB fx).toIntrinsic]).declVars
        (Spec.argVars (ofIntB fx).toIntrinsic.specArgs))
      (ofIntB fx).toIntrinsic.spec.pred) :
    (ofIntB fx).Lawful [] where
  argL := Embedding.lawfulInt
  resL := fl.embL
  domSound := fun _ _ _ _ => True.intro
  semWellTyped := fun _ _ _ _ => .rfl
  specBaseWf := specBaseWf
  encWf := liftUnary_wf fl.ofWf toInt_wf (fun _ _ h => ⟨trivial, h⟩)
  typeWf := nofun
  encEval := fun ρ x hx => by
    rw [liftUnary_eval fl.ofEval toInt_eval
        (f := BitVec.ofInt fx.width) (fun _ _ => rfl) ρ,
      show Term.eval ρ (Term.var .value "a") = Runtime.Val.int x from hx]
    rfl

private def int32ToIntLawful : int32ToIntB.Lawful [] where
  argL := Embedding.lawfulInt32
  resL := Embedding.lawfulInt
  domSound := fun _ _ _ _ => True.intro
  semWellTyped := fun _ _ _ _ => .rfl
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  encWf := liftUnary_wf ofInt_wf fixed32Lawful.toWf (toIntTerm_wf 32)
  typeWf := nofun
  encEval := fun ρ x hx => by
    rw [liftUnary_eval ofInt_eval fixed32Lawful.toEval (toIntTerm_eval 32) ρ,
      show Term.eval ρ (Term.var .value "a") = Runtime.Val.int32 x from hx]
    rfl

private def int64ToIntLawful : int64ToIntB.Lawful [] where
  argL := Embedding.lawfulInt64
  resL := Embedding.lawfulInt
  domSound := fun _ _ _ _ => True.intro
  semWellTyped := fun _ _ _ _ => .rfl
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  encWf := liftUnary_wf ofInt_wf fixed64Lawful.toWf
    (by intro Δ bits h; exact toIntTerm_wf 63 Δ _ ⟨trivial, h⟩)
  typeWf := nofun
  encEval := fun ρ x hx => by
    rw [liftUnary_eval ofInt_eval fixed64Lawful.toEval
        (f := fun bits => (bits.extractLsb' 0 63).toInt)
        (by intro ρ bits; rw [toIntTerm_eval 63]; rfl) ρ,
      show Term.eval ρ (Term.var .value "a") = Runtime.Val.int64 x from hx]
    rfl

private def int64OfInt32Lawful : int64OfInt32B.Lawful [] where
  argL := Embedding.lawfulInt32
  resL := Embedding.lawfulInt64
  domSound := fun _ _ _ _ => True.intro
  semWellTyped := fun _ _ _ _ => .rfl
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  encWf := liftUnary_wf fixed64Lawful.ofWf fixed32Lawful.toWf (by intro Δ bits h; exact ⟨trivial, h⟩)
  typeWf := nofun
  encEval := fun ρ x hx => by
    rw [liftUnary_eval fixed64Lawful.ofEval fixed32Lawful.toEval
        (f := fun bits : BitVec 32 => bits.signExtend 64) (by intro ρ bits; rfl) ρ,
      show Term.eval ρ (Term.var .value "a") = Runtime.Val.int32 x from hx]
    rfl

private def int64ToInt32Lawful : int64ToInt32B.Lawful [] where
  argL := Embedding.lawfulInt64
  resL := Embedding.lawfulInt32
  domSound := fun _ _ _ _ => True.intro
  semWellTyped := fun _ _ _ _ => .rfl
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  encWf := liftUnary_wf fixed32Lawful.ofWf fixed64Lawful.toWf (by intro Δ bits h; exact ⟨trivial, h⟩)
  typeWf := nofun
  encEval := fun ρ x hx => by
    rw [liftUnary_eval fixed32Lawful.ofEval fixed64Lawful.toEval
        (f := fun bits : BitVec 64 => bits.extractLsb' 0 32) (by intro ρ bits; rfl) ρ,
      show Term.eval ρ (Term.var .value "a") = Runtime.Val.int64 x from hx]
    rfl

instance : IntrinsicSound [int32OfInt] int32OfInt :=
  (ofIntLawful fixed32Lawful (by apply PredTrans.checkWf_ok; rfl)).sound
instance : IntrinsicSound [int64OfInt] int64OfInt :=
  (ofIntLawful fixed64Lawful (by apply PredTrans.checkWf_ok; rfl)).sound
instance : IntrinsicSound [int32ToInt] int32ToInt := int32ToIntLawful.sound
instance : IntrinsicSound [int64ToInt] int64ToInt := int64ToIntLawful.sound
instance : IntrinsicSound [int64OfInt32] int64OfInt32 := int64OfInt32Lawful.sound
instance : IntrinsicSound [int64ToInt32] int64ToInt32 := int64ToInt32Lawful.sound

end Intrinsics
end Stdlib
