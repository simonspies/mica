-- SUMMARY: Embeddings and the pure-intrinsic builders (`Pure.Zero`/`Pure.Unary`/`Pure.Binary`/`Pure.Ternary`) that emit an intrinsic and its soundness instance.
import Mica.Verifier.Intrinsic
import Mica.SourceTinyML.Printer

open Iris Iris.BI

namespace Stdlib

open Verifier

namespace Intrinsics

/-! # Combinators for intrinsic soundness -/

/-! ## Shared helpers -/

/-- Apply a `.ret ⟨s, .assert φ ...⟩` spec at a value, discharging the asserted
    `φ` as a pure side condition. -/
theorem assert_ret_apply [MicaGS HasLC.hasLC Sig] (W : TinyML.World) (Φ : Runtime.Val → iProp)
    (s : String) (ρ : Env) (φ : Formula) (v : Runtime.Val)
    (hφ : φ.eval (ρ.updateConst .value s v)) :
    PredTrans.apply (TinyML.ValHasType W) Φ (.ret ⟨s, .assert φ (.ret ())⟩) ρ ⊢ Φ v := by
  simp only [PredTrans.apply, Assertion.pre, Assertion.post]
  refine (forall_elim v).trans ?_
  iintro Hw
  iapply Hw
  ipureintro
  exact hφ

/-- Wrap an optional precondition around a spec predicate: `some φ` prepends an
    `.assert φ`; `none` leaves the predicate untouched, keeping the emitted spec
    of precondition-free intrinsics unchanged. -/
def withPre : Option Formula → PredTrans TinyML.Typ → PredTrans TinyML.Typ
  | none,   post => post
  | some φ, post => .assert φ post

/-- Eliminate `withPre`: applying the wrapped predicate yields the precondition
    as a pure fact (vacuous for `none`) alongside the unwrapped application. -/
theorem withPre_apply [MicaGS HasLC.hasLC Sig] (W : TinyML.World) (Φ : Runtime.Val → iProp)
    (pre : Option Formula) (post : PredTrans TinyML.Typ) (ρ : Env) :
    PredTrans.apply (TinyML.ValHasType W) Φ (withPre pre post) ρ ⊢
      iprop(⌜∀ φ, pre = some φ → φ.eval ρ⌝ ∗ PredTrans.apply (TinyML.ValHasType W) Φ post ρ) := by
  cases pre with
  | none =>
    simp only [withPre]
    iintro H
    isplitl []
    · ipureintro; exact fun φ h => nomatch h
    · iexact H
  | some φ =>
    simp only [withPre, PredTrans.apply, Assertion.pre]
    iintro ⟨%hφ, H⟩
    isplitl []
    · ipureintro; intro φ' h; cases h; exact hφ
    · iexact H

/-- A length-mismatched argument list makes the typing premise inconsistent, so
    it entails anything. -/
theorem valsHaveTypes_off_shape [MicaGS HasLC.hasLC Sig] {W : TinyML.World}
    {vs : List Runtime.Val} {tys : List TinyML.Typ} (P : iProp)
    (hlen : vs.length ≠ tys.length) :
    TinyML.ValsHaveTypes W vs tys ⊢ P := by
  refine TinyML.ValsHaveTypes.length_eq.trans ?_
  iintro %h
  simp at h; omega

/-- Respect for an arity-one symbol survives the argument-binding fold; each
    step rebinds a `value` constant, which never touches the unary table. -/
private theorem respects_argsEnv_one {s : FOL.Symbol .one} :
    ∀ (args : List String) (vs : List Runtime.Val) {ρ : Env},
      ρ.respects (some s) → (Spec.argsEnv ρ args vs).respects (some s)
  | [], _, _, h => h
  | _ :: _, [], _, h => h
  | _ :: rest, _ :: vs, ρ, h => by
      simp only [Spec.argsEnv]
      refine respects_argsEnv_one rest vs ?_
      simpa only [Env.respects, Env.updateConst_unary] using h

/-- Respect for an arity-two symbol survives the argument-binding fold; each
    step rebinds a `value` constant, which never touches the binary table. -/
private theorem respects_argsEnv_two {s : FOL.Symbol .two} :
    ∀ (args : List String) (vs : List Runtime.Val) {ρ : Env},
      ρ.respects (some s) → (Spec.argsEnv ρ args vs).respects (some s)
  | [], _, _, h => h
  | _ :: _, [], _, h => h
  | _ :: rest, _ :: vs, ρ, h => by
      simp only [Spec.argsEnv]
      refine respects_argsEnv_two rest vs ?_
      simpa only [Env.respects, Env.updateConst_binary] using h

/-- Respect for an arity-three symbol survives the argument-binding fold; each
    step rebinds a `value` constant, which never touches the ternary table. -/
private theorem respects_argsEnv_three {s : FOL.Symbol .three} :
    ∀ (args : List String) (vs : List Runtime.Val) {ρ : Env},
      ρ.respects (some s) → (Spec.argsEnv ρ args vs).respects (some s)
  | [], _, _, h => h
  | _ :: _, [], _, h => h
  | _ :: rest, _ :: vs, ρ, h => by
      simp only [Spec.argsEnv]
      refine respects_argsEnv_three rest vs ?_
      simpa only [Env.respects, Env.updateConst_ternary] using h

/-! ## `specWf`: predicate-transformer well-formedness -/

/-- The `specWf` obligation from a base well-formedness fact in the fragment's
    signature: monotonicity carries it to any signature containing that
    signature. -/
theorem specWf_of_base {fragment : Registry} {i : Intrinsic}
    (hbase : PredTrans.wfIn
      ((Intrinsic.sigOf fragment).declVars (Spec.argVars i.specArgs)) i.spec.pred)
    {Δ : Signature} (hsub : (Intrinsic.sigOf fragment).Subset Δ) (hwf : Δ.wf) :
    PredTrans.wfIn (Δ.declVars (Spec.argVars i.specArgs)) i.spec.pred :=
  PredTrans.wfIn_mono hbase
    (Signature.Subset.declVars hsub (Spec.argVars i.specArgs))
    (Signature.wf_declVars hwf)

/-! ## Embeddings: Lean types embedded into values

A `Embedding` records how a Lean carrier type sits inside `Runtime.Val` at a
given TinyML type: an injection, a matching projection, and the `is-of`
predicate that recognizes the type at the value sort. The coherence laws
live in `Embedding.Lawful`. -/

/-- How a Lean carrier is represented as runtime values of a TinyML type: an
    injection, its retracting projection, the semantic type predicate
    `typePred` — the resource left of a typing fact after peeling off the
    injection (`emp` for the base types) — and an optional `is-of` value-sort
    predicate recognizing the type (absent when the type is a variable).
    Pure data; see `Embedding.Lawful` for the laws. -/
structure Embedding where
  typ      : TinyML.SchemaTyp
  carrier  : Type
  inject   : carrier → Runtime.Val
  project  : Runtime.Val → carrier
  typePred : ∀ [MicaGS.{0} HasLC.hasLC Sig],
              (TinyML.TyVar → TinyML.Typ) → TinyML.World → carrier → iProp
  isOf     : Option (UnPred .value)

/-- Integer projection of a runtime value, matching FOL's `toInt`. -/
def valInt : Runtime.Val → Int
  | .int n => n
  | _      => 0

/-- 32-bit integer projection of a runtime value, matching FOL's `toInt32`. -/
def valInt32 : Runtime.Val → BitVec 32
  | .int32 bits => bits
  | _ => 0

/-- 64-bit integer projection of a runtime value, matching FOL's `toInt64`. -/
def valInt64 : Runtime.Val → BitVec 64
  | .int64 bits => bits
  | _ => 0

/-- Boolean projection of a runtime value, matching FOL's `toBool`. -/
def valBool : Runtime.Val → Bool
  | .bool b => b
  | _       => false

/-- Character projection of a runtime value, matching FOL's `toChar`. -/
def valChar : Runtime.Val → UInt8
  | .char c => c
  | _       => 0

/-- Byte-string projection of a runtime value, matching FOL's `toString`. -/
def valStr : Runtime.Val → List UInt8
  | .str s => s
  | _      => []

/-- Float projection of a runtime value, matching FOL's `toFloat`. -/
def valFloat : Runtime.Val → UInt64
  | .float b => b
  | _        => 0

/-- Vector projection of a runtime value, matching FOL's `toVec`. -/
def valVec : Runtime.Val → List Runtime.Val
  | .vec l => l
  | _      => []

/-- Integers as `.int` values. -/
def Embedding.int  : Embedding :=
  ⟨.int, Int, .int, valInt, fun _ _ _ => iprop(emp), some .isInt⟩
/-- 32-bit integers as `.int32` values. -/
def Embedding.int32 : Embedding :=
  ⟨.int32, BitVec 32, .int32, valInt32, fun _ _ _ => iprop(emp), some .isInt32⟩
/-- 64-bit integers as `.int64` values. -/
def Embedding.int64 : Embedding :=
  ⟨.int64, BitVec 64, .int64, valInt64, fun _ _ _ => iprop(emp), some .isInt64⟩
/-- Booleans as `.bool` values. -/
def Embedding.bool : Embedding :=
  ⟨.bool, Bool, .bool, valBool, fun _ _ _ => iprop(emp), some .isBool⟩
/-- Bytes as `.char` values. -/
def Embedding.char : Embedding :=
  ⟨.char, UInt8, .char, valChar, fun _ _ _ => iprop(emp), some .isChar⟩
/-- Byte strings as `.str` values. -/
def Embedding.str  : Embedding :=
  ⟨.string, List UInt8, .str, valStr, fun _ _ _ => iprop(emp), some .isStr⟩
/-- IEEE binary64 bit-patterns as `.float` values. -/
def Embedding.float : Embedding :=
  ⟨.float, UInt64, .float, valFloat, fun _ _ _ => iprop(emp), some .isFloat⟩

/-- A type variable: any runtime value, with its typing at the
    instantiated type as the type predicate. No `is-of` recognizer, so no
    type axiom. -/
def Embedding.poly (v : TinyML.TyVar) : Embedding :=
  ⟨.tvar v, Runtime.Val, id, id,
    fun σ W w => TinyML.ValHasType W w (σ v), none⟩

/-- An arbitrary type scheme represented by the runtime value itself. -/
def Embedding.logical (typ : TinyML.SchemaTyp) : Embedding :=
  ⟨typ, Runtime.Val, id, id,
    fun σ W w => TinyML.ValHasType W w (TinyML.Typ.subst σ typ), none⟩

/-- The empty type: no closed values inhabit it. Trivial `Unit` carrier with a
    `False` type predicate, so only an intrinsic with an unsatisfiable domain
    can use it as a result. No `is-of` recognizer, so no type axiom. -/
def Embedding.empty : Embedding :=
  ⟨.empty, Unit, fun _ => .unit, fun _ => (), fun _ _ _ => iprop(False), none⟩

/-- Vectors of an arbitrary element scheme: element lists, with the big-sep of
    instantiated element typings as the type predicate. -/
def Embedding.vec (elem : TinyML.SchemaTyp) : Embedding :=
  ⟨.vec elem, List Runtime.Val, .vec, valVec,
    fun σ W l => iprop([∗list] w ∈ l, TinyML.ValHasType W w (TinyML.Typ.subst σ elem)),
    some .isVec⟩

/-- Coherence laws for an `Embedding`. The `member`/`intro` laws are stated at
    every instantiation `e.typ.subst σ` of the embedding's type. -/
structure Embedding.Lawful (e : Embedding) where
  project_inject : ∀ x, e.project (e.inject x) = x
  isOf_wf        : ∀ Δ p, e.isOf = some p → p.wfIn Δ
  isOf_inject    : ∀ (ρ : Env) (x : e.carrier) p, e.isOf = some p →
                     UnPred.eval ρ p (e.inject x)
  member         : ∀ [MicaGS HasLC.hasLC Sig] (σ : TinyML.TyVar → TinyML.Typ)
                     (W : TinyML.World) (w : Runtime.Val),
                     TinyML.ValHasType W w (TinyML.Typ.subst σ e.typ) ⊣⊢
                       iprop(∃ x, ⌜w = e.inject x⌝ ∗ e.typePred σ W x)
  intro          : ∀ [MicaGS HasLC.hasLC Sig] (σ : TinyML.TyVar → TinyML.Typ)
                     (W : TinyML.World) (x : e.carrier),
                     e.typePred σ W x ⊢ TinyML.ValHasType W (e.inject x) (TinyML.Typ.subst σ e.typ)

/-- Lift the pure membership fact of an embedding with trivial type predicate
    to the predicate-carrying `member` shape (`∗ emp` under the existential). -/
theorem pure_member [MicaGS HasLC.hasLC Sig] {P : iProp} {α : Type} {φ : α → Prop}
    (h : P ⊣⊢ iprop(⌜∃ x, φ x⌝)) : P ⊣⊢ iprop(∃ x, ⌜φ x⌝ ∗ emp) :=
  h.trans (pure_exists.symm.trans (exists_congr fun _ => sep_emp.symm))

/-- Integers are a lawful embedding. -/
def Embedding.lawfulInt : Embedding.int.Lawful where
  project_inject _ := rfl
  isOf_wf _ _ h := by cases h; trivial
  isOf_inject _ _ _ h := by cases h; simp [Embedding.int]
  member _ W w := pure_member (φ := fun x => w = .int x)
    (by simpa [Embedding.int, TinyML.Typ.subst] using TinyML.ValHasType.int W w)
  intro _ W x := by simpa [Embedding.int, TinyML.Typ.subst] using TinyML.ValHasType.int_intro W x

/-- 32-bit integers are a lawful embedding. -/
def Embedding.lawfulInt32 : Embedding.int32.Lawful where
  project_inject _ := rfl
  isOf_wf _ _ h := by cases h; trivial
  isOf_inject _ _ _ h := by cases h; simp [Embedding.int32]
  member _ W w := pure_member (φ := fun x => w = .int32 x)
    (by simpa [Embedding.int32, TinyML.Typ.subst] using TinyML.ValHasType.int32 W w)
  intro _ W x := by
    simpa [Embedding.int32, TinyML.Typ.subst] using TinyML.ValHasType.int32_intro W x

/-- 64-bit integers are a lawful embedding. -/
def Embedding.lawfulInt64 : Embedding.int64.Lawful where
  project_inject _ := rfl
  isOf_wf _ _ h := by cases h; trivial
  isOf_inject _ _ _ h := by cases h; simp [Embedding.int64]
  member _ W w := pure_member (φ := fun x => w = .int64 x)
    (by simpa [Embedding.int64, TinyML.Typ.subst] using TinyML.ValHasType.int64 W w)
  intro _ W x := by
    simpa [Embedding.int64, TinyML.Typ.subst] using TinyML.ValHasType.int64_intro W x

/-- Booleans are a lawful embedding. -/
def Embedding.lawfulBool : Embedding.bool.Lawful where
  project_inject _ := rfl
  isOf_wf _ _ h := by cases h; trivial
  isOf_inject _ _ _ h := by cases h; simp [Embedding.bool]
  member _ W w := pure_member (φ := fun x => w = .bool x)
    (by simpa [Embedding.bool, TinyML.Typ.subst] using TinyML.ValHasType.bool W w)
  intro _ W x := by simpa [Embedding.bool, TinyML.Typ.subst] using TinyML.ValHasType.bool_intro W x

/-- Characters are a lawful embedding. -/
def Embedding.lawfulChar : Embedding.char.Lawful where
  project_inject _ := rfl
  isOf_wf _ _ h := by cases h; trivial
  isOf_inject _ _ _ h := by cases h; simp [Embedding.char]
  member _ W w := pure_member (φ := fun x => w = .char x)
    (by simpa [Embedding.char, TinyML.Typ.subst] using TinyML.ValHasType.char W w)
  intro _ W x := by simpa [Embedding.char, TinyML.Typ.subst] using TinyML.ValHasType.char_intro W x

/-- Byte strings are a lawful embedding. -/
def Embedding.lawfulStr : Embedding.str.Lawful where
  project_inject _ := rfl
  isOf_wf _ _ h := by cases h; trivial
  isOf_inject _ _ _ h := by cases h; simp [Embedding.str]
  member _ W w := pure_member (φ := fun x => w = .str x)
    (by simpa [Embedding.str, TinyML.Typ.subst] using TinyML.ValHasType.string W w)
  intro _ W x := by simpa [Embedding.str, TinyML.Typ.subst] using TinyML.ValHasType.string_intro W x

/-- Floats are a lawful embedding. -/
def Embedding.lawfulFloat : Embedding.float.Lawful where
  project_inject _ := rfl
  isOf_wf _ _ h := by cases h; trivial
  isOf_inject _ _ _ h := by cases h; simp [Embedding.float]
  member _ W w := pure_member (φ := fun x => w = .float x)
    (by simpa [Embedding.float, TinyML.Typ.subst] using TinyML.ValHasType.float W w)
  intro _ W x := by simpa [Embedding.float, TinyML.Typ.subst] using TinyML.ValHasType.float_intro W x

/-- Type variables are a lawful embedding: the type predicate is the typing fact itself. -/
def Embedding.lawfulPoly (v : TinyML.TyVar) : (Embedding.poly v).Lawful where
  project_inject _ := rfl
  isOf_wf _ _ h := nomatch h
  isOf_inject _ _ _ h := nomatch h
  member σ W w := by
    simp only [Embedding.poly, TinyML.Typ.subst]
    constructor
    · iintro H
      iexists w
      isplitl []
      · ipureintro; rfl
      · iexact H
    · iintro ⟨%x, %hw, H⟩
      obtain rfl := hw
      iexact H
  intro σ W x := by
    simp only [Embedding.poly, TinyML.Typ.subst]
    exact .rfl

/-- The identity representation of an arbitrary logical type is lawful. -/
def Embedding.lawfulLogical (typ : TinyML.SchemaTyp) : (Embedding.logical typ).Lawful where
  project_inject _ := rfl
  isOf_wf _ _ h := nomatch h
  isOf_inject _ _ _ h := nomatch h
  member σ W w := by
    simp only [Embedding.logical]
    constructor
    · iintro H
      iexists w
      isplitl []
      · ipureintro; rfl
      · iexact H
    · iintro ⟨%x, %hw, H⟩
      obtain rfl := hw
      iexact H
  intro _ _ _ := .rfl

/-- Vectors are a lawful embedding: exactly the `ValHasType.vec` API. -/
def Embedding.lawfulVec (elem : TinyML.SchemaTyp) : (Embedding.vec elem).Lawful where
  project_inject _ := rfl
  isOf_wf _ _ h := by cases h; trivial
  isOf_inject _ _ _ h := by cases h; simp [Embedding.vec]
  member σ W w := by
    simpa [Embedding.vec, TinyML.Typ.subst] using TinyML.ValHasType.vec W w (TinyML.Typ.subst σ elem)
  intro σ W l := by
    simpa [Embedding.vec, TinyML.Typ.subst] using TinyML.ValHasType.vec_intro W l (TinyML.Typ.subst σ elem)

/-! ## Name-based term builders -/

/-- Uninterpreted unary value symbol `name` applied to `x`. -/
def unTerm (name : String) (x : Term .value) : Term .value :=
  .unop (.uninterpreted name .value .value) x

/-- Uninterpreted binary value symbol `name` applied to `x` and `y`. -/
def binTerm (name : String) (x y : Term .value) : Term .value :=
  .binop (.uninterpreted name .value .value .value) x y

/-- Uninterpreted ternary value symbol `name` applied to `x`, `y`, and `z`. -/
def terTerm (name : String) (x y z : Term .value) : Term .value :=
  .terop (.uninterpreted name .value .value .value .value) x y z

/-- Uninterpreted nullary value symbol `name` as a term. -/
def constTerm (name : String) : Term .value :=
  .const (.uninterpreted name .value)

namespace Pure

/-! ## Encodings: how a pure intrinsic reaches the solver -/

/-- How a pure intrinsic reaches the solver. A `symbol` encoding declares an
    uninterpreted symbol and constrains it with the given defining axiom. A
    `direct` encoding puts the value term itself in the query: it declares
    nothing and asserts nothing, so the solver reads native operations instead
    of an uninterpreted function under a trigger. -/
inductive Encoding (n : Arity) where
  | symbol (defAxiom : Formula)
  | direct (encode : Arity.tup n (Term .value) → Term .value)

/-- The well-formedness obligation of an encoding: a `symbol` encoding must put
    its defining axiom in the signature, a `direct` encoding its term. -/
def Encoding.wf {n : Arity} (Δ : Signature) : Encoding n → Prop
  | .symbol φ => φ.wfIn Δ
  | .direct e => IntrinsicFOL.Lawful (.direct e)

/-! ## Builder for pure zero-arity intrinsics

`Pure.Zero` bundles the *computational* content of a pure constant intrinsic:
its name/path, result embedding, carrier value, and SMT defining axiom. From
this alone the `Intrinsic` and its FOL symbol are built (`toIntrinsic`). The
proof obligations live in `Pure.Zero.Lawful`. -/

/-- The computational data of a pure zero-arity intrinsic. -/
structure Zero where
  name : String
  path : Option (String × List String)
  res  : Embedding
  f    : res.carrier
  enc  : Encoding .zero

/-- The symbol that a `symbol` encoding declares: the standard interpretation
    injects the carrier value. -/
def Zero.sym (b : Zero) : FOL.Symbol .zero where
  name   := b.name
  interp := fun () => b.res.inject b.f

/-- How the intrinsic reaches the solver. -/
def Zero.fol (b : Zero) : IntrinsicFOL .zero :=
  match b.enc with
  | .symbol _ => .symbol b.sym
  | .direct e => .direct e

/-- The term that the spec asserts the result equal to. -/
def Zero.opTerm (b : Zero) : Term .value :=
  b.fol.term .zero ()

/-- The result-typing axiom, generated from `res` when it has a recognizer. A
    direct encoding needs none: its term applies the constructor itself. -/
def Zero.typeAxiom (b : Zero) : Option Formula :=
  match b.enc with
  | .direct _ => none
  | .symbol _ => b.res.isOf.map fun p => .unpred p b.opTerm

/-- The axioms that the encoding contributes. A direct encoding contributes
    none. -/
def Zero.axioms (b : Zero) : List Axiom :=
  match b.enc with
  | .direct _ => []
  | .symbol φ => ⟨φ, .low⟩ :: (b.typeAxiom.map (⟨·, .low⟩)).toList

/-- The intrinsic built from `b`: a literal `Intrinsic.mk`. -/
def Zero.toIntrinsic (b : Zero) : Intrinsic where
  arity  := .zero
  name   := b.name
  path   := b.path
  reduce := Reduce.pure fun () v => v = b.res.inject b.f
  wp     := fun () Q => Q (b.res.inject b.f)
  argTys := []
  retTy  := b.res.typ
  spec   :=
    { args  := []
      ghost := []
      pred  := .ret ⟨"ret",
        .assert (.eq .value (.var .value "ret") b.opTerm) (.ret ())⟩ }
  folTerm := some b.fol
  axioms := b.axioms

@[simp] theorem Zero.toWp_eq (b : Zero) (Q : Runtime.Val → iProp) :
    b.toIntrinsic.toWp [] Q = Q (b.res.inject b.f) := rfl

@[simp] theorem Zero.toReduce_eq (b : Zero) (v : Runtime.Val) (μ μ' : TinyML.Heap) :
    b.toIntrinsic.toReduce [] μ v μ' = (v = b.res.inject b.f ∧ μ' = μ) := rfl

/-- What the encoding must tell the solver truthfully. A `symbol` encoding must
    satisfy its defining axiom. A `direct` encoding must compute `f`. -/
def Zero.encEval (b : Zero) (dependencies : Registry) : Prop :=
  match b.enc with
  | .symbol φ => ∀ ρ : Env, (∀ d ∈ dependencies, ρ.respects d.folSym) →
      ρ.respects (some b.sym) → Formula.eval ρ φ
  | .direct e => ∀ ρ : Env, Term.eval ρ (e ()) = b.res.inject b.f

/-- Proof obligations for a pure zero-arity intrinsic and its additional
    registry dependencies. The `nameFresh` premise
    keeps the generated constant symbol distinct from the spec's `"ret"`
    binder, since both live in the value-constant namespace. -/
structure Zero.Lawful (dependencies : Registry) (b : Zero) where
  resL         : b.res.Lawful
  nameFresh    : b.name ≠ "ret"
  semWellTyped : ∀ [MicaGS HasLC.hasLC Sig] (σ : TinyML.TyVar → TinyML.Typ)
                 (W : TinyML.World), iprop(emp) ⊢ b.res.typePred σ W b.f
  specBaseWf   : PredTrans.wfIn
                 ((Intrinsic.sigOf (b.toIntrinsic :: dependencies)).declVars
                   (Spec.argVars b.toIntrinsic.specArgs)) b.toIntrinsic.spec.pred
  encWf        : b.enc.wf (Intrinsic.sigOf (b.toIntrinsic :: dependencies))
  typeWf       : ∀ φ, b.typeAxiom = some φ →
                 φ.wfIn (Intrinsic.sigOf (b.toIntrinsic :: dependencies))
  encEval      : b.encEval dependencies

/-- Whichever encoding is in use, the term the spec asserts evaluates, in the
    spec's own environment, to what `f` computes. -/
theorem Zero.Lawful.opEval {dependencies : Registry} {b : Zero}
    (l : b.Lawful dependencies) (ρ : Env)
    (hρ : ∀ d ∈ b.toIntrinsic :: dependencies, ρ.respects d.folSym) :
    Term.eval (ρ.updateConst .value "ret" (b.res.inject b.f)) b.opTerm
      = b.res.inject b.f := by
  have hev := l.encEval
  simp only [Zero.opTerm, Zero.fol]
  cases hb : b.enc with
  | direct e =>
    simp only [Zero.encEval, hb] at hev
    exact hev _
  | symbol φ =>
    have hresp : ρ.respects (some b.sym) := by
      simpa [Intrinsic.folSym, Zero.toIntrinsic, Zero.fol, hb]
        using hρ b.toIntrinsic (by simp)
    have hconst : (ρ.updateConst .value "ret" (b.res.inject b.f)).lookupConst
        .value b.name = b.res.inject b.f := by
      rw [Env.lookupConst_updateConst_ne l.nameFresh]
      simpa [Env.respects, Zero.sym] using hresp
    simpa [IntrinsicFOL.term, Term.eval, Const.denote] using hconst

/-- The `IntrinsicSound` instance for a pure zero-arity intrinsic. -/
@[reducible] def Zero.Lawful.sound {dependencies : Registry} {b : Zero}
    (l : b.Lawful dependencies) :
    IntrinsicSound (b.toIntrinsic :: dependencies) b.toIntrinsic where
  argLen := rfl
  specWf := fun _ hsub hwf => specWf_of_base l.specBaseWf hsub hwf
  wp_sound := by
    intro _ ctx hctx vs Φ
    match vs with
    | _ :: _ => exact false_elim
    | [] =>
      have hred : ∀ μ v μ',
          ctx b.toIntrinsic.name [] μ v μ' ↔ v = b.res.inject b.f ∧ μ' = μ := by
        intro μ v μ'
        rw [hctx]
        simp only [Zero.toIntrinsic, Intrinsic.toReduce_zero_of_arity, Reduce.pure]
      rw [Zero.toWp_eq]
      istart
      iintro HΦ
      iapply (wp.prim_pure hred ⟨b.res.inject b.f, rfl⟩)
      iintro %v %hv
      subst hv
      iexact HΦ
  bridge := by
    intro _ σ W vs ρ Φ hρ
    show TinyML.ValsHaveTypes W vs [] ∗ _ ⊢ _
    match vs with
    | _ :: _ => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [] =>
      simp only [Zero.toIntrinsic, Intrinsic.toWp_zero_of_arity]
      refine (sep_mono_left (TinyML.ValsHaveTypes.nil W).1).trans ?_
      refine emp_sep.1.trans ?_
      refine (assert_ret_apply W _ "ret" _ _ (b.res.inject b.f) ?_).trans ?_
      · exact (l.opEval ρ hρ).symm
      · iintro Hwand
        iapply Hwand
        exact (l.semWellTyped σ W).trans (l.resL.intro σ W b.f)
  axiomWf := by
    intro Δ hsub hwf a hφ
    simp only [Zero.toIntrinsic, Zero.axioms] at hφ
    have hw := l.encWf
    cases hb : b.enc with
    | direct e => rw [hb] at hφ; cases hφ
    | symbol φ =>
      rw [hb] at hφ hw
      simp only [Encoding.wf] at hw
      simp only [List.mem_cons, Option.mem_toList, Option.map_eq_some_iff] at hφ
      rcases hφ with rfl | ⟨ψ, hψ, rfl⟩
      · exact Formula.wfIn_mono _ hw hsub hwf
      · exact Formula.wfIn_mono _ (l.typeWf ψ hψ) hsub hwf
  proof := by
    intro ρ hdeps a hφ
    simp only [Zero.toIntrinsic, Zero.axioms] at hφ
    have hev := l.encEval
    cases hb : b.enc with
    | direct e => rw [hb] at hφ; cases hφ
    | symbol φ =>
      rw [hb] at hφ
      simp only [Zero.encEval, hb] at hev
      have hresp : ρ.respects (some b.sym) := by
        simpa [Intrinsic.folSym, Zero.toIntrinsic, Zero.fol, hb]
          using hdeps b.toIntrinsic (by simp)
      simp only [List.mem_cons, Option.mem_toList, Option.map_eq_some_iff,
        Zero.typeAxiom, hb] at hφ
      rcases hφ with rfl | ⟨ψ, ⟨p, hp, rfl⟩, rfl⟩
      · exact hev ρ (fun d hd => hdeps d (List.mem_cons_of_mem _ hd)) hresp
      · simp only [Formula.eval, Zero.opTerm, Zero.fol, hb, IntrinsicFOL.term,
          Term.eval, Const.denote]
        have hconst : ρ.consts .value b.sym.name = b.res.inject b.f := by
          simpa [Env.respects, Env.lookupConst, Zero.sym] using hresp
        rw [hconst]
        exact l.resL.isOf_inject _ _ p hp
  folWf := by
    intro f hf
    simp only [Zero.toIntrinsic, Option.some.injEq] at hf
    subst hf
    have hw := l.encWf
    simp only [Zero.fol]
    cases hb : b.enc with
    | symbol φ => trivial
    | direct e => rw [hb] at hw; exact hw

/-! ## Builder for pure unary intrinsics

`Pure.Unary` bundles the *computational* content of a pure unary intrinsic: its
name/path, the argument and result embeddings, the carrier function `f`, and the
SMT defining axiom. From this alone the `Intrinsic` and its FOL symbol are built
(`toIntrinsic`). The proof obligations live in `Pure.Unary.Lawful`. -/

/-- The computational data of a pure unary intrinsic. `dom` is the carrier-level
    domain guarding `reduce`/`wp`; `pre` is the matching FOL precondition as a
    function of the spec's argument name (the builder applies it at `"a"`). For
    total intrinsics: `dom := fun _ => True`, `pre := none`. -/
structure Unary where
  name : String
  path : Option (String × List String)
  arg  : Embedding
  res  : Embedding
  f    : arg.carrier → res.carrier
  dom  : arg.carrier → Prop
  pre  : Option (String → Formula)
  enc  : Encoding .one

/-- The symbol that a `symbol` encoding declares: the standard interpretation
    projects, applies `f`, injects. -/
def Unary.sym (b : Unary) : FOL.Symbol .one where
  name   := b.name
  interp := fun a => b.res.inject (b.f (b.arg.project a))

/-- How the intrinsic reaches the solver. -/
def Unary.fol (b : Unary) : IntrinsicFOL .one :=
  match b.enc with
  | .symbol _ => .symbol b.sym
  | .direct e => .direct e

/-- The term that the spec asserts the result equal to. -/
def Unary.opTerm (b : Unary) (x : Term .value) : Term .value :=
  b.fol.term .one x

/-- The result-typing axiom, generated from `res` when it has a recognizer. A
    direct encoding needs none: its term applies the constructor itself. -/
def Unary.typeAxiom (b : Unary) : Option Formula :=
  match b.enc with
  | .direct _ => none
  | .symbol _ => b.res.isOf.map fun p =>
      .forall_ "a" .value [.term (b.opTerm (.var .value "a"))] <|
        .unpred p (b.opTerm (.var .value "a"))

/-- The axioms that the encoding contributes. A direct encoding contributes
    none. -/
def Unary.axioms (b : Unary) : List Axiom :=
  match b.enc with
  | .direct _ => []
  | .symbol φ => ⟨φ, .high⟩ :: (b.typeAxiom.map (⟨·, .high⟩)).toList

/-- The intrinsic built from `b`: a literal `Intrinsic.mk`. -/
def Unary.toIntrinsic (b : Unary) : Intrinsic where
  arity  := .one
  name   := b.name
  path   := b.path
  reduce := Reduce.pure fun a v =>
    ∃ x, a = b.arg.inject x ∧ b.dom x ∧ v = b.res.inject (b.f x)
  wp     := fun a Q => iprop(∃ x, ⌜a = b.arg.inject x ∧ b.dom x⌝ ∗ Q (b.res.inject (b.f x)))
  argTys := [b.arg.typ]
  retTy  := b.res.typ
  spec   :=
    { args  := ["a"]
      ghost := []
      pred  := withPre (b.pre.map (· "a")) <| .ret ⟨"ret",
        .assert (.eq .value (.var .value "ret")
          (b.opTerm (.var .value "a"))) (.ret ())⟩ }
  folTerm := some b.fol
  axioms := b.axioms

@[simp] theorem Unary.toWp_eq (b : Unary) (a : Runtime.Val) (Q : Runtime.Val → iProp) :
    b.toIntrinsic.toWp [a] Q
      = iprop(∃ x, ⌜a = b.arg.inject x ∧ b.dom x⌝ ∗ Q (b.res.inject (b.f x))) := rfl

@[simp] theorem Unary.toReduce_eq (b : Unary) (a v : Runtime.Val) (μ μ' : TinyML.Heap) :
    b.toIntrinsic.toReduce [a] μ v μ' =
      ((∃ x, a = b.arg.inject x ∧ b.dom x ∧ v = b.res.inject (b.f x)) ∧ μ' = μ) := rfl

@[simp] theorem Unary.spec_pred (b : Unary) :
    b.toIntrinsic.spec.pred = withPre (b.pre.map (· "a"))
      (.ret ⟨"ret",
        .assert (.eq .value (.var .value "ret")
          (b.opTerm (.var .value "a"))) (.ret ())⟩) := rfl

@[simp] theorem Unary.argTys_map_subst (b : Unary) (σ : TinyML.TyVar → TinyML.Typ) :
    b.toIntrinsic.argTys.map (TinyML.Typ.subst σ) = [TinyML.Typ.subst σ b.arg.typ] := rfl

@[simp] theorem Unary.retTy_subst (b : Unary) (σ : TinyML.TyVar → TinyML.Typ) :
    TinyML.Typ.subst σ b.toIntrinsic.retTy = TinyML.Typ.subst σ b.res.typ := rfl

/-- What the encoding must tell the solver truthfully. A `symbol` encoding must
    satisfy its defining axiom. A `direct` encoding must compute `f`. -/
def Unary.encEval (b : Unary) (dependencies : Registry) : Prop :=
  match b.enc with
  | .symbol φ => ∀ ρ : Env, (∀ d ∈ dependencies, ρ.respects d.folSym) →
      ρ.respects (some b.sym) → Formula.eval ρ φ
  | .direct e => ∀ (ρ : Env) (x : b.arg.carrier),
      ρ.lookupConst .value "a" = b.arg.inject x →
      Term.eval ρ (e (.var .value "a")) = b.res.inject (b.f x)

/-- Proof obligations for a pure unary intrinsic and its additional registry
    dependencies. `domSound` extracts the
    carrier-level domain from the evaluated precondition; when `pre = none` the
    hypothesis is vacuous, so `dom` must hold unconditionally. -/
structure Unary.Lawful (dependencies : Registry) (b : Unary) where
  argL         : b.arg.Lawful
  resL         : b.res.Lawful
  domSound     : ∀ (ρ : Env) (x : b.arg.carrier),
                 (∀ d ∈ dependencies, ρ.respects d.folSym) →
                 (∀ p, b.pre = some p →
                   (p "a").eval (ρ.updateConst .value "a" (b.arg.inject x))) →
                 b.dom x
  semWellTyped : ∀ [MicaGS HasLC.hasLC Sig] (σ : TinyML.TyVar → TinyML.Typ)
                 (W : TinyML.World) (x : b.arg.carrier), b.dom x →
                 b.arg.typePred σ W x ⊢ b.res.typePred σ W (b.f x)
  specBaseWf   : PredTrans.wfIn
                 ((Intrinsic.sigOf (b.toIntrinsic :: dependencies)).declVars
                   (Spec.argVars b.toIntrinsic.specArgs)) b.toIntrinsic.spec.pred
  encWf        : b.enc.wf (Intrinsic.sigOf (b.toIntrinsic :: dependencies))
  typeWf       : ∀ φ, b.typeAxiom = some φ →
                 φ.wfIn (Intrinsic.sigOf (b.toIntrinsic :: dependencies))
  encEval      : b.encEval dependencies

/-- Whichever encoding is in use, the term the spec asserts evaluates, in the
    spec's own environment, to what `f` computes. -/
theorem Unary.Lawful.opEval {dependencies : Registry} {b : Unary}
    (l : b.Lawful dependencies) (ρ : Env) (x : b.arg.carrier)
    (hρ : ∀ d ∈ b.toIntrinsic :: dependencies, ρ.respects d.folSym) :
    Term.eval ((Spec.argsEnv ρ b.toIntrinsic.specArgs [b.arg.inject x]).updateConst
        .value "ret" (b.res.inject (b.f x))) (b.opTerm (.var .value "a"))
      = b.res.inject (b.f x) := by
  have hev := l.encEval
  simp only [Unary.opTerm, Unary.fol]
  cases hb : b.enc with
  | direct e =>
    simp only [Unary.encEval, hb] at hev
    exact hev _ x rfl
  | symbol φ =>
    have hresp : ρ.respects (some b.sym) := by
      simpa [Intrinsic.folSym, Unary.toIntrinsic, Unary.fol, hb]
        using hρ b.toIntrinsic (by simp)
    have hun : (Spec.argsEnv ρ b.toIntrinsic.specArgs [b.arg.inject x]).unary
        .value .value b.name = b.sym.interp := by
      simpa [Env.respects, Unary.sym] using
        respects_argsEnv_one b.toIntrinsic.specArgs [b.arg.inject x] hresp
    show (Spec.argsEnv ρ b.toIntrinsic.specArgs [b.arg.inject x]).unary
      .value .value b.name (b.arg.inject x) = b.res.inject (b.f x)
    simp [hun, Unary.sym, l.argL.project_inject]

/-- The `IntrinsicSound` instance for a pure unary intrinsic. -/
@[reducible] def Unary.Lawful.sound {dependencies : Registry} {b : Unary}
    (l : b.Lawful dependencies) :
    IntrinsicSound (b.toIntrinsic :: dependencies) b.toIntrinsic where
  argLen := rfl
  specWf := fun _ hsub hwf => specWf_of_base l.specBaseWf hsub hwf
  wp_sound := by
    intro _ ctx hctx vs Φ
    match vs with
    | [] => exact false_elim
    | _ :: _ :: _ => exact false_elim
    | [a] =>
      have hred : ∀ x, b.dom x → ∀ μ v μ',
          ctx b.toIntrinsic.name [b.arg.inject x] μ v μ'
            ↔ v = b.res.inject (b.f x) ∧ μ' = μ := by
        intro x hdom μ v μ'
        rw [hctx]
        simp only [Unary.toIntrinsic, Intrinsic.toReduce_one_of_arity, Reduce.pure]
        constructor
        · rintro ⟨⟨x', hx, _, hv⟩, hμ⟩
          have hxx : x = x' := by
            have := congrArg b.arg.project hx
            rwa [l.argL.project_inject, l.argL.project_inject] at this
          subst hxx
          exact ⟨hv, hμ⟩
        · rintro ⟨hv, hμ⟩
          exact ⟨⟨x, rfl, hdom, hv⟩, hμ⟩
      show iprop(∃ x, ⌜a = b.arg.inject x ∧ b.dom x⌝ ∗ Φ (b.res.inject (b.f x))) ⊢ _
      istart
      iintro ⟨%x, %ha, HΦ⟩
      obtain ⟨rfl, hdom⟩ := ha
      iapply (wp.prim_pure (hred x hdom) ⟨_, rfl⟩)
      iintro %v %hv
      subst hv
      iexact HΦ
  bridge := by
    intro _ σ W vs ρ Φ hρ
    simp only [Unary.argTys_map_subst, Unary.retTy_subst, Unary.spec_pred]
    match vs with
    | [] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | _ :: _ :: _ =>
        exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [v] =>
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons W v [] _ _).1 $$ Hvs
      icases Hcons with ⟨Hv, _⟩
      ihave Hveq := (l.argL.member σ W v).1 $$ Hv
      icases Hveq with ⟨%x, %hw, Hrel⟩
      obtain rfl := hw
      ihave Hsplit := withPre_apply W _ _ _ _ $$ Hpred
      icases Hsplit with ⟨%hpre, Hpost⟩
      have hdom : b.dom x := by
        refine l.domSound ρ x
          (fun d hd => hρ d (List.mem_cons_of_mem _ hd)) fun p hp => ?_
        have h := hpre (p "a") (by rw [hp]; rfl)
        simpa [Spec.argsEnv, ] using h
      ihave Hty : iprop(TinyML.ValHasType W (b.res.inject (b.f x)) (TinyML.Typ.subst σ b.res.typ)) $$ [Hrel]
      · iapply (l.resL.intro σ W (b.f x))
        iapply (l.semWellTyped σ W x hdom)
        iexact Hrel
      simp only [Unary.toIntrinsic, Intrinsic.toWp_one_of_arity]
      iexists x
      isplitr [Hpost Hty]
      · ipureintro; exact ⟨rfl, hdom⟩
      · have hassert : (Formula.eq .value (.var .value "ret")
            (b.opTerm (.var .value "a"))).eval
            ((Spec.argsEnv ρ b.toIntrinsic.specArgs [b.arg.inject x]).updateConst
              .value "ret" (b.res.inject (b.f x))) :=
          (l.opEval ρ x hρ).symm
        refine (sep_mono_left
          (assert_ret_apply W _ "ret" _ _ (b.res.inject (b.f x)) hassert)).trans ?_
        iintro ⟨Hwand, Hty⟩
        iapply Hwand
        iexact Hty
  axiomWf := by
    intro Δ hsub hwf a hφ
    simp only [Unary.toIntrinsic, Unary.axioms] at hφ
    have hw := l.encWf
    cases hb : b.enc with
    | direct e => rw [hb] at hφ; cases hφ
    | symbol φ =>
      rw [hb] at hφ hw
      simp only [Encoding.wf] at hw
      simp only [List.mem_cons, Option.mem_toList, Option.map_eq_some_iff] at hφ
      rcases hφ with rfl | ⟨ψ, hψ, rfl⟩
      · exact Formula.wfIn_mono _ hw hsub hwf
      · exact Formula.wfIn_mono _ (l.typeWf ψ hψ) hsub hwf
  proof := by
    intro ρ hdeps a hφ
    simp only [Unary.toIntrinsic, Unary.axioms] at hφ
    have hev := l.encEval
    cases hb : b.enc with
    | direct e => rw [hb] at hφ; cases hφ
    | symbol φ =>
      rw [hb] at hφ
      simp only [Unary.encEval, hb] at hev
      have hresp : ρ.respects (some b.sym) := by
        simpa [Intrinsic.folSym, Unary.toIntrinsic, Unary.fol, hb]
          using hdeps b.toIntrinsic (by simp)
      simp only [List.mem_cons, Option.mem_toList, Option.map_eq_some_iff,
        Unary.typeAxiom, hb] at hφ
      rcases hφ with rfl | ⟨ψ, ⟨p, hp, rfl⟩, rfl⟩
      · exact hev ρ (fun d hd => hdeps d (List.mem_cons_of_mem _ hd)) hresp
      · simp only [Formula.eval]
        intro y
        have hu : (ρ.updateConst .value "a" y).unary .value .value b.name
            = b.sym.interp := by
          rw [Env.updateConst_unary]
          simpa [Unary.sym] using hresp
        simp only [Unary.opTerm, Unary.fol, hb, IntrinsicFOL.term, Term.eval,
          UnOp.eval, Env.lookupConst_updateConst_same, hu, Unary.sym]
        exact l.resL.isOf_inject _ _ p hp
  folWf := by
    intro f hf
    simp only [Unary.toIntrinsic, Option.some.injEq] at hf
    subst hf
    have hw := l.encWf
    simp only [Unary.fol]
    cases hb : b.enc with
    | symbol φ => trivial
    | direct e => rw [hb] at hw; exact hw

/-! ## Builder for pure binary intrinsics

`Pure.Binary` bundles the *computational* content of a pure binary intrinsic:
its name/path, the argument and result embeddings, the carrier function `f`, and
the SMT defining axiom. From this alone the `Intrinsic` and its FOL symbol are
built (`toIntrinsic`). The proof obligations live in `Pure.Binary.Lawful`. -/

/-- The computational data of a pure binary intrinsic. `dom` is the carrier-level
    domain guarding `reduce`/`wp`; `pre` is the matching FOL precondition as a
    function of the spec's argument names (the builder applies it at `"a"`/`"b"`).
    For total intrinsics: `dom := fun _ _ => True`, `pre := none`. -/
structure Binary where
  name : String
  path : Option (String × List String)
  arg₁ : Embedding
  arg₂ : Embedding
  res  : Embedding
  f    : arg₁.carrier → arg₂.carrier → res.carrier
  dom  : arg₁.carrier → arg₂.carrier → Prop
  pre  : Option (String → String → Formula)
  enc  : Encoding .two

/-- The symbol that a `symbol` encoding declares: the standard interpretation
    projects both arguments, applies `f`, and injects the result. -/
def Binary.sym (b : Binary) : FOL.Symbol .two where
  name   := b.name
  interp := fun (a, c) => b.res.inject (b.f (b.arg₁.project a) (b.arg₂.project c))

/-- How the intrinsic reaches the solver. -/
def Binary.fol (b : Binary) : IntrinsicFOL .two :=
  match b.enc with
  | .symbol _ => .symbol b.sym
  | .direct e => .direct e

/-- The term that the spec asserts the result equal to. -/
def Binary.opTerm (b : Binary) (x y : Term .value) : Term .value :=
  b.fol.term .two (x, y)

/-- The result-typing axiom, generated from `res` when it has a recognizer: the
    op result satisfies the result embedding's `is-of` predicate. A direct
    encoding needs none: its term applies the constructor itself. -/
def Binary.typeAxiom (b : Binary) : Option Formula :=
  match b.enc with
  | .direct _ => none
  | .symbol _ => b.res.isOf.map fun p =>
      .all "a" .value <| .forall_ "b" .value
        [.term (b.opTerm (.var .value "a") (.var .value "b"))] <|
        .unpred p (b.opTerm (.var .value "a") (.var .value "b"))

/-- The axioms that the encoding contributes. A direct encoding contributes
    none. -/
def Binary.axioms (b : Binary) : List Axiom :=
  match b.enc with
  | .direct _ => []
  | .symbol φ => ⟨φ, .high⟩ :: (b.typeAxiom.map (⟨·, .high⟩)).toList

/-- The intrinsic built from `b`: a literal `Intrinsic.mk` so the arity-unfolding
    lemmas (`toReduce_two_of_arity`, `toWp_two_of_arity`) keep firing by `rfl`. -/
def Binary.toIntrinsic (b : Binary) : Intrinsic where
  arity  := .two
  name   := b.name
  path   := b.path
  reduce := Reduce.pure fun (a, c) v =>
    ∃ x y, a = b.arg₁.inject x ∧ c = b.arg₂.inject y ∧ b.dom x y ∧ v = b.res.inject (b.f x y)
  wp     := fun (a, c) Q =>
    iprop(∃ x y, ⌜a = b.arg₁.inject x ∧ c = b.arg₂.inject y ∧ b.dom x y⌝ ∗
      Q (b.res.inject (b.f x y)))
  argTys := [b.arg₁.typ, b.arg₂.typ]
  retTy  := b.res.typ
  spec   :=
    { args  := ["a", "b"]
      ghost := []
      pred  := withPre (b.pre.map (· "a" "b")) <| .ret ⟨"ret",
        .assert (.eq .value (.var .value "ret")
          (b.opTerm (.var .value "a") (.var .value "b"))) (.ret ())⟩ }
  folTerm := some b.fol
  axioms := b.axioms

@[simp] theorem Binary.toWp_eq (b : Binary) (a c : Runtime.Val) (Q : Runtime.Val → iProp) :
    b.toIntrinsic.toWp [a, c] Q =
      iprop(∃ x y, ⌜a = b.arg₁.inject x ∧ c = b.arg₂.inject y ∧ b.dom x y⌝ ∗
        Q (b.res.inject (b.f x y))) := rfl

@[simp] theorem Binary.toReduce_eq (b : Binary) (a c v : Runtime.Val) (μ μ' : TinyML.Heap) :
    b.toIntrinsic.toReduce [a, c] μ v μ' =
      ((∃ x y, a = b.arg₁.inject x ∧ c = b.arg₂.inject y ∧ b.dom x y ∧
        v = b.res.inject (b.f x y)) ∧ μ' = μ) := rfl

@[simp] theorem Binary.spec_pred (b : Binary) :
    b.toIntrinsic.spec.pred = withPre (b.pre.map (· "a" "b"))
      (.ret ⟨"ret",
        .assert (.eq .value (.var .value "ret")
          (b.opTerm (.var .value "a") (.var .value "b"))) (.ret ())⟩) := rfl

@[simp] theorem Binary.argTys_map_subst (b : Binary) (σ : TinyML.TyVar → TinyML.Typ) :
    b.toIntrinsic.argTys.map (TinyML.Typ.subst σ)
      = [TinyML.Typ.subst σ b.arg₁.typ, TinyML.Typ.subst σ b.arg₂.typ] := rfl

@[simp] theorem Binary.retTy_subst (b : Binary) (σ : TinyML.TyVar → TinyML.Typ) :
    TinyML.Typ.subst σ b.toIntrinsic.retTy = TinyML.Typ.subst σ b.res.typ := rfl

/-- What the encoding must tell the solver truthfully. A `symbol` encoding must
    satisfy its defining axiom. A `direct` encoding must compute `f`. -/
def Binary.encEval (b : Binary) (dependencies : Registry) : Prop :=
  match b.enc with
  | .symbol φ => ∀ ρ : Env, (∀ d ∈ dependencies, ρ.respects d.folSym) →
      ρ.respects (some b.sym) → Formula.eval ρ φ
  | .direct e => ∀ (ρ : Env) (x : b.arg₁.carrier) (y : b.arg₂.carrier),
      ρ.lookupConst .value "a" = b.arg₁.inject x →
      ρ.lookupConst .value "b" = b.arg₂.inject y →
      Term.eval ρ (e (.var .value "a", .var .value "b")) = b.res.inject (b.f x y)

/-- Proof obligations for a pure binary intrinsic and its additional registry
    dependencies. -/
structure Binary.Lawful (dependencies : Registry) (b : Binary) where
  argL₁        : b.arg₁.Lawful
  argL₂        : b.arg₂.Lawful
  resL         : b.res.Lawful
  domSound     : ∀ (ρ : Env) (x : b.arg₁.carrier) (y : b.arg₂.carrier),
                 (∀ d ∈ dependencies, ρ.respects d.folSym) →
                 (∀ p, b.pre = some p →
                   (p "a" "b").eval ((ρ.updateConst .value "a" (b.arg₁.inject x)).updateConst
                     .value "b" (b.arg₂.inject y))) →
                 b.dom x y
  semWellTyped : ∀ [MicaGS HasLC.hasLC Sig] (σ : TinyML.TyVar → TinyML.Typ)
                 (W : TinyML.World) (x : b.arg₁.carrier) (y : b.arg₂.carrier),
                 b.dom x y →
                 b.arg₁.typePred σ W x ∗ b.arg₂.typePred σ W y ⊢ b.res.typePred σ W (b.f x y)
  specBaseWf   : PredTrans.wfIn
                 ((Intrinsic.sigOf (b.toIntrinsic :: dependencies)).declVars
                   (Spec.argVars b.toIntrinsic.specArgs)) b.toIntrinsic.spec.pred
  encWf        : b.enc.wf (Intrinsic.sigOf (b.toIntrinsic :: dependencies))
  typeWf       : ∀ φ, b.typeAxiom = some φ →
                 φ.wfIn (Intrinsic.sigOf (b.toIntrinsic :: dependencies))
  encEval      : b.encEval dependencies

/-- Whichever encoding is in use, the term the spec asserts evaluates, in the
    spec's own environment, to what `f` computes. -/
theorem Binary.Lawful.opEval {dependencies : Registry} {b : Binary}
    (l : b.Lawful dependencies) (ρ : Env) (x : b.arg₁.carrier) (y : b.arg₂.carrier)
    (hρ : ∀ d ∈ b.toIntrinsic :: dependencies, ρ.respects d.folSym) :
    Term.eval ((Spec.argsEnv ρ b.toIntrinsic.specArgs
        [b.arg₁.inject x, b.arg₂.inject y]).updateConst
        .value "ret" (b.res.inject (b.f x y)))
        (b.opTerm (.var .value "a") (.var .value "b"))
      = b.res.inject (b.f x y) := by
  have hev := l.encEval
  simp only [Binary.opTerm, Binary.fol]
  cases hb : b.enc with
  | direct e =>
    simp only [Binary.encEval, hb] at hev
    exact hev _ x y rfl rfl
  | symbol φ =>
    have hresp : ρ.respects (some b.sym) := by
      simpa [Intrinsic.folSym, Binary.toIntrinsic, Binary.fol, hb]
        using hρ b.toIntrinsic (by simp)
    have hbin : (Spec.argsEnv ρ b.toIntrinsic.specArgs
        [b.arg₁.inject x, b.arg₂.inject y]).binary .value .value .value b.name
        = fun a c => b.sym.interp (a, c) := by
      simpa [Env.respects, Binary.sym] using
        respects_argsEnv_two b.toIntrinsic.specArgs
          [b.arg₁.inject x, b.arg₂.inject y] hresp
    show (Spec.argsEnv ρ b.toIntrinsic.specArgs
      [b.arg₁.inject x, b.arg₂.inject y]).binary
      .value .value .value b.name (b.arg₁.inject x) (b.arg₂.inject y)
      = b.res.inject (b.f x y)
    simp [hbin, Binary.sym, l.argL₁.project_inject, l.argL₂.project_inject]

/-- The `IntrinsicSound` instance for a pure binary intrinsic. -/
@[reducible] def Binary.Lawful.sound {dependencies : Registry} {b : Binary}
    (l : b.Lawful dependencies) :
    IntrinsicSound (b.toIntrinsic :: dependencies) b.toIntrinsic where
  argLen := rfl
  specWf := fun _ hsub hwf => specWf_of_base l.specBaseWf hsub hwf
  wp_sound := by
    intro _ ctx hctx vs Φ
    match vs with
    | [] => exact false_elim
    | [_] => exact false_elim
    | _ :: _ :: _ :: _ => exact false_elim
    | [a, c] =>
      have hred : ∀ x y, b.dom x y → ∀ μ v μ',
          ctx b.toIntrinsic.name [b.arg₁.inject x, b.arg₂.inject y] μ v μ'
            ↔ v = b.res.inject (b.f x y) ∧ μ' = μ := by
        intro x y hdom μ v μ'
        rw [hctx]
        simp only [Binary.toIntrinsic, Intrinsic.toReduce_two_of_arity, Reduce.pure]
        constructor
        · rintro ⟨⟨x', y', hx, hy, _, hv⟩, hμ⟩
          have hxx : x = x' := by
            have := congrArg b.arg₁.project hx
            rwa [l.argL₁.project_inject, l.argL₁.project_inject] at this
          have hyy : y = y' := by
            have := congrArg b.arg₂.project hy
            rwa [l.argL₂.project_inject, l.argL₂.project_inject] at this
          subst hxx; subst hyy
          exact ⟨hv, hμ⟩
        · rintro ⟨hv, hμ⟩
          exact ⟨⟨x, y, rfl, rfl, hdom, hv⟩, hμ⟩
      show iprop(∃ x y, ⌜a = b.arg₁.inject x ∧ c = b.arg₂.inject y ∧ b.dom x y⌝ ∗
        Φ (b.res.inject (b.f x y))) ⊢ _
      istart
      iintro ⟨%x, %y, %hab, HΦ⟩
      obtain ⟨rfl, rfl, hdom⟩ := hab
      iapply (wp.prim_pure (hred x y hdom) ⟨_, rfl⟩)
      iintro %v %hv
      subst hv
      iexact HΦ
  bridge := by
    intro _ σ W vs ρ Φ hρ
    simp only [Binary.argTys_map_subst, Binary.retTy_subst, Binary.spec_pred]
    show TinyML.ValsHaveTypes W vs [TinyML.Typ.subst σ b.arg₁.typ, TinyML.Typ.subst σ b.arg₂.typ] ∗ _ ⊢ _
    match vs with
    | [] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [_] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | _ :: _ :: _ :: _ =>
        exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [v1, v2] =>
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons W v1 [v2] _ _).1 $$ Hvs
      icases Hcons with ⟨Hv1, Hvs2⟩
      ihave Hcons2 := (TinyML.ValsHaveTypes.cons W v2 [] _ _).1 $$ Hvs2
      icases Hcons2 with ⟨Hv2, _⟩
      ihave Hv1eq := (l.argL₁.member σ W v1).1 $$ Hv1
      icases Hv1eq with ⟨%x, %hw1, Hrel1⟩
      obtain rfl := hw1
      ihave Hv2eq := (l.argL₂.member σ W v2).1 $$ Hv2
      icases Hv2eq with ⟨%y, %hw2, Hrel2⟩
      obtain rfl := hw2
      ihave Hsplit := withPre_apply W _ _ _ _ $$ Hpred
      icases Hsplit with ⟨%hpre, Hpost⟩
      have hdom : b.dom x y := by
        refine l.domSound ρ x y
          (fun d hd => hρ d (List.mem_cons_of_mem _ hd)) fun p hp => ?_
        have h := hpre (p "a" "b") (by rw [hp]; rfl)
        simpa [Spec.argsEnv, ] using h
      ihave Hty : iprop(TinyML.ValHasType W (b.res.inject (b.f x y))
          (TinyML.Typ.subst σ b.res.typ)) $$ [Hrel1 Hrel2]
      · iapply (l.resL.intro σ W (b.f x y))
        iapply (l.semWellTyped σ W x y hdom)
        isplitl [Hrel1]
        · iexact Hrel1
        · iexact Hrel2
      simp only [Binary.toIntrinsic, Intrinsic.toWp_two_of_arity]
      iexists x
      iexists y
      isplitr [Hpost Hty]
      · ipureintro; exact ⟨rfl, rfl, hdom⟩
      · have hassert : (Formula.eq .value (.var .value "ret")
            (b.opTerm (.var .value "a") (.var .value "b"))).eval
            ((Spec.argsEnv ρ b.toIntrinsic.specArgs
              [b.arg₁.inject x, b.arg₂.inject y]).updateConst
              .value "ret" (b.res.inject (b.f x y))) :=
          (l.opEval ρ x y hρ).symm
        refine (sep_mono_left
          (assert_ret_apply W _ "ret" _ _ (b.res.inject (b.f x y)) hassert)).trans ?_
        iintro ⟨Hwand, Hty⟩
        iapply Hwand
        iexact Hty
  axiomWf := by
    intro Δ hsub hwf a hφ
    simp only [Binary.toIntrinsic, Binary.axioms] at hφ
    have hw := l.encWf
    cases hb : b.enc with
    | direct e => rw [hb] at hφ; cases hφ
    | symbol φ =>
      rw [hb] at hφ hw
      simp only [Encoding.wf] at hw
      simp only [List.mem_cons, Option.mem_toList, Option.map_eq_some_iff] at hφ
      rcases hφ with rfl | ⟨ψ, hψ, rfl⟩
      · exact Formula.wfIn_mono _ hw hsub hwf
      · exact Formula.wfIn_mono _ (l.typeWf ψ hψ) hsub hwf
  proof := by
    intro ρ hdeps a hφ
    simp only [Binary.toIntrinsic, Binary.axioms] at hφ
    have hev := l.encEval
    cases henc : b.enc with
    | direct e => rw [henc] at hφ; cases hφ
    | symbol φ =>
      rw [henc] at hφ
      simp only [Binary.encEval, henc] at hev
      have hresp : ρ.respects (some b.sym) := by
        simpa [Intrinsic.folSym, Binary.toIntrinsic, Binary.fol, henc]
          using hdeps b.toIntrinsic (by simp)
      simp only [List.mem_cons, Option.mem_toList, Option.map_eq_some_iff,
        Binary.typeAxiom, henc] at hφ
      rcases hφ with rfl | ⟨ψ, ⟨p, hp, rfl⟩, rfl⟩
      · exact hev ρ (fun d hd => hdeps d (List.mem_cons_of_mem _ hd)) hresp
      · simp only [Formula.all, Formula.eval]
        intro x y
        have hb : ((ρ.updateConst .value "a" x).updateConst .value "b" y).binary
            .value .value .value b.name = fun a c => b.sym.interp (a, c) := by
          rw [Env.updateConst_binary, Env.updateConst_binary]
          simpa [Binary.sym] using hresp
        simp only [Binary.opTerm, Binary.fol, henc, IntrinsicFOL.term, Term.eval,
          BinOp.eval, Env.lookupConst_updateConst_same,
          Env.lookupConst_updateConst_ne (show "a" ≠ "b" by decide), hb, Binary.sym]
        exact l.resL.isOf_inject _ _ p hp
  folWf := by
    intro f hf
    simp only [Binary.toIntrinsic, Option.some.injEq] at hf
    subst hf
    have hw := l.encWf
    simp only [Binary.fol]
    cases hb : b.enc with
    | symbol φ => trivial
    | direct e => rw [hb] at hw; exact hw

/-! ## Builder for pure ternary intrinsics

`Pure.Ternary` bundles the *computational* content of a pure ternary intrinsic:
its name/path, the argument and result embeddings, the carrier function `f`, and
the SMT defining axiom. From this alone the `Intrinsic` and its FOL symbol are
built (`toIntrinsic`). The proof obligations live in `Pure.Ternary.Lawful`. -/

/-- The computational data of a pure ternary intrinsic. `dom` is the carrier-level
    domain guarding `reduce`/`wp`; `pre` is the matching FOL precondition as a
    function of the spec's argument names (the builder applies it at
    `"a"`/`"b"`/`"c"`). For total intrinsics: `dom := fun _ _ _ => True`,
    `pre := none`. -/
structure Ternary where
  name : String
  path : Option (String × List String)
  arg₁ : Embedding
  arg₂ : Embedding
  arg₃ : Embedding
  res  : Embedding
  f    : arg₁.carrier → arg₂.carrier → arg₃.carrier → res.carrier
  dom  : arg₁.carrier → arg₂.carrier → arg₃.carrier → Prop
  pre  : Option (String → String → String → Formula)
  enc  : Encoding .three

/-- The symbol that a `symbol` encoding declares: the standard interpretation
    projects all arguments, applies `f`, and injects the result. -/
def Ternary.sym (b : Ternary) : FOL.Symbol .three where
  name   := b.name
  interp := fun (a, c, d) =>
    b.res.inject (b.f (b.arg₁.project a) (b.arg₂.project c) (b.arg₃.project d))

/-- How the intrinsic reaches the solver. -/
def Ternary.fol (b : Ternary) : IntrinsicFOL .three :=
  match b.enc with
  | .symbol _ => .symbol b.sym
  | .direct e => .direct e

/-- The term that the spec asserts the result equal to. -/
def Ternary.opTerm (b : Ternary) (x y z : Term .value) : Term .value :=
  b.fol.term .three (x, y, z)

/-- The result-typing axiom, generated from `res` when it has a recognizer: the
    op result satisfies the result embedding's `is-of` predicate. A direct
    encoding needs none: its term applies the constructor itself. -/
def Ternary.typeAxiom (b : Ternary) : Option Formula :=
  match b.enc with
  | .direct _ => none
  | .symbol _ => b.res.isOf.map fun p =>
      .all "a" .value <| .all "b" .value <| .forall_ "c" .value
        [.term (b.opTerm (.var .value "a") (.var .value "b") (.var .value "c"))] <|
        .unpred p (b.opTerm (.var .value "a") (.var .value "b") (.var .value "c"))

/-- The axioms that the encoding contributes. A direct encoding contributes
    none. -/
def Ternary.axioms (b : Ternary) : List Axiom :=
  match b.enc with
  | .direct _ => []
  | .symbol φ => ⟨φ, .high⟩ :: (b.typeAxiom.map (⟨·, .high⟩)).toList

/-- The intrinsic built from `b`: a literal `Intrinsic.mk` so the arity-unfolding
    lemmas (`toReduce_three_of_arity`, `toWp_three_of_arity`) keep firing by `rfl`. -/
def Ternary.toIntrinsic (b : Ternary) : Intrinsic where
  arity  := .three
  name   := b.name
  path   := b.path
  reduce := Reduce.pure fun (a, c, d) v =>
    ∃ x y z, a = b.arg₁.inject x ∧ c = b.arg₂.inject y ∧ d = b.arg₃.inject z ∧
      b.dom x y z ∧ v = b.res.inject (b.f x y z)
  wp     := fun (a, c, d) Q =>
    iprop(∃ x y z, ⌜a = b.arg₁.inject x ∧ c = b.arg₂.inject y ∧ d = b.arg₃.inject z ∧
      b.dom x y z⌝ ∗ Q (b.res.inject (b.f x y z)))
  argTys := [b.arg₁.typ, b.arg₂.typ, b.arg₃.typ]
  retTy  := b.res.typ
  spec   :=
    { args  := ["a", "b", "c"]
      ghost := []
      pred  := withPre (b.pre.map (· "a" "b" "c")) <| .ret ⟨"ret",
        .assert (.eq .value (.var .value "ret")
          (b.opTerm (.var .value "a") (.var .value "b") (.var .value "c"))) (.ret ())⟩ }
  folTerm := some b.fol
  axioms := b.axioms

@[simp] theorem Ternary.toWp_eq (b : Ternary) (a c d : Runtime.Val) (Q : Runtime.Val → iProp) :
    b.toIntrinsic.toWp [a, c, d] Q =
      iprop(∃ x y z, ⌜a = b.arg₁.inject x ∧ c = b.arg₂.inject y ∧ d = b.arg₃.inject z ∧
        b.dom x y z⌝ ∗ Q (b.res.inject (b.f x y z))) := rfl

@[simp] theorem Ternary.toReduce_eq (b : Ternary) (a c d v : Runtime.Val) (μ μ' : TinyML.Heap) :
    b.toIntrinsic.toReduce [a, c, d] μ v μ' =
      ((∃ x y z, a = b.arg₁.inject x ∧ c = b.arg₂.inject y ∧ d = b.arg₃.inject z ∧
        b.dom x y z ∧ v = b.res.inject (b.f x y z)) ∧ μ' = μ) := rfl

@[simp] theorem Ternary.spec_pred (b : Ternary) :
    b.toIntrinsic.spec.pred = withPre (b.pre.map (· "a" "b" "c"))
      (.ret ⟨"ret",
        .assert (.eq .value (.var .value "ret")
          (b.opTerm (.var .value "a") (.var .value "b") (.var .value "c"))) (.ret ())⟩) := rfl

@[simp] theorem Ternary.argTys_map_subst (b : Ternary) (σ : TinyML.TyVar → TinyML.Typ) :
    b.toIntrinsic.argTys.map (TinyML.Typ.subst σ)
      = [TinyML.Typ.subst σ b.arg₁.typ, TinyML.Typ.subst σ b.arg₂.typ, TinyML.Typ.subst σ b.arg₃.typ] := rfl

@[simp] theorem Ternary.retTy_subst (b : Ternary) (σ : TinyML.TyVar → TinyML.Typ) :
    TinyML.Typ.subst σ b.toIntrinsic.retTy = TinyML.Typ.subst σ b.res.typ := rfl

/-- What the encoding must tell the solver truthfully. A `symbol` encoding must
    satisfy its defining axiom. A `direct` encoding must compute `f`. -/
def Ternary.encEval (b : Ternary) (dependencies : Registry) : Prop :=
  match b.enc with
  | .symbol φ => ∀ ρ : Env, (∀ d ∈ dependencies, ρ.respects d.folSym) →
      ρ.respects (some b.sym) → Formula.eval ρ φ
  | .direct e => ∀ (ρ : Env) (x : b.arg₁.carrier) (y : b.arg₂.carrier)
      (z : b.arg₃.carrier),
      ρ.lookupConst .value "a" = b.arg₁.inject x →
      ρ.lookupConst .value "b" = b.arg₂.inject y →
      ρ.lookupConst .value "c" = b.arg₃.inject z →
      Term.eval ρ (e (.var .value "a", .var .value "b", .var .value "c"))
        = b.res.inject (b.f x y z)

/-- Proof obligations for a pure ternary intrinsic and its additional registry
    dependencies. -/
structure Ternary.Lawful (dependencies : Registry) (b : Ternary) where
  argL₁        : b.arg₁.Lawful
  argL₂        : b.arg₂.Lawful
  argL₃        : b.arg₃.Lawful
  resL         : b.res.Lawful
  domSound     : ∀ (ρ : Env) (x : b.arg₁.carrier) (y : b.arg₂.carrier) (z : b.arg₃.carrier),
                 (∀ d ∈ dependencies, ρ.respects d.folSym) →
                 (∀ p, b.pre = some p →
                   (p "a" "b" "c").eval (((ρ.updateConst .value "a"
                     (b.arg₁.inject x)).updateConst .value "b"
                     (b.arg₂.inject y)).updateConst .value "c" (b.arg₃.inject z))) →
                 b.dom x y z
  semWellTyped : ∀ [MicaGS HasLC.hasLC Sig] (σ : TinyML.TyVar → TinyML.Typ)
                 (W : TinyML.World) (x : b.arg₁.carrier) (y : b.arg₂.carrier)
                 (z : b.arg₃.carrier), b.dom x y z →
                 b.arg₁.typePred σ W x ∗ b.arg₂.typePred σ W y ∗ b.arg₃.typePred σ W z ⊢
                   b.res.typePred σ W (b.f x y z)
  specBaseWf   : PredTrans.wfIn
                 ((Intrinsic.sigOf (b.toIntrinsic :: dependencies)).declVars
                   (Spec.argVars b.toIntrinsic.specArgs)) b.toIntrinsic.spec.pred
  encWf        : b.enc.wf (Intrinsic.sigOf (b.toIntrinsic :: dependencies))
  typeWf       : ∀ φ, b.typeAxiom = some φ →
                 φ.wfIn (Intrinsic.sigOf (b.toIntrinsic :: dependencies))
  encEval      : b.encEval dependencies

/-- Whichever encoding is in use, the term the spec asserts evaluates, in the
    spec's own environment, to what `f` computes. -/
theorem Ternary.Lawful.opEval {dependencies : Registry} {b : Ternary}
    (l : b.Lawful dependencies) (ρ : Env) (x : b.arg₁.carrier) (y : b.arg₂.carrier)
    (z : b.arg₃.carrier)
    (hρ : ∀ d ∈ b.toIntrinsic :: dependencies, ρ.respects d.folSym) :
    Term.eval ((Spec.argsEnv ρ b.toIntrinsic.specArgs
        [b.arg₁.inject x, b.arg₂.inject y, b.arg₃.inject z]).updateConst
        .value "ret" (b.res.inject (b.f x y z)))
        (b.opTerm (.var .value "a") (.var .value "b") (.var .value "c"))
      = b.res.inject (b.f x y z) := by
  have hev := l.encEval
  simp only [Ternary.opTerm, Ternary.fol]
  cases hb : b.enc with
  | direct e =>
    simp only [Ternary.encEval, hb] at hev
    exact hev _ x y z rfl rfl rfl
  | symbol φ =>
    have hresp : ρ.respects (some b.sym) := by
      simpa [Intrinsic.folSym, Ternary.toIntrinsic, Ternary.fol, hb]
        using hρ b.toIntrinsic (by simp)
    have hter : (Spec.argsEnv ρ b.toIntrinsic.specArgs
        [b.arg₁.inject x, b.arg₂.inject y, b.arg₃.inject z]).ternary
        .value .value .value .value b.name
        = fun a c d => b.sym.interp (a, c, d) := by
      simpa [Env.respects, Ternary.sym] using
        respects_argsEnv_three b.toIntrinsic.specArgs
          [b.arg₁.inject x, b.arg₂.inject y, b.arg₃.inject z] hresp
    show (Spec.argsEnv ρ b.toIntrinsic.specArgs
      [b.arg₁.inject x, b.arg₂.inject y, b.arg₃.inject z]).ternary
      .value .value .value .value b.name
      (b.arg₁.inject x) (b.arg₂.inject y) (b.arg₃.inject z)
      = b.res.inject (b.f x y z)
    simp [hter, Ternary.sym, l.argL₁.project_inject, l.argL₂.project_inject,
      l.argL₃.project_inject]

/-- The whole `IntrinsicSound` instance for a pure ternary intrinsic. -/
@[reducible] def Ternary.Lawful.sound {dependencies : Registry} {b : Ternary}
    (l : b.Lawful dependencies) :
    IntrinsicSound (b.toIntrinsic :: dependencies) b.toIntrinsic where
  argLen := rfl
  specWf := fun _ hsub hwf => specWf_of_base l.specBaseWf hsub hwf
  wp_sound := by
    intro _ ctx hctx vs Φ
    match vs with
    | [] => exact false_elim
    | [_] => exact false_elim
    | [_, _] => exact false_elim
    | _ :: _ :: _ :: _ :: _ => exact false_elim
    | [a, c, d] =>
      have hred : ∀ x y z, b.dom x y z → ∀ μ v μ',
          ctx b.toIntrinsic.name [b.arg₁.inject x, b.arg₂.inject y, b.arg₃.inject z] μ v μ'
            ↔ v = b.res.inject (b.f x y z) ∧ μ' = μ := by
        intro x y z hdom μ v μ'
        rw [hctx]
        simp only [Ternary.toIntrinsic, Intrinsic.toReduce_three_of_arity, Reduce.pure]
        constructor
        · rintro ⟨⟨x', y', z', hx, hy, hz, _, hv⟩, hμ⟩
          have hxx : x = x' := by
            have := congrArg b.arg₁.project hx
            rwa [l.argL₁.project_inject, l.argL₁.project_inject] at this
          have hyy : y = y' := by
            have := congrArg b.arg₂.project hy
            rwa [l.argL₂.project_inject, l.argL₂.project_inject] at this
          have hzz : z = z' := by
            have := congrArg b.arg₃.project hz
            rwa [l.argL₃.project_inject, l.argL₃.project_inject] at this
          subst hxx; subst hyy; subst hzz
          exact ⟨hv, hμ⟩
        · rintro ⟨hv, hμ⟩
          exact ⟨⟨x, y, z, rfl, rfl, rfl, hdom, hv⟩, hμ⟩
      show iprop(∃ x y z, ⌜a = b.arg₁.inject x ∧ c = b.arg₂.inject y ∧ d = b.arg₃.inject z ∧
        b.dom x y z⌝ ∗ Φ (b.res.inject (b.f x y z))) ⊢ _
      istart
      iintro ⟨%x, %y, %z, %habc, HΦ⟩
      obtain ⟨rfl, rfl, rfl, hdom⟩ := habc
      iapply (wp.prim_pure (hred x y z hdom) ⟨_, rfl⟩)
      iintro %v %hv
      subst hv
      iexact HΦ
  bridge := by
    intro _ σ W vs ρ Φ hρ
    simp only [Ternary.argTys_map_subst, Ternary.retTy_subst, Ternary.spec_pred]
    show TinyML.ValsHaveTypes W vs
      [TinyML.Typ.subst σ b.arg₁.typ, TinyML.Typ.subst σ b.arg₂.typ, TinyML.Typ.subst σ b.arg₃.typ] ∗ _ ⊢ _
    match vs with
    | [] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [_] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [_, _] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | _ :: _ :: _ :: _ :: _ =>
        exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [v1, v2, v3] =>
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons W v1 [v2, v3] _ _).1 $$ Hvs
      icases Hcons with ⟨Hv1, Hvs2⟩
      ihave Hcons2 := (TinyML.ValsHaveTypes.cons W v2 [v3] _ _).1 $$ Hvs2
      icases Hcons2 with ⟨Hv2, Hvs3⟩
      ihave Hcons3 := (TinyML.ValsHaveTypes.cons W v3 [] _ _).1 $$ Hvs3
      icases Hcons3 with ⟨Hv3, _⟩
      ihave Hv1eq := (l.argL₁.member σ W v1).1 $$ Hv1
      icases Hv1eq with ⟨%x, %hw1, Hrel1⟩
      obtain rfl := hw1
      ihave Hv2eq := (l.argL₂.member σ W v2).1 $$ Hv2
      icases Hv2eq with ⟨%y, %hw2, Hrel2⟩
      obtain rfl := hw2
      ihave Hv3eq := (l.argL₃.member σ W v3).1 $$ Hv3
      icases Hv3eq with ⟨%z, %hw3, Hrel3⟩
      obtain rfl := hw3
      ihave Hsplit := withPre_apply W _ _ _ _ $$ Hpred
      icases Hsplit with ⟨%hpre, Hpost⟩
      have hdom : b.dom x y z := by
        refine l.domSound ρ x y z
          (fun d hd => hρ d (List.mem_cons_of_mem _ hd)) fun p hp => ?_
        have h := hpre (p "a" "b" "c") (by rw [hp]; rfl)
        simpa [Spec.argsEnv, ] using h
      ihave Hty : iprop(TinyML.ValHasType W (b.res.inject (b.f x y z))
          (TinyML.Typ.subst σ b.res.typ)) $$ [Hrel1 Hrel2 Hrel3]
      · iapply (l.resL.intro σ W (b.f x y z))
        iapply (l.semWellTyped σ W x y z hdom)
        isplitl [Hrel1]
        · iexact Hrel1
        · isplitl [Hrel2]
          · iexact Hrel2
          · iexact Hrel3
      simp only [Ternary.toIntrinsic, Intrinsic.toWp_three_of_arity]
      iexists x
      iexists y
      iexists z
      isplitr [Hpost Hty]
      · ipureintro; exact ⟨rfl, rfl, rfl, hdom⟩
      · have hassert : (Formula.eq .value (.var .value "ret")
            (b.opTerm (.var .value "a") (.var .value "b") (.var .value "c"))).eval
            ((Spec.argsEnv ρ b.toIntrinsic.specArgs
              [b.arg₁.inject x, b.arg₂.inject y, b.arg₃.inject z]).updateConst
              .value "ret" (b.res.inject (b.f x y z))) :=
          (l.opEval ρ x y z hρ).symm
        refine (sep_mono_left
          (assert_ret_apply W _ "ret" _ _ (b.res.inject (b.f x y z)) hassert)).trans ?_
        iintro ⟨Hwand, Hty⟩
        iapply Hwand
        iexact Hty
  axiomWf := by
    intro Δ hsub hwf a hφ
    simp only [Ternary.toIntrinsic, Ternary.axioms] at hφ
    have hw := l.encWf
    cases henc : b.enc with
    | direct e => rw [henc] at hφ; cases hφ
    | symbol φ =>
      rw [henc] at hφ hw
      simp only [Encoding.wf] at hw
      simp only [List.mem_cons, Option.mem_toList, Option.map_eq_some_iff] at hφ
      rcases hφ with rfl | ⟨ψ, hψ, rfl⟩
      · exact Formula.wfIn_mono _ hw hsub hwf
      · exact Formula.wfIn_mono _ (l.typeWf ψ hψ) hsub hwf
  proof := by
    intro ρ hdeps a hφ
    simp only [Ternary.toIntrinsic, Ternary.axioms] at hφ
    have hev := l.encEval
    cases henc : b.enc with
    | direct e => rw [henc] at hφ; cases hφ
    | symbol φ =>
      rw [henc] at hφ
      simp only [Ternary.encEval, henc] at hev
      have hresp : ρ.respects (some b.sym) := by
        simpa [Intrinsic.folSym, Ternary.toIntrinsic, Ternary.fol, henc]
          using hdeps b.toIntrinsic (by simp)
      simp only [List.mem_cons, Option.mem_toList, Option.map_eq_some_iff,
        Ternary.typeAxiom, henc] at hφ
      rcases hφ with rfl | ⟨ψ, ⟨p, hp, rfl⟩, rfl⟩
      · exact hev ρ (fun d hd => hdeps d (List.mem_cons_of_mem _ hd)) hresp
      · simp only [Formula.all, Formula.eval]
        intro x y z
        have ht : (((ρ.updateConst .value "a" x).updateConst .value "b" y).updateConst
              .value "c" z).ternary .value .value .value .value b.name =
            fun a c d => b.sym.interp (a, c, d) := by
          rw [Env.updateConst_ternary, Env.updateConst_ternary, Env.updateConst_ternary]
          simpa [Ternary.sym] using hresp
        simp only [Ternary.opTerm, Ternary.fol, henc, IntrinsicFOL.term, Term.eval,
          TerOp.eval, Env.lookupConst_updateConst_same,
          Env.lookupConst_updateConst_ne (show "a" ≠ "b" by decide),
          Env.lookupConst_updateConst_ne (show "a" ≠ "c" by decide),
          Env.lookupConst_updateConst_ne (show "b" ≠ "c" by decide),
          ht, Ternary.sym]
        exact l.resL.isOf_inject _ _ p hp
  folWf := by
    intro f hf
    simp only [Ternary.toIntrinsic, Option.some.injEq] at hf
    subst hf
    have hw := l.encWf
    simp only [Ternary.fol]
    cases hb : b.enc with
    | symbol φ => trivial
    | direct e => rw [hb] at hw; exact hw

end Pure

syntax (name := intrinsicDefEval) "intrinsic_def_eval" "["
  ((Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),*,?) "]" : tactic

macro_rules
  | `(tactic| intrinsic_def_eval [$xs,*]) => `(tactic|
  ((intro ρ; intro _; intro hρ);
   simp_all [Env.respects, Formula.eval, Formula.all, Term.eval, Env.lookupConst,
    Env.updateConst, Env.updateConst_unary, Env.updateConst_binary, Env.updateConst_ternary,
    Env.lookupConst_updateConst_same, Pure.Zero.sym, Pure.Unary.sym, Pure.Binary.sym,
    Pure.Ternary.sym,
    Embedding.int, Embedding.bool, Embedding.char, Embedding.str, Embedding.float,
    Embedding.poly, Embedding.vec,
     Const.denote, valInt, valBool, valChar, valStr, valFloat, valVec, $xs,*]))

end Intrinsics
end Stdlib
