-- SUMMARY: Embeddings and the pure-intrinsic builders (`Pure.Zero`/`Pure.Unary`/`Pure.Binary`/`Pure.Ternary`) that emit an intrinsic and its soundness instance.
import Mica.Verifier.Intrinsic
import Mica.TinyML.Printer

open Iris Iris.BI

namespace Stdlib

open Verifier

namespace Intrinsics

/-! # Combinators for intrinsic soundness -/

/-! ## Shared helpers -/

/-- Apply a `.ret (s, .assert φ ...)` spec at a value, discharging the asserted
    `φ` as a pure side condition. -/
theorem assert_ret_apply [MicaGS HasLC.hasLC Sig] (Θ : TinyML.TypeEnv) (Φ : Runtime.Val → iProp)
    (s : String) (ρ : VerifM.Env) (φ : Formula) (v : Runtime.Val)
    (hφ : φ.eval (ρ.updateConst .value s v).env) :
    PredTrans.apply Θ Φ (.ret (s, .assert φ (.ret ()))) ρ ⊢ Φ v := by
  simp only [PredTrans.apply, Assertion.pre, Assertion.post]
  refine (forall_elim v).trans ?_
  iintro Hw
  iapply Hw
  ipureintro
  exact hφ

/-- Wrap an optional precondition around a spec predicate: `some φ` prepends an
    `.assert φ`; `none` leaves the predicate untouched, keeping the emitted spec
    of precondition-free intrinsics unchanged. -/
def withPre : Option Formula → PredTrans → PredTrans
  | none,   post => post
  | some φ, post => .assert φ post

/-- Eliminate `withPre`: applying the wrapped predicate yields the precondition
    as a pure fact (vacuous for `none`) alongside the unwrapped application. -/
theorem withPre_apply [MicaGS HasLC.hasLC Sig] (Θ : TinyML.TypeEnv) (Φ : Runtime.Val → iProp)
    (pre : Option Formula) (post : PredTrans) (ρ : VerifM.Env) :
    PredTrans.apply Θ Φ (withPre pre post) ρ ⊢
      iprop(⌜∀ φ, pre = some φ → φ.eval ρ.env⌝ ∗ PredTrans.apply Θ Φ post ρ) := by
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
theorem valsHaveTypes_off_shape [MicaGS HasLC.hasLC Sig] {Θ : TinyML.TypeEnv}
    {vs : List Runtime.Val} {tys : List TinyML.Typ} (P : iProp)
    (hlen : vs.length ≠ tys.length) :
    TinyML.ValsHaveTypes Θ vs tys ⊢ P := by
  refine TinyML.ValsHaveTypes.length_eq.trans ?_
  iintro %h
  simp at h; omega

/-- Respect for an arity-one symbol survives the argument-binding fold; each
    step rebinds a `value` constant, which never touches the unary table. -/
private theorem respects_argsEnv_one {s : FOL.Symbol .one} :
    ∀ (args : List (String × TinyML.Typ)) (vs : List Runtime.Val) {ρ : VerifM.Env},
      ρ.env.respects (some s) → (Spec.argsEnv ρ args vs).env.respects (some s)
  | [], _, _, h => h
  | _ :: _, [], _, h => h
  | (_, _) :: rest, _ :: vs, ρ, h => by
      simp only [Spec.argsEnv]
      refine respects_argsEnv_one rest vs ?_
      rw [VerifM.Env.updateConst_env]
      simpa only [Env.respects, Env.updateConst_unary] using h

/-- Respect for an arity-two symbol survives the argument-binding fold; each
    step rebinds a `value` constant, which never touches the binary table. -/
private theorem respects_argsEnv_two {s : FOL.Symbol .two} :
    ∀ (args : List (String × TinyML.Typ)) (vs : List Runtime.Val) {ρ : VerifM.Env},
      ρ.env.respects (some s) → (Spec.argsEnv ρ args vs).env.respects (some s)
  | [], _, _, h => h
  | _ :: _, [], _, h => h
  | (_, _) :: rest, _ :: vs, ρ, h => by
      simp only [Spec.argsEnv]
      refine respects_argsEnv_two rest vs ?_
      rw [VerifM.Env.updateConst_env]
      simpa only [Env.respects, Env.updateConst_binary] using h

/-- Respect for an arity-three symbol survives the argument-binding fold; each
    step rebinds a `value` constant, which never touches the ternary table. -/
private theorem respects_argsEnv_three {s : FOL.Symbol .three} :
    ∀ (args : List (String × TinyML.Typ)) (vs : List Runtime.Val) {ρ : VerifM.Env},
      ρ.env.respects (some s) → (Spec.argsEnv ρ args vs).env.respects (some s)
  | [], _, _, h => h
  | _ :: _, [], _, h => h
  | (_, _) :: rest, _ :: vs, ρ, h => by
      simp only [Spec.argsEnv]
      refine respects_argsEnv_three rest vs ?_
      rw [VerifM.Env.updateConst_env]
      simpa only [Env.respects, Env.updateConst_ternary] using h

/-! ## `specWf`: predicate-transformer well-formedness -/

/-- The `specWf` obligation from a base well-formedness fact in the singleton
    signature: monotonicity carries it to any signature declaring the symbol. -/
theorem specWf_of_base {i : Intrinsic}
    (hbase : PredTrans.wfIn
      ((Intrinsic.sigOf [i]).declVars (Spec.argVars i.specArgs)) i.spec.pred)
    {Δ : Signature} (hsub : (Signature.empty.extendWithSym i.folSym).Subset Δ) (hwf : Δ.wf) :
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
  typ      : TinyML.Typ
  carrier  : Type
  inject   : carrier → Runtime.Val
  project  : Runtime.Val → carrier
  typePred : ∀ [MicaGS.{0} HasLC.hasLC Sig],
              (TinyML.TyVar → TinyML.Typ) → TinyML.TypeEnv → carrier → iProp
  isOf     : Option (UnPred .value)

/-- Integer projection of a runtime value, matching FOL's `toInt`. -/
def valInt : Runtime.Val → Int
  | .int n => n
  | _      => 0

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
    fun σ Θ w => TinyML.ValHasType Θ w (σ v), none⟩

/-- An arbitrary type scheme represented by the runtime value itself. -/
def Embedding.logical (typ : TinyML.Typ) : Embedding :=
  ⟨typ, Runtime.Val, id, id,
    fun σ Θ w => TinyML.ValHasType Θ w (typ.subst σ), none⟩

/-- The empty type: no closed values inhabit it. Trivial `Unit` carrier with a
    `False` type predicate, so only an intrinsic with an unsatisfiable domain
    can use it as a result. No `is-of` recognizer, so no type axiom. -/
def Embedding.empty : Embedding :=
  ⟨.empty, Unit, fun _ => .unit, fun _ => (), fun _ _ _ => iprop(False), none⟩

/-- Vectors of an arbitrary element scheme: element lists, with the big-sep of
    instantiated element typings as the type predicate. -/
def Embedding.vec (elem : TinyML.Typ) : Embedding :=
  ⟨.vec elem, List Runtime.Val, .vec, valVec,
    fun σ Θ l => iprop([∗list] w ∈ l, TinyML.ValHasType Θ w (elem.subst σ)),
    some .isVec⟩

/-- Coherence laws for an `Embedding`. The `member`/`intro` laws are stated at
    every instantiation `e.typ.subst σ` of the embedding's type. -/
structure Embedding.Lawful (e : Embedding) where
  project_inject : ∀ x, e.project (e.inject x) = x
  isOf_wf        : ∀ Δ p, e.isOf = some p → p.wfIn Δ
  isOf_inject    : ∀ (ρ : Env) (x : e.carrier) p, e.isOf = some p →
                     UnPred.eval ρ p (e.inject x)
  member         : ∀ [MicaGS HasLC.hasLC Sig] (σ : TinyML.TyVar → TinyML.Typ)
                     (Θ : TinyML.TypeEnv) (w : Runtime.Val),
                     TinyML.ValHasType Θ w (e.typ.subst σ) ⊣⊢
                       iprop(∃ x, ⌜w = e.inject x⌝ ∗ e.typePred σ Θ x)
  intro          : ∀ [MicaGS HasLC.hasLC Sig] (σ : TinyML.TyVar → TinyML.Typ)
                     (Θ : TinyML.TypeEnv) (x : e.carrier),
                     e.typePred σ Θ x ⊢ TinyML.ValHasType Θ (e.inject x) (e.typ.subst σ)

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
  member _ Θ w := pure_member (φ := fun x => w = .int x)
    (by simpa [Embedding.int, TinyML.Typ.subst] using TinyML.ValHasType.int Θ w)
  intro _ Θ x := by simpa [Embedding.int, TinyML.Typ.subst] using TinyML.ValHasType.int_intro Θ x

/-- Booleans are a lawful embedding. -/
def Embedding.lawfulBool : Embedding.bool.Lawful where
  project_inject _ := rfl
  isOf_wf _ _ h := by cases h; trivial
  isOf_inject _ _ _ h := by cases h; simp [Embedding.bool]
  member _ Θ w := pure_member (φ := fun x => w = .bool x)
    (by simpa [Embedding.bool, TinyML.Typ.subst] using TinyML.ValHasType.bool Θ w)
  intro _ Θ x := by simpa [Embedding.bool, TinyML.Typ.subst] using TinyML.ValHasType.bool_intro Θ x

/-- Characters are a lawful embedding. -/
def Embedding.lawfulChar : Embedding.char.Lawful where
  project_inject _ := rfl
  isOf_wf _ _ h := by cases h; trivial
  isOf_inject _ _ _ h := by cases h; simp [Embedding.char]
  member _ Θ w := pure_member (φ := fun x => w = .char x)
    (by simpa [Embedding.char, TinyML.Typ.subst] using TinyML.ValHasType.char Θ w)
  intro _ Θ x := by simpa [Embedding.char, TinyML.Typ.subst] using TinyML.ValHasType.char_intro Θ x

/-- Byte strings are a lawful embedding. -/
def Embedding.lawfulStr : Embedding.str.Lawful where
  project_inject _ := rfl
  isOf_wf _ _ h := by cases h; trivial
  isOf_inject _ _ _ h := by cases h; simp [Embedding.str]
  member _ Θ w := pure_member (φ := fun x => w = .str x)
    (by simpa [Embedding.str, TinyML.Typ.subst] using TinyML.ValHasType.string Θ w)
  intro _ Θ x := by simpa [Embedding.str, TinyML.Typ.subst] using TinyML.ValHasType.string_intro Θ x

/-- Floats are a lawful embedding. -/
def Embedding.lawfulFloat : Embedding.float.Lawful where
  project_inject _ := rfl
  isOf_wf _ _ h := by cases h; trivial
  isOf_inject _ _ _ h := by cases h; simp [Embedding.float]
  member _ Θ w := pure_member (φ := fun x => w = .float x)
    (by simpa [Embedding.float, TinyML.Typ.subst] using TinyML.ValHasType.float Θ w)
  intro _ Θ x := by simpa [Embedding.float, TinyML.Typ.subst] using TinyML.ValHasType.float_intro Θ x

/-- Type variables are a lawful embedding: the type predicate is the typing fact itself. -/
def Embedding.lawfulPoly (v : TinyML.TyVar) : (Embedding.poly v).Lawful where
  project_inject _ := rfl
  isOf_wf _ _ h := nomatch h
  isOf_inject _ _ _ h := nomatch h
  member σ Θ w := by
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
  intro σ Θ x := by
    simp only [Embedding.poly, TinyML.Typ.subst]
    exact .rfl

/-- The identity representation of an arbitrary logical type is lawful. -/
def Embedding.lawfulLogical (typ : TinyML.Typ) : (Embedding.logical typ).Lawful where
  project_inject _ := rfl
  isOf_wf _ _ h := nomatch h
  isOf_inject _ _ _ h := nomatch h
  member σ Θ w := by
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

/-- The empty embedding is lawful: `ValHasType` at `.empty` is `False`, so both
    typing directions are vacuous. -/
def Embedding.lawfulEmpty : Embedding.empty.Lawful where
  project_inject _ := rfl
  isOf_wf _ _ h := nomatch h
  isOf_inject _ _ _ h := nomatch h
  member σ Θ w := by
    simp only [Embedding.empty, TinyML.Typ.subst]
    refine (TinyML.ValHasType.empty Θ w).trans ?_
    constructor
    · exact false_elim
    · iintro ⟨%x, %hw, H⟩
      iexact H
  intro σ Θ x := by
    simp only [Embedding.empty, TinyML.Typ.subst]
    exact false_elim

/-- Vectors are a lawful embedding: exactly the `ValHasType.vec` API. -/
def Embedding.lawfulVec (elem : TinyML.Typ) : (Embedding.vec elem).Lawful where
  project_inject _ := rfl
  isOf_wf _ _ h := by cases h; trivial
  isOf_inject _ _ _ h := by cases h; simp [Embedding.vec]
  member σ Θ w := by
    simpa [Embedding.vec, TinyML.Typ.subst] using TinyML.ValHasType.vec Θ w (elem.subst σ)
  intro σ Θ l := by
    simpa [Embedding.vec, TinyML.Typ.subst] using TinyML.ValHasType.vec_intro Θ l (elem.subst σ)

/-! ## Scheme matching -/

/-- Render a list of types for intrinsic-instantiation diagnostics. -/
private def printTypes (tys : List TinyML.Typ) : String :=
  s!"[{", ".intercalate (tys.map TinyML.Typ.print)}]"

/-- Match type variables occurring in a scheme type against an inferred type.
    A variable is fixed by its first occurrence; later occurrences are checked
    by the elaborator against the instantiated scheme, including subtyping. -/
def matchType (inst : List (TinyML.TyVar × TinyML.Typ))
    (pattern actual : TinyML.Typ) : Except String (List (TinyML.TyVar × TinyML.Typ)) :=
  if pattern.closed then .ok inst
  else
    match pattern, actual with
    | .tvar v, t => .ok (if inst.lookup v |>.isSome then inst else (v, t) :: inst)
    | .sum ps, .sum ts => matchTypes inst ps ts
    | .arrow p₁ p₂, .arrow t₁ t₂ => do
        let inst ← matchType inst p₁ t₁
        matchType inst p₂ t₂
    | .ref p, .ref t | .array p, .array t | .vec p, .vec t | .owned p, .owned t =>
        matchType inst p t
    | .tuple ps, .tuple ts => matchTypes inst ps ts
    -- Constructor syntax is inferred as a sparse structural sum before the
    -- primitive scheme is known. Recover the parameter of a predefined type
    -- from the constructor that is present; an empty constructor carries no
    -- information, so instantiate it at the top value type.
    | .named (.predef .list) [p], .sum [.unit, .empty] =>
        matchType inst p .value
    | .named (.predef .list) [p], .sum [_, .tuple [t, _]] =>
        matchType inst p t
    | .named (.predef .option) [p], .sum [.unit, .empty] =>
        matchType inst p .value
    | .named (.predef .option) [p], .sum [_, t] =>
        matchType inst p t
    | .named P ps, .named T ts =>
        if P = T then matchTypes inst ps ts
        else .error s!"expected {pattern.print}, got {actual.print}"
    | _, _ => .error s!"expected {pattern.print}, got {actual.print}"
where
  matchTypes (inst : List (TinyML.TyVar × TinyML.Typ)) :
      List TinyML.Typ → List TinyML.Typ →
        Except String (List (TinyML.TyVar × TinyML.Typ))
    | [], [] => .ok inst
    | p :: ps, t :: ts => do
        let inst ← matchType inst p t
        matchTypes inst ps ts
    | ps, ts => .error s!"expected type arguments {printTypes ps}, got {printTypes ts}"

/-- Derive a primitive instantiation by structurally matching its argument
    scheme against the inferred argument types. Arity and the instantiated
    domains are rechecked by the elaborator. -/
def schemeTyping (patterns : List TinyML.Typ) :
    TinyML.TypeEnv → List TinyML.Typ →
      Except String (List (TinyML.TyVar × TinyML.Typ)) :=
  fun _ actuals =>
    if patterns.length = actuals.length then
      matchType.matchTypes [] patterns actuals
    else
      .error s!"expected {patterns.length} arguments {printTypes patterns}, got \
        {actuals.length} arguments {printTypes actuals}"

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

/-! ## Builder for pure zero-arity intrinsics

`Pure.Zero` bundles the *computational* content of a pure constant intrinsic:
its name/path, result embedding, carrier value, and SMT defining axiom. From
this alone the `Intrinsic` and its FOL symbol are built (`toIntrinsic`). The
proof obligations live in `Pure.Zero.Lawful`. -/

/-- The computational data of a pure zero-arity intrinsic. -/
structure Zero where
  name     : String
  path     : Option (String × List String)
  res      : Embedding
  f        : res.carrier
  defAxiom : Formula

/-- The intrinsic's uninterpreted constant symbol as a value term. -/
def Zero.opTerm (b : Zero) : Term .value :=
  .const (.uninterpreted b.name .value)

/-- The FOL symbol: the standard interpretation injects the carrier value. -/
def Zero.sym (b : Zero) : FOL.Symbol .zero where
  name   := b.name
  interp := fun () => b.res.inject b.f

/-- The result-typing axiom, generated from `res` when it has a recognizer. -/
def Zero.typeAxiom (b : Zero) : Option Formula :=
  b.res.isOf.map fun p => .unpred p b.opTerm

/-- The intrinsic built from `b`: a literal `Intrinsic.mk`. -/
def Zero.toIntrinsic (b : Zero) : Intrinsic where
  arity  := .zero
  name   := b.name
  path   := b.path
  reduce := Reduce.pure fun () v => v = b.res.inject b.f
  wp     := fun () Q => Q (b.res.inject b.f)
  spec   :=
    { args  := []
      retTy := b.res.typ
      pred  := .ret ("ret",
        .assert (.eq .value (.var .value "ret") b.opTerm) (.ret ())) }
  typing := schemeTyping []
  folSym := some b.sym
  axioms := ⟨b.defAxiom, .low⟩ :: (b.typeAxiom.map (⟨·, .low⟩)).toList

@[simp] theorem Zero.toWp_eq (b : Zero) (Q : Runtime.Val → iProp) :
    b.toIntrinsic.toWp [] Q = Q (b.res.inject b.f) := rfl

@[simp] theorem Zero.toReduce_eq (b : Zero) (v : Runtime.Val) (μ μ' : TinyML.Heap) :
    b.toIntrinsic.toReduce [] μ v μ' = (v = b.res.inject b.f ∧ μ' = μ) := rfl

@[simp] theorem Zero.instantiate_retTy (b : Zero) (σ : TinyML.TyVar → TinyML.Typ) :
    (b.toIntrinsic.spec.instantiate σ).retTy = b.res.typ.subst σ := rfl

/-- Proof obligations for a pure zero-arity intrinsic. The `nameFresh` premise
    keeps the generated constant symbol distinct from the spec's `"ret"`
    binder, since both live in the value-constant namespace. -/
structure Zero.Lawful (b : Zero) where
  resL         : b.res.Lawful
  nameFresh    : b.name ≠ "ret"
  semWellTyped : ∀ [MicaGS HasLC.hasLC Sig] (σ : TinyML.TyVar → TinyML.Typ)
                 (Θ : TinyML.TypeEnv), iprop(emp) ⊢ b.res.typePred σ Θ b.f
  specBaseWf   : PredTrans.wfIn
                 ((Intrinsic.sigOf [b.toIntrinsic]).declVars
                   (Spec.argVars b.toIntrinsic.specArgs)) b.toIntrinsic.spec.pred
  defWf        : b.defAxiom.wfIn (Intrinsic.sigOf [b.toIntrinsic])
  typeWf       : ∀ φ, b.typeAxiom = some φ → φ.wfIn (Intrinsic.sigOf [b.toIntrinsic])
  defEval      : ∀ ρ : Env, ρ.respects (some b.sym) → Formula.eval ρ b.defAxiom

/-- The `IntrinsicSound` instance for a pure zero-arity intrinsic. -/
@[reducible] def Zero.Lawful.sound {b : Zero} (l : b.Lawful) :
    IntrinsicSound [b.toIntrinsic] b.toIntrinsic where
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
    intro _ σ Θ vs ρ Φ hρ
    simp only [Zero.instantiate_retTy, Spec.instantiate_pred]
    show TinyML.ValsHaveTypes Θ vs [] ∗ _ ⊢ _
    match vs with
    | _ :: _ => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [] =>
      simp only [Zero.toIntrinsic, Intrinsic.toWp_zero_of_arity]
      refine (sep_mono_left (TinyML.ValsHaveTypes.nil Θ).1).trans ?_
      refine emp_sep.1.trans ?_
      refine (assert_ret_apply Θ _ "ret" _ _ (b.res.inject b.f) ?_).trans ?_
      · have hconst : (ρ.updateConst .value "ret" (b.res.inject b.f)).env.lookupConst
            .value b.name = b.res.inject b.f := by
          rw [VerifM.Env.updateConst_env]
          rw [Env.lookupConst_updateConst_ne l.nameFresh]
          simpa [Env.respects, Zero.sym] using hρ
        simpa [Zero.opTerm, Term.eval, Const.denote] using hconst.symm
      · iintro Hwand
        iapply Hwand
        exact (l.semWellTyped σ Θ).trans (l.resL.intro σ Θ b.f)
  axiomWf := by
    intro Δ hsub hwf a hφ
    simp only [Zero.toIntrinsic, List.mem_cons, Option.mem_toList,
      Option.map_eq_some_iff] at hφ
    rcases hφ with rfl | ⟨φ, hφ, rfl⟩
    · exact Formula.wfIn_mono _ l.defWf hsub hwf
    · exact Formula.wfIn_mono _ (l.typeWf φ hφ) hsub hwf
  proof := by
    intro ρ hdeps a hφ
    simp only [Zero.toIntrinsic, List.mem_cons, Option.mem_toList,
      Option.map_eq_some_iff, Zero.typeAxiom] at hφ
    have hresp : ρ.respects (some b.sym) := by
      have h := hdeps b.toIntrinsic (by simp)
      simpa [Zero.toIntrinsic] using h
    rcases hφ with rfl | ⟨φ, ⟨p, hp, rfl⟩, rfl⟩
    · exact l.defEval ρ hresp
    · simp only [Formula.eval, Zero.opTerm, Term.eval, Const.denote]
      have hconst : ρ.consts .value b.name = b.res.inject b.f := by
        simpa [Env.respects, Env.lookupConst, Zero.sym] using hresp
      rw [hconst]
      exact l.resL.isOf_inject _ _ p hp

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
  name     : String
  path     : Option (String × List String)
  arg      : Embedding
  res      : Embedding
  f        : arg.carrier → res.carrier
  dom      : arg.carrier → Prop
  pre      : Option (String → Formula)
  defAxiom : Formula

/-- The intrinsic's uninterpreted unary symbol applied to a value term. -/
def Unary.opTerm (b : Unary) (x : Term .value) : Term .value :=
  .unop (.uninterpreted b.name .value .value) x

/-- The FOL symbol: the standard interpretation projects, applies `f`, injects. -/
def Unary.sym (b : Unary) : FOL.Symbol .one where
  name   := b.name
  interp := fun a => b.res.inject (b.f (b.arg.project a))

/-- The result-typing axiom, generated from `res` when it has a recognizer. -/
def Unary.typeAxiom (b : Unary) : Option Formula :=
  b.res.isOf.map fun p =>
    .forall_ "a" .value [.term (b.opTerm (.var .value "a"))] <|
      .unpred p (b.opTerm (.var .value "a"))

/-- The intrinsic built from `b`: a literal `Intrinsic.mk`. -/
def Unary.toIntrinsic (b : Unary) : Intrinsic where
  arity  := .one
  name   := b.name
  path   := b.path
  reduce := Reduce.pure fun a v =>
    ∃ x, a = b.arg.inject x ∧ b.dom x ∧ v = b.res.inject (b.f x)
  wp     := fun a Q => iprop(∃ x, ⌜a = b.arg.inject x ∧ b.dom x⌝ ∗ Q (b.res.inject (b.f x)))
  spec   :=
    { args  := [("a", b.arg.typ)]
      retTy := b.res.typ
      pred  := withPre (b.pre.map (· "a")) <| .ret ("ret",
        .assert (.eq .value (.var .value "ret")
          (b.opTerm (.var .value "a"))) (.ret ())) }
  typing := schemeTyping [b.arg.typ]
  folSym := some b.sym
  axioms := ⟨b.defAxiom, .high⟩ :: (b.typeAxiom.map (⟨·, .high⟩)).toList

@[simp] theorem Unary.toWp_eq (b : Unary) (a : Runtime.Val) (Q : Runtime.Val → iProp) :
    b.toIntrinsic.toWp [a] Q
      = iprop(∃ x, ⌜a = b.arg.inject x ∧ b.dom x⌝ ∗ Q (b.res.inject (b.f x))) := rfl

@[simp] theorem Unary.toReduce_eq (b : Unary) (a v : Runtime.Val) (μ μ' : TinyML.Heap) :
    b.toIntrinsic.toReduce [a] μ v μ' =
      ((∃ x, a = b.arg.inject x ∧ b.dom x ∧ v = b.res.inject (b.f x)) ∧ μ' = μ) := rfl

@[simp] theorem Unary.spec_pred (b : Unary) :
    b.toIntrinsic.spec.pred = withPre (b.pre.map (· "a"))
      (.ret ("ret",
        .assert (.eq .value (.var .value "ret")
          (b.opTerm (.var .value "a"))) (.ret ()))) := rfl

@[simp] theorem Unary.instantiate_args (b : Unary) (σ : TinyML.TyVar → TinyML.Typ) :
    (b.toIntrinsic.spec.instantiate σ).args = [("a", b.arg.typ.subst σ)] := rfl

@[simp] theorem Unary.instantiate_retTy (b : Unary) (σ : TinyML.TyVar → TinyML.Typ) :
    (b.toIntrinsic.spec.instantiate σ).retTy = b.res.typ.subst σ := rfl

/-- Proof obligations for a pure unary intrinsic. `domSound` extracts the
    carrier-level domain from the evaluated precondition; when `pre = none` the
    hypothesis is vacuous, so `dom` must hold unconditionally
    (`fun _ _ _ => trivial` for `dom := fun _ => True`). -/
structure Unary.Lawful (b : Unary) where
  argL         : b.arg.Lawful
  resL         : b.res.Lawful
  domSound     : ∀ (ρ : Env) (x : b.arg.carrier),
                 (∀ p, b.pre = some p →
                   (p "a").eval (ρ.updateConst .value "a" (b.arg.inject x))) →
                 b.dom x
  semWellTyped : ∀ [MicaGS HasLC.hasLC Sig] (σ : TinyML.TyVar → TinyML.Typ)
                 (Θ : TinyML.TypeEnv) (x : b.arg.carrier), b.dom x →
                 b.arg.typePred σ Θ x ⊢ b.res.typePred σ Θ (b.f x)
  specBaseWf   : PredTrans.wfIn
                 ((Intrinsic.sigOf [b.toIntrinsic]).declVars
                   (Spec.argVars b.toIntrinsic.specArgs)) b.toIntrinsic.spec.pred
  defWf        : b.defAxiom.wfIn (Intrinsic.sigOf [b.toIntrinsic])
  typeWf       : ∀ φ, b.typeAxiom = some φ → φ.wfIn (Intrinsic.sigOf [b.toIntrinsic])
  defEval      : ∀ ρ : Env, ρ.respects (some b.sym) → Formula.eval ρ b.defAxiom

/-- The `IntrinsicSound` instance for a pure unary intrinsic. -/
@[reducible] def Unary.Lawful.sound {b : Unary} (l : b.Lawful) :
    IntrinsicSound [b.toIntrinsic] b.toIntrinsic where
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
    intro _ σ Θ vs ρ Φ hρ
    simp only [Unary.instantiate_args, Unary.instantiate_retTy,
      Spec.instantiate_pred, Unary.spec_pred, List.map_cons, List.map_nil]
    match vs with
    | [] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | _ :: _ :: _ =>
        exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [v] =>
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ v [] _ _).1 $$ Hvs
      icases Hcons with ⟨Hv, _⟩
      ihave Hveq := (l.argL.member σ Θ v).1 $$ Hv
      icases Hveq with ⟨%x, %hw, Hrel⟩
      obtain rfl := hw
      ihave Hsplit := withPre_apply Θ _ _ _ _ $$ Hpred
      icases Hsplit with ⟨%hpre, Hpost⟩
      have hdom : b.dom x := by
        refine l.domSound ρ.env x fun p hp => ?_
        have h := hpre (p "a") (by rw [hp]; rfl)
        simpa [Spec.argsEnv, VerifM.Env.updateConst_env] using h
      ihave Hty : iprop(TinyML.ValHasType Θ (b.res.inject (b.f x)) (b.res.typ.subst σ)) $$ [Hrel]
      · iapply (l.resL.intro σ Θ (b.f x))
        iapply (l.semWellTyped σ Θ x hdom)
        iexact Hrel
      simp only [Unary.toIntrinsic, Intrinsic.toWp_one_of_arity]
      iexists x
      isplitr [Hpost Hty]
      · ipureintro; exact ⟨rfl, hdom⟩
      · have hassert : (Formula.eq .value (.var .value "ret")
            (b.opTerm (.var .value "a"))).eval
            ((Spec.argsEnv ρ b.toIntrinsic.specArgs [b.arg.inject x]).updateConst
              .value "ret" (b.res.inject (b.f x))).env := by
          have hargs := respects_argsEnv_one b.toIntrinsic.specArgs [b.arg.inject x] hρ
          have hun : (Spec.argsEnv ρ b.toIntrinsic.specArgs [b.arg.inject x]).env.unary
              .value .value b.name = b.sym.interp := by
            simpa [Env.respects, Unary.sym] using hargs
          show b.res.inject (b.f x) =
            (Spec.argsEnv ρ b.toIntrinsic.specArgs [b.arg.inject x]).env.unary
              .value .value b.name (b.arg.inject x)
          simp [hun, Unary.sym, l.argL.project_inject]
        refine (sep_mono_left
          (assert_ret_apply Θ _ "ret" _ _ (b.res.inject (b.f x)) hassert)).trans ?_
        iintro ⟨Hwand, Hty⟩
        iapply Hwand
        iexact Hty
  axiomWf := by
    intro Δ hsub hwf a hφ
    simp only [Unary.toIntrinsic, List.mem_cons, Option.mem_toList,
      Option.map_eq_some_iff] at hφ
    rcases hφ with rfl | ⟨φ, hφ, rfl⟩
    · exact Formula.wfIn_mono _ l.defWf hsub hwf
    · exact Formula.wfIn_mono _ (l.typeWf φ hφ) hsub hwf
  proof := by
    intro ρ hdeps a hφ
    simp only [Unary.toIntrinsic, List.mem_cons, Option.mem_toList,
      Option.map_eq_some_iff, Unary.typeAxiom] at hφ
    have hresp : ρ.respects (some b.sym) := by
      have h := hdeps b.toIntrinsic (by simp)
      simpa [Unary.toIntrinsic] using h
    rcases hφ with rfl | ⟨φ, ⟨p, hp, rfl⟩, rfl⟩
    · exact l.defEval ρ hresp
    · simp only [Formula.eval]
      intro x
      have hu : (ρ.updateConst .value "a" x).unary .value .value b.name = b.sym.interp := by
        rw [Env.updateConst_unary]
        simpa [Unary.sym] using hresp
      simp only [Unary.opTerm, Term.eval, UnOp.eval, Env.lookupConst_updateConst_same,
        hu, Unary.sym]
      exact l.resL.isOf_inject _ _ p hp

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
  name     : String
  path     : Option (String × List String)
  arg₁     : Embedding
  arg₂     : Embedding
  res      : Embedding
  f        : arg₁.carrier → arg₂.carrier → res.carrier
  dom      : arg₁.carrier → arg₂.carrier → Prop
  pre      : Option (String → String → Formula)
  defAxiom : Formula

/-- The intrinsic's uninterpreted binary symbol applied to two value terms. -/
def Binary.opTerm (b : Binary) (x y : Term .value) : Term .value :=
  .binop (.uninterpreted b.name .value .value .value) x y

/-- The FOL symbol: the standard interpretation projects both arguments, applies
    `f`, and injects the result. -/
def Binary.sym (b : Binary) : FOL.Symbol .two where
  name   := b.name
  interp := fun (a, c) => b.res.inject (b.f (b.arg₁.project a) (b.arg₂.project c))

/-- The result-typing axiom, generated from `res` when it has a recognizer: the
    op result satisfies the result embedding's `is-of` predicate. -/
def Binary.typeAxiom (b : Binary) : Option Formula :=
  b.res.isOf.map fun p =>
    .all "a" .value <| .forall_ "b" .value
      [.term (b.opTerm (.var .value "a") (.var .value "b"))] <|
      .unpred p (b.opTerm (.var .value "a") (.var .value "b"))

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
  spec   :=
    { args  := [("a", b.arg₁.typ), ("b", b.arg₂.typ)]
      retTy := b.res.typ
      pred  := withPre (b.pre.map (· "a" "b")) <| .ret ("ret",
        .assert (.eq .value (.var .value "ret")
          (b.opTerm (.var .value "a") (.var .value "b"))) (.ret ())) }
  typing := schemeTyping [b.arg₁.typ, b.arg₂.typ]
  folSym := some b.sym
  axioms := ⟨b.defAxiom, .high⟩ :: (b.typeAxiom.map (⟨·, .high⟩)).toList

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
      (.ret ("ret",
        .assert (.eq .value (.var .value "ret")
          (b.opTerm (.var .value "a") (.var .value "b"))) (.ret ()))) := rfl

@[simp] theorem Binary.instantiate_args (b : Binary) (σ : TinyML.TyVar → TinyML.Typ) :
    (b.toIntrinsic.spec.instantiate σ).args
      = [("a", b.arg₁.typ.subst σ), ("b", b.arg₂.typ.subst σ)] := rfl

@[simp] theorem Binary.instantiate_retTy (b : Binary) (σ : TinyML.TyVar → TinyML.Typ) :
    (b.toIntrinsic.spec.instantiate σ).retTy = b.res.typ.subst σ := rfl

/-- Proof obligations for a pure binary intrinsic: lawful embeddings, the three
    well-formedness facts (spec/def-axiom/type-axiom — one-liners at literal
    names), and validity of the defining axiom under the standard
    interpretation. -/
structure Binary.Lawful (b : Binary) where
  argL₁        : b.arg₁.Lawful
  argL₂        : b.arg₂.Lawful
  resL         : b.res.Lawful
  domSound     : ∀ (ρ : Env) (x : b.arg₁.carrier) (y : b.arg₂.carrier),
                 (∀ p, b.pre = some p →
                   (p "a" "b").eval ((ρ.updateConst .value "a" (b.arg₁.inject x)).updateConst
                     .value "b" (b.arg₂.inject y))) →
                 b.dom x y
  semWellTyped : ∀ [MicaGS HasLC.hasLC Sig] (σ : TinyML.TyVar → TinyML.Typ)
                 (Θ : TinyML.TypeEnv) (x : b.arg₁.carrier) (y : b.arg₂.carrier),
                 b.dom x y →
                 b.arg₁.typePred σ Θ x ∗ b.arg₂.typePred σ Θ y ⊢ b.res.typePred σ Θ (b.f x y)
  specBaseWf   : PredTrans.wfIn
                 ((Intrinsic.sigOf [b.toIntrinsic]).declVars
                   (Spec.argVars b.toIntrinsic.specArgs)) b.toIntrinsic.spec.pred
  defWf        : b.defAxiom.wfIn (Intrinsic.sigOf [b.toIntrinsic])
  typeWf       : ∀ φ, b.typeAxiom = some φ → φ.wfIn (Intrinsic.sigOf [b.toIntrinsic])
  defEval      : ∀ ρ : Env, ρ.respects (some b.sym) → Formula.eval ρ b.defAxiom

/-- The whole `IntrinsicSound` instance for a pure binary intrinsic. -/
@[reducible] def Binary.Lawful.sound {b : Binary} (l : b.Lawful) :
    IntrinsicSound [b.toIntrinsic] b.toIntrinsic where
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
    intro _ σ Θ vs ρ Φ hρ
    simp only [Binary.instantiate_args, Binary.instantiate_retTy,
      Spec.instantiate_pred, Binary.spec_pred, List.map_cons, List.map_nil]
    show TinyML.ValsHaveTypes Θ vs [b.arg₁.typ.subst σ, b.arg₂.typ.subst σ] ∗ _ ⊢ _
    match vs with
    | [] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [_] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | _ :: _ :: _ :: _ =>
        exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [v1, v2] =>
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ v1 [v2] _ _).1 $$ Hvs
      icases Hcons with ⟨Hv1, Hvs2⟩
      ihave Hcons2 := (TinyML.ValsHaveTypes.cons Θ v2 [] _ _).1 $$ Hvs2
      icases Hcons2 with ⟨Hv2, _⟩
      ihave Hv1eq := (l.argL₁.member σ Θ v1).1 $$ Hv1
      icases Hv1eq with ⟨%x, %hw1, Hrel1⟩
      obtain rfl := hw1
      ihave Hv2eq := (l.argL₂.member σ Θ v2).1 $$ Hv2
      icases Hv2eq with ⟨%y, %hw2, Hrel2⟩
      obtain rfl := hw2
      ihave Hsplit := withPre_apply Θ _ _ _ _ $$ Hpred
      icases Hsplit with ⟨%hpre, Hpost⟩
      have hdom : b.dom x y := by
        refine l.domSound ρ.env x y fun p hp => ?_
        have h := hpre (p "a" "b") (by rw [hp]; rfl)
        simpa [Spec.argsEnv, VerifM.Env.updateConst_env] using h
      ihave Hty : iprop(TinyML.ValHasType Θ (b.res.inject (b.f x y))
          (b.res.typ.subst σ)) $$ [Hrel1 Hrel2]
      · iapply (l.resL.intro σ Θ (b.f x y))
        iapply (l.semWellTyped σ Θ x y hdom)
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
              .value "ret" (b.res.inject (b.f x y))).env := by
          have hargs := respects_argsEnv_two b.toIntrinsic.specArgs
            [b.arg₁.inject x, b.arg₂.inject y] hρ
          have hbin : (Spec.argsEnv ρ b.toIntrinsic.specArgs
              [b.arg₁.inject x, b.arg₂.inject y]).env.binary .value .value .value b.name
              = fun a c => b.sym.interp (a, c) := by
            simpa [Env.respects, Binary.sym] using hargs
          show b.res.inject (b.f x y) =
            (Spec.argsEnv ρ b.toIntrinsic.specArgs
              [b.arg₁.inject x, b.arg₂.inject y]).env.binary
              .value .value .value b.name (b.arg₁.inject x) (b.arg₂.inject y)
          simp [hbin, Binary.sym, l.argL₁.project_inject, l.argL₂.project_inject]
        refine (sep_mono_left
          (assert_ret_apply Θ _ "ret" _ _ (b.res.inject (b.f x y)) hassert)).trans ?_
        iintro ⟨Hwand, Hty⟩
        iapply Hwand
        iexact Hty
  axiomWf := by
    intro Δ hsub hwf a hφ
    simp only [Binary.toIntrinsic, List.mem_cons, Option.mem_toList,
      Option.map_eq_some_iff] at hφ
    rcases hφ with rfl | ⟨φ, hφ, rfl⟩
    · exact Formula.wfIn_mono _ l.defWf hsub hwf
    · exact Formula.wfIn_mono _ (l.typeWf φ hφ) hsub hwf
  proof := by
    intro ρ hdeps a hφ
    simp only [Binary.toIntrinsic, List.mem_cons, Option.mem_toList,
      Option.map_eq_some_iff, Binary.typeAxiom] at hφ
    have hresp : ρ.respects (some b.sym) := by
      have h := hdeps b.toIntrinsic (by simp)
      simpa [Binary.toIntrinsic] using h
    rcases hφ with rfl | ⟨φ, ⟨p, hp, rfl⟩, rfl⟩
    · exact l.defEval ρ hresp
    · simp only [Formula.all, Formula.eval]
      intro x y
      have hb : ((ρ.updateConst .value "a" x).updateConst .value "b" y).binary
          .value .value .value b.name = fun a c => b.sym.interp (a, c) := by
        rw [Env.updateConst_binary, Env.updateConst_binary]
        simpa [Binary.sym] using hresp
      simp only [Binary.opTerm, Term.eval, BinOp.eval, Env.lookupConst_updateConst_same,
        Env.lookupConst_updateConst_ne (show "a" ≠ "b" by decide), hb, Binary.sym]
      exact l.resL.isOf_inject _ _ p hp

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
  name     : String
  path     : Option (String × List String)
  arg₁     : Embedding
  arg₂     : Embedding
  arg₃     : Embedding
  res      : Embedding
  f        : arg₁.carrier → arg₂.carrier → arg₃.carrier → res.carrier
  dom      : arg₁.carrier → arg₂.carrier → arg₃.carrier → Prop
  pre      : Option (String → String → String → Formula)
  defAxiom : Formula

/-- The intrinsic's uninterpreted ternary symbol applied to three value terms. -/
def Ternary.opTerm (b : Ternary) (x y z : Term .value) : Term .value :=
  .terop (.uninterpreted b.name .value .value .value .value) x y z

/-- The FOL symbol: the standard interpretation projects all arguments, applies
    `f`, and injects the result. -/
def Ternary.sym (b : Ternary) : FOL.Symbol .three where
  name   := b.name
  interp := fun (a, c, d) =>
    b.res.inject (b.f (b.arg₁.project a) (b.arg₂.project c) (b.arg₃.project d))

/-- The result-typing axiom, generated from `res` when it has a recognizer: the
    op result satisfies the result embedding's `is-of` predicate. -/
def Ternary.typeAxiom (b : Ternary) : Option Formula :=
  b.res.isOf.map fun p =>
    .all "a" .value <| .all "b" .value <| .forall_ "c" .value
      [.term (b.opTerm (.var .value "a") (.var .value "b") (.var .value "c"))] <|
      .unpred p (b.opTerm (.var .value "a") (.var .value "b") (.var .value "c"))

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
  spec   :=
    { args  := [("a", b.arg₁.typ), ("b", b.arg₂.typ), ("c", b.arg₃.typ)]
      retTy := b.res.typ
      pred  := withPre (b.pre.map (· "a" "b" "c")) <| .ret ("ret",
        .assert (.eq .value (.var .value "ret")
          (b.opTerm (.var .value "a") (.var .value "b") (.var .value "c"))) (.ret ())) }
  typing := schemeTyping [b.arg₁.typ, b.arg₂.typ, b.arg₃.typ]
  folSym := some b.sym
  axioms := ⟨b.defAxiom, .high⟩ :: (b.typeAxiom.map (⟨·, .high⟩)).toList

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
      (.ret ("ret",
        .assert (.eq .value (.var .value "ret")
          (b.opTerm (.var .value "a") (.var .value "b") (.var .value "c"))) (.ret ()))) := rfl

@[simp] theorem Ternary.instantiate_args (b : Ternary) (σ : TinyML.TyVar → TinyML.Typ) :
    (b.toIntrinsic.spec.instantiate σ).args
      = [("a", b.arg₁.typ.subst σ), ("b", b.arg₂.typ.subst σ), ("c", b.arg₃.typ.subst σ)] := rfl

@[simp] theorem Ternary.instantiate_retTy (b : Ternary) (σ : TinyML.TyVar → TinyML.Typ) :
    (b.toIntrinsic.spec.instantiate σ).retTy = b.res.typ.subst σ := rfl

/-- Proof obligations for a pure ternary intrinsic. -/
structure Ternary.Lawful (b : Ternary) where
  argL₁        : b.arg₁.Lawful
  argL₂        : b.arg₂.Lawful
  argL₃        : b.arg₃.Lawful
  resL         : b.res.Lawful
  domSound     : ∀ (ρ : Env) (x : b.arg₁.carrier) (y : b.arg₂.carrier) (z : b.arg₃.carrier),
                 (∀ p, b.pre = some p →
                   (p "a" "b" "c").eval (((ρ.updateConst .value "a"
                     (b.arg₁.inject x)).updateConst .value "b"
                     (b.arg₂.inject y)).updateConst .value "c" (b.arg₃.inject z))) →
                 b.dom x y z
  semWellTyped : ∀ [MicaGS HasLC.hasLC Sig] (σ : TinyML.TyVar → TinyML.Typ)
                 (Θ : TinyML.TypeEnv) (x : b.arg₁.carrier) (y : b.arg₂.carrier)
                 (z : b.arg₃.carrier), b.dom x y z →
                 b.arg₁.typePred σ Θ x ∗ b.arg₂.typePred σ Θ y ∗ b.arg₃.typePred σ Θ z ⊢
                   b.res.typePred σ Θ (b.f x y z)
  specBaseWf   : PredTrans.wfIn
                 ((Intrinsic.sigOf [b.toIntrinsic]).declVars
                   (Spec.argVars b.toIntrinsic.specArgs)) b.toIntrinsic.spec.pred
  defWf        : b.defAxiom.wfIn (Intrinsic.sigOf [b.toIntrinsic])
  typeWf       : ∀ φ, b.typeAxiom = some φ → φ.wfIn (Intrinsic.sigOf [b.toIntrinsic])
  defEval      : ∀ ρ : Env, ρ.respects (some b.sym) → Formula.eval ρ b.defAxiom

/-- The whole `IntrinsicSound` instance for a pure ternary intrinsic. -/
@[reducible] def Ternary.Lawful.sound {b : Ternary} (l : b.Lawful) :
    IntrinsicSound [b.toIntrinsic] b.toIntrinsic where
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
    intro _ σ Θ vs ρ Φ hρ
    simp only [Ternary.instantiate_args, Ternary.instantiate_retTy,
      Spec.instantiate_pred, Ternary.spec_pred, List.map_cons, List.map_nil]
    show TinyML.ValsHaveTypes Θ vs
      [b.arg₁.typ.subst σ, b.arg₂.typ.subst σ, b.arg₃.typ.subst σ] ∗ _ ⊢ _
    match vs with
    | [] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [_] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [_, _] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | _ :: _ :: _ :: _ :: _ =>
        exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [v1, v2, v3] =>
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ v1 [v2, v3] _ _).1 $$ Hvs
      icases Hcons with ⟨Hv1, Hvs2⟩
      ihave Hcons2 := (TinyML.ValsHaveTypes.cons Θ v2 [v3] _ _).1 $$ Hvs2
      icases Hcons2 with ⟨Hv2, Hvs3⟩
      ihave Hcons3 := (TinyML.ValsHaveTypes.cons Θ v3 [] _ _).1 $$ Hvs3
      icases Hcons3 with ⟨Hv3, _⟩
      ihave Hv1eq := (l.argL₁.member σ Θ v1).1 $$ Hv1
      icases Hv1eq with ⟨%x, %hw1, Hrel1⟩
      obtain rfl := hw1
      ihave Hv2eq := (l.argL₂.member σ Θ v2).1 $$ Hv2
      icases Hv2eq with ⟨%y, %hw2, Hrel2⟩
      obtain rfl := hw2
      ihave Hv3eq := (l.argL₃.member σ Θ v3).1 $$ Hv3
      icases Hv3eq with ⟨%z, %hw3, Hrel3⟩
      obtain rfl := hw3
      ihave Hsplit := withPre_apply Θ _ _ _ _ $$ Hpred
      icases Hsplit with ⟨%hpre, Hpost⟩
      have hdom : b.dom x y z := by
        refine l.domSound ρ.env x y z fun p hp => ?_
        have h := hpre (p "a" "b" "c") (by rw [hp]; rfl)
        simpa [Spec.argsEnv, VerifM.Env.updateConst_env] using h
      ihave Hty : iprop(TinyML.ValHasType Θ (b.res.inject (b.f x y z))
          (b.res.typ.subst σ)) $$ [Hrel1 Hrel2 Hrel3]
      · iapply (l.resL.intro σ Θ (b.f x y z))
        iapply (l.semWellTyped σ Θ x y z hdom)
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
              .value "ret" (b.res.inject (b.f x y z))).env := by
          have hargs := respects_argsEnv_three b.toIntrinsic.specArgs
            [b.arg₁.inject x, b.arg₂.inject y, b.arg₃.inject z] hρ
          have hter : (Spec.argsEnv ρ b.toIntrinsic.specArgs
              [b.arg₁.inject x, b.arg₂.inject y, b.arg₃.inject z]).env.ternary
              .value .value .value .value b.name
              = fun a c d => b.sym.interp (a, c, d) := by
            simpa [Env.respects, Ternary.sym] using hargs
          show b.res.inject (b.f x y z) =
            (Spec.argsEnv ρ b.toIntrinsic.specArgs
              [b.arg₁.inject x, b.arg₂.inject y, b.arg₃.inject z]).env.ternary
              .value .value .value .value b.name
              (b.arg₁.inject x) (b.arg₂.inject y) (b.arg₃.inject z)
          simp [hter, Ternary.sym, l.argL₁.project_inject, l.argL₂.project_inject,
            l.argL₃.project_inject]
        refine (sep_mono_left
          (assert_ret_apply Θ _ "ret" _ _ (b.res.inject (b.f x y z)) hassert)).trans ?_
        iintro ⟨Hwand, Hty⟩
        iapply Hwand
        iexact Hty
  axiomWf := by
    intro Δ hsub hwf a hφ
    simp only [Ternary.toIntrinsic, List.mem_cons, Option.mem_toList,
      Option.map_eq_some_iff] at hφ
    rcases hφ with rfl | ⟨φ, hφ, rfl⟩
    · exact Formula.wfIn_mono _ l.defWf hsub hwf
    · exact Formula.wfIn_mono _ (l.typeWf φ hφ) hsub hwf
  proof := by
    intro ρ hdeps a hφ
    simp only [Ternary.toIntrinsic, List.mem_cons, Option.mem_toList,
      Option.map_eq_some_iff, Ternary.typeAxiom] at hφ
    have hresp : ρ.respects (some b.sym) := by
      have h := hdeps b.toIntrinsic (by simp)
      simpa [Ternary.toIntrinsic] using h
    rcases hφ with rfl | ⟨φ, ⟨p, hp, rfl⟩, rfl⟩
    · exact l.defEval ρ hresp
    · simp only [Formula.all, Formula.eval]
      intro x y z
      have ht : (((ρ.updateConst .value "a" x).updateConst .value "b" y).updateConst
            .value "c" z).ternary .value .value .value .value b.name =
          fun a c d => b.sym.interp (a, c, d) := by
        rw [Env.updateConst_ternary, Env.updateConst_ternary, Env.updateConst_ternary]
        simpa [Ternary.sym] using hresp
      simp only [Ternary.opTerm, Term.eval, TerOp.eval, Env.lookupConst_updateConst_same,
        Env.lookupConst_updateConst_ne (show "a" ≠ "b" by decide),
        Env.lookupConst_updateConst_ne (show "a" ≠ "c" by decide),
        Env.lookupConst_updateConst_ne (show "b" ≠ "c" by decide),
        ht, Ternary.sym]
      exact l.resL.isOf_inject _ _ p hp

end Pure

syntax (name := intrinsicDefEval) "intrinsic_def_eval" "["
  ((Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),*,?) "]" : tactic

macro_rules
  | `(tactic| intrinsic_def_eval [$xs,*]) => `(tactic|
  ((intro ρ; intro hρ);
   simp_all [Env.respects, Formula.eval, Formula.all, Term.eval, Env.lookupConst,
    Env.updateConst, Env.updateConst_unary, Env.updateConst_binary, Env.updateConst_ternary,
    Env.lookupConst_updateConst_same, Pure.Zero.sym, Pure.Unary.sym, Pure.Binary.sym,
    Pure.Ternary.sym,
    Embedding.int, Embedding.bool, Embedding.char, Embedding.str, Embedding.float,
    Embedding.poly, Embedding.vec,
     Const.denote, valInt, valBool, valChar, valStr, valFloat, valVec, $xs,*]))

end Intrinsics
end Stdlib
