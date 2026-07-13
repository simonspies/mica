-- SUMMARY: Byte-string intrinsics (`String.length`, `get`, `sub`, `cat`, `equal`, `starts_with`, `ends_with`) and soundness instances.
import Mica.Stdlib.IntStd

open Iris Iris.BI

namespace Stdlib

open Verifier

namespace Intrinsics

/-! ## FOL symbols -/

/-- FOL symbol for `String.length`. -/
def stringLengthSym : FOL.Symbol .one where
  name   := "string_length"
  interp := fun a => .int (valStr a).length

/-- FOL symbol for `String.cat`. -/
def stringCatSym : FOL.Symbol .two where
  name   := "string_cat"
  interp := fun (a, b) => .str (valStr a ++ valStr b)

/-- FOL symbol for `String.get`. -/
def stringGetSym : FOL.Symbol .two where
  name   := "string_get"
  interp := fun (s, i) => .char ((valStr s)[Int.toNat (valInt i)]?.getD 0)

/-- Total byte-string slice used by the FOL interpretation. The intrinsic
    precondition restricts runtime calls to OCaml's in-bounds case. -/
def stringSubBytes (s : List UInt8) (pos len : Int) : List UInt8 :=
  (s.drop (Int.toNat pos)).take (Int.toNat len)

/-- FOL symbol for `String.sub`. -/
def stringSubSym : FOL.Symbol .three where
  name   := "string_sub"
  interp := fun (s, pos, len) => .str (stringSubBytes (valStr s) (valInt pos) (valInt len))

/-- FOL symbol for `String.equal`. -/
def stringEqualSym : FOL.Symbol .two where
  name   := "string_equal"
  interp := fun (a, b) => .bool (valStr a == valStr b)

/-- FOL symbol for `String.starts_with`. -/
def stringStartsWithSym : FOL.Symbol .two where
  name   := "string_starts_with"
  interp := fun (p, s) => .bool ((valStr p).isPrefixOf (valStr s))

/-- FOL symbol for `String.ends_with`. -/
def stringEndsWithSym : FOL.Symbol .two where
  name   := "string_ends_with"
  interp := fun (q, s) => .bool ((valStr q).isSuffixOf (valStr s))

@[simp] theorem stringLengthSym_name : stringLengthSym.name = "string_length" := rfl
@[simp] theorem stringCatSym_name : stringCatSym.name = "string_cat" := rfl
@[simp] theorem stringGetSym_name : stringGetSym.name = "string_get" := rfl
@[simp] theorem stringSubSym_name : stringSubSym.name = "string_sub" := rfl
@[simp] theorem stringEqualSym_name : stringEqualSym.name = "string_equal" := rfl
@[simp] theorem stringStartsWithSym_name : stringStartsWithSym.name = "string_starts_with" := rfl
@[simp] theorem stringEndsWithSym_name : stringEndsWithSym.name = "string_ends_with" := rfl

/-! ## Defining axioms

Each intrinsic carries two axioms, both quantified over the **value sort**:
a *defining* axiom tying the symbol to Z3's native sequence theory (through the
`toString`/`toInt` projections), and a *typing* axiom asserting the result is
the expected value constructor (`is-of_int`/`is-of_string`/`is-of_bool`).

The typing axiom is what lets a bare value-level equality such as
`String.length s = 2` discharge: without it Z3 only knows the symbol's `toInt`
projection, not that the result *is* an integer value. Only the defining axiom
is written by hand here; the typing axiom is generated uniformly from the result
embedding by `Pure.Binary`/`Pure.Unary`. -/

def stringLengthDefAxiom : Formula :=
  .forall_ "s" .value [.term (unTerm "string_length" (.var .value "s"))] <|
    .eq .int
      (.unop .toInt (unTerm "string_length" (.var .value "s")))
      (.unop .seqLen (.unop .toString (.var .value "s")))

def stringCatDefAxiom : Formula :=
  .all "a" .value <| .forall_ "b" .value
    [.term (binTerm "string_cat" (.var .value "a") (.var .value "b"))] <|
    .eq .string
      (.unop .toString (binTerm "string_cat" (.var .value "a") (.var .value "b")))
      (.binop .seqConcat (.unop .toString (.var .value "a")) (.unop .toString (.var .value "b")))

def stringGetPre : Formula :=
  let i := .unop .toInt (.var .value "i")
  let len := .unop .seqLen (.unop .toString (.var .value "s"))
  .and
    (.binpred .le (.const (.i 0)) i)
    (.binpred .lt i len)

/-- The value-level FOL term for `String.get s i`. -/
def stringGetTerm (s i : Term .value) : Term .value :=
  binTerm "string_get" s i

/-- Total byte lookup used by the FOL interpretation. The intrinsic precondition
    restricts runtime calls to OCaml's in-bounds case. -/
def stringGetByte (s : List UInt8) (i : Int) : UInt8 :=
  s[Int.toNat i]?.getD 0

def stringGetDefAxiom : Formula :=
  .all "s" .value <| .forall_ "i" .value
    [.term (stringGetTerm (.var .value "s") (.var .value "i"))] <|
    .implies stringGetPre <|
      .eq .char
        (.unop .toChar (stringGetTerm (.var .value "s") (.var .value "i")))
        (.binop .seqNth (.unop .toString (.var .value "s")) (.unop .toInt (.var .value "i")))

def stringGetTypeAxiom : Formula :=
  .all "s" .value <| .forall_ "i" .value
    [.term (stringGetTerm (.var .value "s") (.var .value "i"))] <|
    .unpred .isChar (stringGetTerm (.var .value "s") (.var .value "i"))

def stringSubPre : Formula :=
  let pos := .unop .toInt (.var .value "pos")
  let len := .unop .toInt (.var .value "len")
  let strlen := .unop .seqLen (.unop .toString (.var .value "s"))
  .and
    (.binpred .le (.const (.i 0)) pos)
    (.and
      (.binpred .le (.const (.i 0)) len)
      (.binpred .le (.binop .add pos len) strlen))

/-- The value-level FOL term for `String.sub s pos len`. -/
def stringSubTerm (s pos len : Term .value) : Term .value :=
  terTerm "string_sub" s pos len

def stringSubDefAxiom : Formula :=
  .all "s" .value <| .all "pos" .value <| .forall_ "len" .value
    [.term (stringSubTerm (.var .value "s") (.var .value "pos") (.var .value "len"))] <|
    .implies stringSubPre <|
      .eq .string
        (.unop .toString (stringSubTerm (.var .value "s") (.var .value "pos") (.var .value "len")))
        (.terop .seqExtract
          (.unop .toString (.var .value "s"))
          (.unop .toInt (.var .value "pos"))
          (.unop .toInt (.var .value "len")))

def stringSubTypeAxiom : Formula :=
  .all "s" .value <| .all "pos" .value <| .forall_ "len" .value
    [.term (stringSubTerm (.var .value "s") (.var .value "pos") (.var .value "len"))] <|
    .unpred .isStr (stringSubTerm (.var .value "s") (.var .value "pos") (.var .value "len"))

def stringEqualDefAxiom : Formula :=
  .all "a" .value <| .forall_ "b" .value
    [.term (binTerm "string_equal" (.var .value "a") (.var .value "b"))] <|
    .eq .bool
      (.unop .toBool (binTerm "string_equal" (.var .value "a") (.var .value "b")))
      (.binop (.eq (τ := .string)) (.unop .toString (.var .value "a")) (.unop .toString (.var .value "b")))

def stringStartsWithDefAxiom : Formula :=
  .all "prefix" .value <| .forall_ "s" .value
    [.term (binTerm "string_starts_with" (.var .value "prefix") (.var .value "s"))] <|
    .eq .bool
      (.unop .toBool (binTerm "string_starts_with" (.var .value "prefix") (.var .value "s")))
      (.binop .seqPrefixOf (.unop .toString (.var .value "prefix")) (.unop .toString (.var .value "s")))

def stringEndsWithDefAxiom : Formula :=
  .all "suffix" .value <| .forall_ "s" .value
    [.term (binTerm "string_ends_with" (.var .value "suffix") (.var .value "s"))] <|
    .eq .bool
      (.unop .toBool (binTerm "string_ends_with" (.var .value "suffix") (.var .value "s")))
      (.binop .seqSuffixOf (.unop .toString (.var .value "suffix")) (.unop .toString (.var .value "s")))

/-! ## `String.length` -/

/-- `String.length`: byte length, built by `Pure.Unary`. -/
def stringLengthB : Pure.Unary where
  name     := "string_length"
  path     := some ("String", ["length"])
  arg      := .str
  res      := .int
  f        := (fun s => (s.length : Int) : List UInt8 → Int)
  typing   := monoTyping .one
  defAxiom := stringLengthDefAxiom

def stringLength : Intrinsic := stringLengthB.toIntrinsic

@[simp] theorem stringLength_arity : stringLength.arity = .one := rfl
@[simp] theorem stringLength_folSym : stringLength.folSym = some stringLengthSym := rfl

def stringLengthLawful : stringLengthB.Lawful where
  argL       := Embedding.lawfulStr
  resL       := Embedding.lawfulInt
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by intrinsic_def_eval [unTerm, stringLengthB, stringLengthDefAxiom]; intros; rfl

instance : IntrinsicSound [stringLength] stringLength := stringLengthLawful.sound

/-! ## `String.cat` -/

/-- `String.cat`: byte-string concatenation, built by `Pure.Binary`. -/
def stringCatB : Pure.Binary where
  name     := "string_cat"
  path     := some ("String", ["cat"])
  arg₁     := .str
  arg₂     := .str
  res      := .str
  f        := (fun x y => x ++ y : List UInt8 → List UInt8 → List UInt8)
  typing   := monoTyping .two
  defAxiom := stringCatDefAxiom

def stringCat : Intrinsic := stringCatB.toIntrinsic

@[simp] theorem stringCat_arity : stringCat.arity = .two := rfl
@[simp] theorem stringCat_folSym : stringCat.folSym = some stringCatSym := rfl

def stringCatLawful : stringCatB.Lawful where
  argL₁      := Embedding.lawfulStr
  argL₂      := Embedding.lawfulStr
  resL       := Embedding.lawfulStr
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by intrinsic_def_eval [binTerm, stringCatB, stringCatDefAxiom]; intros; rfl

instance : IntrinsicSound [stringCat] stringCat := stringCatLawful.sound

/-! ## `String.get` -/

private theorem string_respects_argsEnv_two {s : FOL.Symbol .two} :
    ∀ (args : List (String × TinyML.Typ)) (vs : List Runtime.Val) {ρ : VerifM.Env},
      ρ.env.respects (some s) → (Spec.argsEnv ρ args vs).env.respects (some s)
  | [], _, _, h => h
  | _ :: _, [], _, h => h
  | (_, _) :: rest, _ :: vs, ρ, h => by
      simp only [Spec.argsEnv]
      refine string_respects_argsEnv_two rest vs ?_
      rw [VerifM.Env.updateConst_env]
      simpa only [Env.respects, Env.updateConst_binary] using h

/-- `String.get`: byte lookup, with OCaml's in-bounds precondition. -/
def stringGet : Intrinsic where
  arity  := .two
  name   := "string_get"
  path   := some ("String", ["get"])
  reduce := Reduce.pure fun (s, i) v =>
    ∃ bytes n, s = .str bytes ∧ i = .int n ∧ 0 ≤ n ∧ n < (bytes.length : Int) ∧
      v = .char (stringGetByte bytes n)
  wp     := fun (s, i) Q =>
    iprop(∃ bytes n,
      ⌜s = .str bytes ∧ i = .int n ∧ 0 ≤ n ∧ n < (bytes.length : Int)⌝ ∗
      Q (.char (stringGetByte bytes n)))
  spec   :=
    { args  := [("s", .string), ("i", .int)]
      retTy := .char
      pred  := .assert stringGetPre <|
        .ret ("ret",
          .assert (.eq .value (.var .value "ret")
            (stringGetTerm (.var .value "s") (.var .value "i")))
            (.ret ())) }
  typing := monoTyping .two
  folSym := some stringGetSym
  axioms := [⟨stringGetDefAxiom, .high⟩, ⟨stringGetTypeAxiom, .high⟩]

@[simp] theorem stringGet_arity : stringGet.arity = .two := rfl
@[simp] theorem stringGet_folSym : stringGet.folSym = some stringGetSym := rfl

@[simp] theorem stringGet.toWp_eq (s i : Runtime.Val) (Q : Runtime.Val → iProp) :
    stringGet.toWp [s, i] Q =
      iprop(∃ bytes n,
        ⌜s = .str bytes ∧ i = .int n ∧ 0 ≤ n ∧ n < (bytes.length : Int)⌝ ∗
        Q (.char (stringGetByte bytes n))) := rfl

@[simp] theorem stringGet.toReduce_eq (s i v : Runtime.Val) (μ μ' : TinyML.Heap) :
    stringGet.toReduce [s, i] μ v μ' =
      ((∃ bytes n, s = .str bytes ∧ i = .int n ∧ 0 ≤ n ∧
        n < (bytes.length : Int) ∧ v = .char (stringGetByte bytes n)) ∧ μ' = μ) := rfl

@[simp] theorem stringGet.instantiate_args (σ : TinyML.TyVar → TinyML.Typ) :
    (stringGet.spec.instantiate σ).args = [("s", .string), ("i", .int)] := by
  simp [stringGet, Spec.instantiate, TinyML.Typ.subst]

@[simp] theorem stringGet.instantiate_retTy (σ : TinyML.TyVar → TinyML.Typ) :
    (stringGet.spec.instantiate σ).retTy = .char := by
  simp [stringGet, Spec.instantiate, TinyML.Typ.subst]

@[simp] theorem stringGet.spec_pred :
    stringGet.spec.pred = .assert stringGetPre
      (.ret ("ret",
        .assert (.eq .value (.var .value "ret")
          (stringGetTerm (.var .value "s") (.var .value "i")))
          (.ret ()))) := rfl

instance : IntrinsicSound [stringGet] stringGet where
  specWf := fun _ hsub hwf =>
    specWf_of_base (by apply PredTrans.checkWf_ok; rfl) hsub hwf
  wp_sound := by
    intro _ ctx hctx vs Φ
    match vs with
    | [] => exact false_elim
    | [_] => exact false_elim
    | _ :: _ :: _ :: _ => exact false_elim
    | [s, i] =>
      have hred : ∀ bytes n μ v μ',
          ctx stringGet.name [.str bytes, .int n] μ v μ'
            ↔ (0 ≤ n ∧ n < (bytes.length : Int) ∧ v = .char (stringGetByte bytes n)) ∧
              μ' = μ := by
        intro bytes n μ v μ'
        rw [hctx]
        simp only [stringGet.toReduce_eq]
        constructor
        · rintro ⟨⟨bytes', n', hs, hi, hlo, hhi, hv⟩, hμ⟩
          cases hs
          cases hi
          exact ⟨⟨hlo, hhi, hv⟩, hμ⟩
        · rintro ⟨⟨hlo, hhi, hv⟩, hμ⟩
          exact ⟨⟨bytes, n, rfl, rfl, hlo, hhi, hv⟩, hμ⟩
      show iprop(∃ bytes n,
        ⌜s = .str bytes ∧ i = .int n ∧ 0 ≤ n ∧ n < (bytes.length : Int)⌝ ∗
        Φ (.char (stringGetByte bytes n))) ⊢ _
      istart
      iintro ⟨%bytes, %n, %ha, HΦ⟩
      obtain ⟨rfl, rfl, hlo, hhi⟩ := ha
      iapply (wp.prim_pure (hred bytes n) ⟨.char (stringGetByte bytes n), hlo, hhi, rfl⟩)
      iintro %v %hv
      obtain ⟨_, _, rfl⟩ := hv
      iexact HΦ
  bridge := by
    intro _ σ Θ vs ρ Φ hρ
    simp only [stringGet.instantiate_args, stringGet.instantiate_retTy,
      Spec.instantiate_pred, stringGet.spec_pred, List.map_cons, List.map_nil]
    match vs with
    | [] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [_] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | _ :: _ :: _ :: _ =>
        exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [s, i] =>
      simp only [PredTrans.apply, Assertion.pre]
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ s [i] _ _).1 $$ Hvs
      icases Hcons with ⟨Hs, Hrest⟩
      ihave Hcons2 := (TinyML.ValsHaveTypes.cons Θ i [] _ _).1 $$ Hrest
      icases Hcons2 with ⟨Hi, _⟩
      ihave Hseq := (TinyML.ValHasType.string Θ s).1 $$ Hs
      ipure Hseq
      obtain ⟨bytes, rfl⟩ := Hseq
      ihave Hieq := (TinyML.ValHasType.int Θ i).1 $$ Hi
      ipure Hieq
      obtain ⟨n, rfl⟩ := Hieq
      icases Hpred with ⟨%hpre, Hpost⟩
      have hbounds : 0 ≤ n ∧ n < (bytes.length : Int) := by
        simpa [stringGetPre, Spec.argsEnv, Formula.eval, Term.eval, Const.denote,
          VerifM.Env.updateConst_env, Env.lookupConst_updateConst_same,
          Env.lookupConst_updateConst_ne (show "s" ≠ "i" by decide)] using hpre
      simp only [stringGet.toWp_eq]
      iexists bytes
      iexists n
      isplitr [Hpost]
      · ipureintro
        exact ⟨rfl, rfl, hbounds.1, hbounds.2⟩
      · have hassert : (Formula.eq .value (.var .value "ret")
            (stringGetTerm (.var .value "s") (.var .value "i"))).eval
            ((Spec.argsEnv ρ stringGet.specArgs [.str bytes, .int n]).updateConst
              .value "ret" (.char (stringGetByte bytes n))).env := by
          have hargs := string_respects_argsEnv_two stringGet.specArgs [.str bytes, .int n] hρ
          have hbin : (Spec.argsEnv ρ stringGet.specArgs [.str bytes, .int n]).env.binary
              .value .value .value "string_get" = fun a b => stringGetSym.interp (a, b) := by
            simpa [Env.respects, stringGetSym] using hargs
          show .char (stringGetByte bytes n) =
            (Spec.argsEnv ρ stringGet.specArgs [.str bytes, .int n]).env.binary
              .value .value .value "string_get" (.str bytes) (.int n)
          simp [stringGetByte, stringGetSym, hbin, valStr, valInt]
        refine (assert_ret_apply Θ _ "ret" _ _ (.char (stringGetByte bytes n)) hassert).trans ?_
        iintro Hwand
        iapply Hwand
        exact TinyML.ValHasType.char_intro Θ (stringGetByte bytes n)
  axiomWf := by
    intro Δ hsub hwf a hφ
    simp only [stringGet, List.mem_cons, List.not_mem_nil, _root_.or_false] at hφ
    rcases hφ with rfl | rfl
    · exact Formula.wfIn_mono _ (by apply Formula.checkWf_ok; rfl) hsub hwf
    · exact Formula.wfIn_mono _ (by apply Formula.checkWf_ok; rfl) hsub hwf
  proof := by
    intro ρ hdeps a hφ
    simp only [stringGet, List.mem_cons, List.not_mem_nil, _root_.or_false] at hφ
    have hresp : ρ.respects (some stringGetSym) := by
      have h := hdeps stringGet (by simp)
      simpa [stringGet] using h
    rcases hφ with rfl | rfl
    · simp only [stringGetDefAxiom, Formula.all, Formula.eval]
      intro s i hpre
      have hbin : (((ρ.updateConst .value "s" s).updateConst .value "i" i).binary
          .value .value .value "string_get") = fun a b => stringGetSym.interp (a, b) := by
        rw [Env.updateConst_binary, Env.updateConst_binary]
        simpa [Env.respects, stringGetSym] using hresp
      simp [stringGetTerm, binTerm, stringGetSym, hbin,
        Term.eval, Env.lookupConst_updateConst_same,
        Env.lookupConst_updateConst_ne (show "s" ≠ "i" by decide), valStr, valInt]
      rfl
    · simp only [stringGetTypeAxiom, Formula.all, Formula.eval]
      intro s i
      have hbin : (((ρ.updateConst .value "s" s).updateConst .value "i" i).binary
          .value .value .value "string_get") = fun a b => stringGetSym.interp (a, b) := by
        rw [Env.updateConst_binary, Env.updateConst_binary]
        simpa [Env.respects, stringGetSym] using hresp
      simp [stringGetTerm, binTerm, stringGetSym, hbin, Term.eval,
        Env.lookupConst_updateConst_same,
        Env.lookupConst_updateConst_ne (show "s" ≠ "i" by decide), valStr, valInt]

/-! ## `String.sub` -/

private theorem string_respects_argsEnv_three {s : FOL.Symbol .three} :
    ∀ (args : List (String × TinyML.Typ)) (vs : List Runtime.Val) {ρ : VerifM.Env},
      ρ.env.respects (some s) → (Spec.argsEnv ρ args vs).env.respects (some s)
  | [], _, _, h => h
  | _ :: _, [], _, h => h
  | (_, _) :: rest, _ :: vs, ρ, h => by
      simp only [Spec.argsEnv]
      refine string_respects_argsEnv_three rest vs ?_
      rw [VerifM.Env.updateConst_env]
      simpa only [Env.respects, Env.updateConst_ternary] using h

/-- `String.sub`: byte-string slicing, with OCaml's bounds precondition. -/
def stringSub : Intrinsic where
  arity  := .three
  name   := "string_sub"
  path   := some ("String", ["sub"])
  reduce := Reduce.pure fun (s, pos, len) v =>
    ∃ bytes p n, s = .str bytes ∧ pos = .int p ∧ len = .int n ∧
      0 ≤ p ∧ 0 ≤ n ∧ p + n ≤ (bytes.length : Int) ∧
      v = .str (stringSubBytes bytes p n)
  wp     := fun (s, pos, len) Q =>
    iprop(∃ bytes p n,
      ⌜s = .str bytes ∧ pos = .int p ∧ len = .int n ∧
        0 ≤ p ∧ 0 ≤ n ∧ p + n ≤ (bytes.length : Int)⌝ ∗
      Q (.str (stringSubBytes bytes p n)))
  spec   :=
    { args  := [("s", .string), ("pos", .int), ("len", .int)]
      retTy := .string
      pred  := .assert stringSubPre <|
        .ret ("ret",
          .assert (.eq .value (.var .value "ret")
            (stringSubTerm (.var .value "s") (.var .value "pos") (.var .value "len")))
            (.ret ())) }
  typing := monoTyping .three
  folSym := some stringSubSym
  axioms := [⟨stringSubDefAxiom, .high⟩, ⟨stringSubTypeAxiom, .high⟩]

@[simp] theorem stringSub_arity : stringSub.arity = .three := rfl
@[simp] theorem stringSub_folSym : stringSub.folSym = some stringSubSym := rfl

@[simp] theorem stringSub.toWp_eq (s pos len : Runtime.Val) (Q : Runtime.Val → iProp) :
    stringSub.toWp [s, pos, len] Q =
      iprop(∃ bytes p n,
        ⌜s = .str bytes ∧ pos = .int p ∧ len = .int n ∧
          0 ≤ p ∧ 0 ≤ n ∧ p + n ≤ (bytes.length : Int)⌝ ∗
        Q (.str (stringSubBytes bytes p n))) := rfl

@[simp] theorem stringSub.toReduce_eq
    (s pos len v : Runtime.Val) (μ μ' : TinyML.Heap) :
    stringSub.toReduce [s, pos, len] μ v μ' =
      ((∃ bytes p n, s = .str bytes ∧ pos = .int p ∧ len = .int n ∧
        0 ≤ p ∧ 0 ≤ n ∧ p + n ≤ (bytes.length : Int) ∧
        v = .str (stringSubBytes bytes p n)) ∧ μ' = μ) := rfl

@[simp] theorem stringSub.instantiate_args (σ : TinyML.TyVar → TinyML.Typ) :
    (stringSub.spec.instantiate σ).args = [("s", .string), ("pos", .int), ("len", .int)] := by
  simp [stringSub, Spec.instantiate, TinyML.Typ.subst]

@[simp] theorem stringSub.instantiate_retTy (σ : TinyML.TyVar → TinyML.Typ) :
    (stringSub.spec.instantiate σ).retTy = .string := by
  simp [stringSub, Spec.instantiate, TinyML.Typ.subst]

@[simp] theorem stringSub.spec_pred :
    stringSub.spec.pred = .assert stringSubPre
      (.ret ("ret",
        .assert (.eq .value (.var .value "ret")
          (stringSubTerm (.var .value "s") (.var .value "pos") (.var .value "len")))
          (.ret ()))) := rfl

instance : IntrinsicSound [stringSub] stringSub where
  specWf := fun _ hsub hwf =>
    specWf_of_base (by apply PredTrans.checkWf_ok; rfl) hsub hwf
  wp_sound := by
    intro _ ctx hctx vs Φ
    match vs with
    | [] => exact false_elim
    | [_] => exact false_elim
    | [_, _] => exact false_elim
    | _ :: _ :: _ :: _ :: _ => exact false_elim
    | [s, pos, len] =>
      have hred : ∀ bytes p n μ v μ',
          ctx stringSub.name [.str bytes, .int p, .int n] μ v μ'
            ↔ (0 ≤ p ∧ 0 ≤ n ∧ p + n ≤ (bytes.length : Int) ∧
              v = .str (stringSubBytes bytes p n)) ∧ μ' = μ := by
        intro bytes p n μ v μ'
        rw [hctx]
        simp only [stringSub.toReduce_eq]
        constructor
        · rintro ⟨⟨bytes', p', n', hs, hp, hn, hp0, hn0, hbound, hv⟩, hμ⟩
          cases hs
          cases hp
          cases hn
          exact ⟨⟨hp0, hn0, hbound, hv⟩, hμ⟩
        · rintro ⟨⟨hp0, hn0, hbound, hv⟩, hμ⟩
          exact ⟨⟨bytes, p, n, rfl, rfl, rfl, hp0, hn0, hbound, hv⟩, hμ⟩
      show iprop(∃ bytes p n,
        ⌜s = .str bytes ∧ pos = .int p ∧ len = .int n ∧
          0 ≤ p ∧ 0 ≤ n ∧ p + n ≤ (bytes.length : Int)⌝ ∗
        Φ (.str (stringSubBytes bytes p n))) ⊢ _
      istart
      iintro ⟨%bytes, %p, %n, %ha, HΦ⟩
      obtain ⟨rfl, rfl, rfl, hp0, hn0, hbound⟩ := ha
      iapply (wp.prim_pure (hred bytes p n)
        ⟨.str (stringSubBytes bytes p n), hp0, hn0, hbound, rfl⟩)
      iintro %v %hv
      obtain ⟨_, _, _, rfl⟩ := hv
      iexact HΦ
  bridge := by
    intro _ σ Θ vs ρ Φ hρ
    simp only [stringSub.instantiate_args, stringSub.instantiate_retTy,
      Spec.instantiate_pred, stringSub.spec_pred, List.map_cons, List.map_nil]
    match vs with
    | [] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [_] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [_, _] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | _ :: _ :: _ :: _ :: _ =>
        exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [s, pos, len] =>
      simp only [PredTrans.apply, Assertion.pre]
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ s [pos, len] _ _).1 $$ Hvs
      icases Hcons with ⟨Hs, Hrest⟩
      ihave Hcons2 := (TinyML.ValsHaveTypes.cons Θ pos [len] _ _).1 $$ Hrest
      icases Hcons2 with ⟨Hpos, Hrest2⟩
      ihave Hcons3 := (TinyML.ValsHaveTypes.cons Θ len [] _ _).1 $$ Hrest2
      icases Hcons3 with ⟨Hlen, _⟩
      ihave Hseq := (TinyML.ValHasType.string Θ s).1 $$ Hs
      ipure Hseq
      obtain ⟨bytes, rfl⟩ := Hseq
      ihave Hposeq := (TinyML.ValHasType.int Θ pos).1 $$ Hpos
      ipure Hposeq
      obtain ⟨p, rfl⟩ := Hposeq
      ihave Hleneq := (TinyML.ValHasType.int Θ len).1 $$ Hlen
      ipure Hleneq
      obtain ⟨n, rfl⟩ := Hleneq
      icases Hpred with ⟨%hpre, Hpost⟩
      have hbounds : 0 ≤ p ∧ 0 ≤ n ∧ p + n ≤ (bytes.length : Int) := by
        simpa [stringSubPre, Spec.argsEnv, Formula.eval, Term.eval, Const.denote,
          VerifM.Env.updateConst_env, Env.lookupConst_updateConst_same,
          Env.lookupConst_updateConst_ne (show "s" ≠ "pos" by decide),
          Env.lookupConst_updateConst_ne (show "s" ≠ "len" by decide),
          Env.lookupConst_updateConst_ne (show "pos" ≠ "len" by decide)] using hpre
      simp only [stringSub.toWp_eq]
      iexists bytes
      iexists p
      iexists n
      isplitr [Hpost]
      · ipureintro
        exact ⟨rfl, rfl, rfl, hbounds.1, hbounds.2.1, hbounds.2.2⟩
      · have hassert : (Formula.eq .value (.var .value "ret")
            (stringSubTerm (.var .value "s") (.var .value "pos") (.var .value "len"))).eval
            ((Spec.argsEnv ρ stringSub.specArgs [.str bytes, .int p, .int n]).updateConst
              .value "ret" (.str (stringSubBytes bytes p n))).env := by
          have hargs := string_respects_argsEnv_three stringSub.specArgs
            [.str bytes, .int p, .int n] hρ
          have hter : (Spec.argsEnv ρ stringSub.specArgs [.str bytes, .int p, .int n]).env.ternary
              .value .value .value .value "string_sub" =
                fun a b c => stringSubSym.interp (a, b, c) := by
            simpa [Env.respects, stringSubSym] using hargs
          show .str (stringSubBytes bytes p n) =
            (Spec.argsEnv ρ stringSub.specArgs [.str bytes, .int p, .int n]).env.ternary
              .value .value .value .value "string_sub" (.str bytes) (.int p) (.int n)
          simp [stringSubBytes, stringSubSym, hter, valStr, valInt]
        refine (assert_ret_apply Θ _ "ret" _ _ (.str (stringSubBytes bytes p n)) hassert).trans ?_
        iintro Hwand
        iapply Hwand
        exact TinyML.ValHasType.string_intro Θ (stringSubBytes bytes p n)
  axiomWf := by
    intro Δ hsub hwf a hφ
    simp only [stringSub, List.mem_cons, List.not_mem_nil, _root_.or_false] at hφ
    rcases hφ with rfl | rfl
    · exact Formula.wfIn_mono _ (by apply Formula.checkWf_ok; rfl) hsub hwf
    · exact Formula.wfIn_mono _ (by apply Formula.checkWf_ok; rfl) hsub hwf
  proof := by
    intro ρ hdeps a hφ
    simp only [stringSub, List.mem_cons, List.not_mem_nil, _root_.or_false] at hφ
    have hresp : ρ.respects (some stringSubSym) := by
      have h := hdeps stringSub (by simp)
      simpa [stringSub] using h
    rcases hφ with rfl | rfl
    · simp only [stringSubDefAxiom, Formula.all, Formula.eval]
      intro s pos len hpre
      have hter : ((((ρ.updateConst .value "s" s).updateConst .value "pos" pos).updateConst
            .value "len" len).ternary .value .value .value .value "string_sub") =
          fun a b c => stringSubSym.interp (a, b, c) := by
        rw [Env.updateConst_ternary, Env.updateConst_ternary, Env.updateConst_ternary]
        simpa [Env.respects, stringSubSym] using hresp
      simp [stringSubTerm, terTerm, stringSubSym, stringSubBytes, hter, Term.eval,
        Env.lookupConst_updateConst_same,
        Env.lookupConst_updateConst_ne (show "s" ≠ "pos" by decide),
        Env.lookupConst_updateConst_ne (show "s" ≠ "len" by decide),
        Env.lookupConst_updateConst_ne (show "pos" ≠ "len" by decide),
        valStr, valInt]
      rfl
    · simp only [stringSubTypeAxiom, Formula.all, Formula.eval]
      intro s pos len
      have hter : ((((ρ.updateConst .value "s" s).updateConst .value "pos" pos).updateConst
            .value "len" len).ternary .value .value .value .value "string_sub") =
          fun a b c => stringSubSym.interp (a, b, c) := by
        rw [Env.updateConst_ternary, Env.updateConst_ternary, Env.updateConst_ternary]
        simpa [Env.respects, stringSubSym] using hresp
      simp [stringSubTerm, terTerm, stringSubSym, stringSubBytes, hter, Term.eval,
        Env.lookupConst_updateConst_same,
        Env.lookupConst_updateConst_ne (show "s" ≠ "pos" by decide),
        Env.lookupConst_updateConst_ne (show "s" ≠ "len" by decide),
        Env.lookupConst_updateConst_ne (show "pos" ≠ "len" by decide),
        valStr, valInt]

/-! ## `String.equal` -/

/-- `String.equal`: byte-string equality, built by `Pure.Binary`. -/
def stringEqualB : Pure.Binary where
  name     := "string_equal"
  path     := some ("String", ["equal"])
  arg₁     := .str
  arg₂     := .str
  res      := .bool
  f        := (fun x y => x == y : List UInt8 → List UInt8 → Bool)
  typing   := monoTyping .two
  defAxiom := stringEqualDefAxiom

def stringEqual : Intrinsic := stringEqualB.toIntrinsic

@[simp] theorem stringEqual_arity : stringEqual.arity = .two := rfl
@[simp] theorem stringEqual_folSym : stringEqual.folSym = some stringEqualSym := rfl

def stringEqualLawful : stringEqualB.Lawful where
  argL₁      := Embedding.lawfulStr
  argL₂      := Embedding.lawfulStr
  resL       := Embedding.lawfulBool
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by
    intrinsic_def_eval [binTerm, stringEqualB, stringEqualDefAxiom, Bool.beq_eq_decide_eq]
    intros; rfl

instance : IntrinsicSound [stringEqual] stringEqual := stringEqualLawful.sound

/-! ## `String.starts_with` -/

/-- `String.starts_with`: byte-string prefix test, built by `Pure.Binary`. -/
def stringStartsWithB : Pure.Binary where
  name     := "string_starts_with"
  path     := some ("String", ["starts_with"])
  arg₁     := .str
  arg₂     := .str
  res      := .bool
  f        := (fun x y => x.isPrefixOf y : List UInt8 → List UInt8 → Bool)
  typing   := monoTyping .two
  defAxiom := stringStartsWithDefAxiom

def stringStartsWith : Intrinsic := stringStartsWithB.toIntrinsic

@[simp] theorem stringStartsWith_arity : stringStartsWith.arity = .two := rfl
@[simp] theorem stringStartsWith_folSym :
    stringStartsWith.folSym = some stringStartsWithSym := rfl

def stringStartsWithLawful : stringStartsWithB.Lawful where
  argL₁      := Embedding.lawfulStr
  argL₂      := Embedding.lawfulStr
  resL       := Embedding.lawfulBool
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by
    intrinsic_def_eval [binTerm, stringStartsWithB, stringStartsWithDefAxiom]; intros; rfl

instance : IntrinsicSound [stringStartsWith] stringStartsWith := stringStartsWithLawful.sound

/-! ## `String.ends_with` -/

/-- `String.ends_with`: byte-string suffix test, built by `Pure.Binary`. -/
def stringEndsWithB : Pure.Binary where
  name     := "string_ends_with"
  path     := some ("String", ["ends_with"])
  arg₁     := .str
  arg₂     := .str
  res      := .bool
  f        := (fun x y => x.isSuffixOf y : List UInt8 → List UInt8 → Bool)
  typing   := monoTyping .two
  defAxiom := stringEndsWithDefAxiom

def stringEndsWith : Intrinsic := stringEndsWithB.toIntrinsic

@[simp] theorem stringEndsWith_arity : stringEndsWith.arity = .two := rfl
@[simp] theorem stringEndsWith_folSym : stringEndsWith.folSym = some stringEndsWithSym := rfl

def stringEndsWithLawful : stringEndsWithB.Lawful where
  argL₁      := Embedding.lawfulStr
  argL₂      := Embedding.lawfulStr
  resL       := Embedding.lawfulBool
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by
    intrinsic_def_eval [binTerm, stringEndsWithB, stringEndsWithDefAxiom]; intros; rfl

instance : IntrinsicSound [stringEndsWith] stringEndsWith := stringEndsWithLawful.sound

end Intrinsics
end Stdlib
