-- SUMMARY: Character intrinsics (`Char.code`, `Char.chr`, `Char.equal`) and their soundness instances.
import Mica.Stdlib.IntStd

open Iris Iris.BI

namespace Stdlib

open Verifier

namespace Intrinsics

/-! ## FOL symbols -/

/-- FOL symbol for `Char.code`. -/
def charCodeSym : FOL.Symbol .one where
  name   := "char_code"
  interp := fun a => .int (valChar a).toNat

/-- FOL-level result of `Char.chr`: agree with byte conversion on OCaml's
    valid range, and return zero outside it. -/
def charChrByte (n : Int) : UInt8 :=
  if n ≥ 0 then
    if n < 256 then UInt8.ofNat n.toNat else 0
  else 0

/-- FOL symbol for `Char.chr`. -/
def charChrSym : FOL.Symbol .one where
  name   := "char_chr"
  interp := fun a => .char (charChrByte (valInt a))

/-- FOL symbol for `Char.equal`. -/
def charEqualSym : FOL.Symbol .two where
  name   := "char_equal"
  interp := fun (a, b) => .bool (valChar a == valChar b)

@[simp] theorem charCodeSym_name : charCodeSym.name = "char_code" := rfl
@[simp] theorem charChrSym_name : charChrSym.name = "char_chr" := rfl
@[simp] theorem charEqualSym_name : charEqualSym.name = "char_equal" := rfl

/-! ## `Char.code` -/

def charCodeDefAxiom : Formula :=
  .forall_ "c" .value [.term (unTerm "char_code" (.var .value "c"))] <|
    .eq .int
      (.unop .toInt (unTerm "char_code" (.var .value "c")))
      (.unop .charToInt (.unop .toChar (.var .value "c")))

/-- `Char.code`: byte value as an integer. -/
def charCodeB : Pure.Unary where
  name     := "char_code"
  path     := some ("Char", ["code"])
  arg      := .char
  res      := .int
  f        := (fun c => (c.toNat : Int) : UInt8 → Int)
  defAxiom := charCodeDefAxiom

def charCode : Intrinsic := charCodeB.toIntrinsic

@[simp] theorem charCode_arity : charCode.arity = .one := rfl
@[simp] theorem charCode_folSym : charCode.folSym = some charCodeSym := rfl

def charCodeLawful : charCodeB.Lawful where
  argL       := Embedding.lawfulChar
  resL       := Embedding.lawfulInt
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by
    intrinsic_def_eval [unTerm, charCodeB, charCodeDefAxiom]
    intro v
    rfl

instance : IntrinsicSound [charCode] charCode := charCodeLawful.sound

/-! ## `Char.chr` -/

def charChrPre : Formula :=
  let n := .unop .toInt (.var .value "n")
  .and
    (.binpred .le (.const (.i 0)) n)
    (.binpred .lt n (.const (.i 256)))

/-- The value-level FOL term for `Char.chr n`. -/
def charChrTerm (n : Term .value) : Term .value :=
  unTerm "char_chr" n

/-- The byte result of the FOL-level `Char.chr` interpretation. Outside OCaml's
    valid range it is zero, matching `charChrByte`. -/
def charChrVal (n : Int) : Runtime.Val :=
  .char (charChrByte n)

def charChrDefAxiom : Formula :=
  .forall_ "n" .value [.term (unTerm "char_chr" (.var .value "n"))] <|
    .implies charChrPre <|
      .eq .char
        (.unop .toChar (unTerm "char_chr" (.var .value "n")))
        (.unop .intToChar (.unop .toInt (.var .value "n")))

def charChrTypeAxiom : Formula :=
  .forall_ "n" .value [.term (charChrTerm (.var .value "n"))] <|
    .unpred .isChar (charChrTerm (.var .value "n"))

private theorem char_respects_argsEnv_one {s : FOL.Symbol .one} :
    ∀ (args : List (String × TinyML.Typ)) (vs : List Runtime.Val) {ρ : VerifM.Env},
      ρ.env.respects (some s) → (Spec.argsEnv ρ args vs).env.respects (some s)
  | [], _, _, h => h
  | _ :: _, [], _, h => h
  | (_, _) :: rest, _ :: vs, ρ, h => by
      simp only [Spec.argsEnv]
      refine char_respects_argsEnv_one rest vs ?_
      rw [VerifM.Env.updateConst_env]
      simpa only [Env.respects, Env.updateConst_unary] using h

/-- `Char.chr`: integer to byte, with the OCaml precondition `0 <= n < 256`.
    The defining axiom only constrains the valid range, matching the spec
    precondition that rules out OCaml's raising cases. -/
def charChr : Intrinsic where
  arity  := .one
  name   := "char_chr"
  path   := some ("Char", ["chr"])
  reduce := Reduce.pure fun a v =>
    ∃ n, a = .int n ∧ 0 ≤ n ∧ n < 256 ∧ v = charChrVal n
  wp     := fun a Q =>
    iprop(∃ n, ⌜a = .int n ∧ 0 ≤ n ∧ n < 256⌝ ∗ Q (charChrVal n))
  spec   :=
    { args  := [("n", .int)]
      retTy := .char
      pred  := .assert charChrPre <|
        .ret ("ret",
          .assert (.eq .value (.var .value "ret") (charChrTerm (.var .value "n")))
            (.ret ())) }
  typing := monoTyping .one
  folSym := some charChrSym
  axioms := [⟨charChrDefAxiom, .high⟩, ⟨charChrTypeAxiom, .high⟩]

@[simp] theorem charChr_arity : charChr.arity = .one := rfl
@[simp] theorem charChr_folSym : charChr.folSym = some charChrSym := rfl

@[simp] theorem charChr.toWp_eq (a : Runtime.Val) (Q : Runtime.Val → iProp) :
    charChr.toWp [a] Q =
      iprop(∃ n, ⌜a = .int n ∧ 0 ≤ n ∧ n < 256⌝ ∗ Q (charChrVal n)) := rfl

@[simp] theorem charChr.toReduce_eq (a v : Runtime.Val) (μ μ' : TinyML.Heap) :
    charChr.toReduce [a] μ v μ' =
      ((∃ n, a = .int n ∧ 0 ≤ n ∧ n < 256 ∧ v = charChrVal n) ∧ μ' = μ) := rfl

@[simp] theorem charChr.instantiate_args (σ : TinyML.TyVar → TinyML.Typ) :
    (charChr.spec.instantiate σ).args = [("n", .int)] := by
  simp [charChr, Spec.instantiate, TinyML.Typ.subst]

@[simp] theorem charChr.instantiate_retTy (σ : TinyML.TyVar → TinyML.Typ) :
    (charChr.spec.instantiate σ).retTy = .char := by
  simp [charChr, Spec.instantiate, TinyML.Typ.subst]

@[simp] theorem charChr.spec_pred :
    charChr.spec.pred = .assert charChrPre
      (.ret ("ret",
        .assert (.eq .value (.var .value "ret") (charChrTerm (.var .value "n")))
          (.ret ()))) := rfl

instance : IntrinsicSound [charChr] charChr where
  specWf := fun _ hsub hwf =>
    specWf_of_base (by apply PredTrans.checkWf_ok; rfl) hsub hwf
  wp_sound := by
    intro _ ctx hctx vs Φ
    match vs with
    | [] => exact false_elim
    | _ :: _ :: _ => exact false_elim
    | [a] =>
      have hred : ∀ n μ v μ',
          ctx charChr.name [.int n] μ v μ'
            ↔ (0 ≤ n ∧ n < 256 ∧ v = charChrVal n) ∧ μ' = μ := by
        intro n μ v μ'
        rw [hctx]
        simp only [charChr.toReduce_eq]
        constructor
        · rintro ⟨⟨n', harg, hlo, hhi, hv⟩, hμ⟩
          cases harg
          exact ⟨⟨hlo, hhi, hv⟩, hμ⟩
        · rintro ⟨⟨hlo, hhi, hv⟩, hμ⟩
          exact ⟨⟨n, rfl, hlo, hhi, hv⟩, hμ⟩
      show iprop(∃ n, ⌜a = .int n ∧ 0 ≤ n ∧ n < 256⌝ ∗ Φ (charChrVal n)) ⊢ _
      istart
      iintro ⟨%n, %ha, HΦ⟩
      obtain ⟨rfl, hlo, hhi⟩ := ha
      iapply (wp.prim_pure (hred n) ⟨charChrVal n, hlo, hhi, rfl⟩)
      iintro %v %hv
      obtain ⟨_, _, rfl⟩ := hv
      iexact HΦ
  bridge := by
    intro _ σ Θ vs ρ Φ hρ
    simp only [charChr.instantiate_args, charChr.instantiate_retTy,
      Spec.instantiate_pred, charChr.spec_pred, List.map_cons, List.map_nil]
    match vs with
    | [] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | _ :: _ :: _ =>
        exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [v] =>
      simp only [PredTrans.apply, Assertion.pre]
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ v [] _ _).1 $$ Hvs
      icases Hcons with ⟨Hv, _⟩
      ihave Hveq := (TinyML.ValHasType.int Θ v).1 $$ Hv
      ipure Hveq
      obtain ⟨n, rfl⟩ := Hveq
      icases Hpred with ⟨%hpre, Hpost⟩
      have hbounds : 0 ≤ n ∧ n < 256 := by
        simpa [charChrPre, Spec.argsEnv, Formula.eval, Term.eval, Const.denote,
          VerifM.Env.updateConst_env, Env.lookupConst_updateConst_same] using hpre
      simp only [charChr.toWp_eq]
      iexists n
      isplitr [Hpost]
      · ipureintro
        exact ⟨rfl, hbounds.1, hbounds.2⟩
      · have hassert : (Formula.eq .value (.var .value "ret")
            (charChrTerm (.var .value "n"))).eval
            ((Spec.argsEnv ρ charChr.specArgs [.int n]).updateConst
              .value "ret" (charChrVal n)).env := by
          have hargs := char_respects_argsEnv_one charChr.specArgs [.int n] hρ
          have hun : (Spec.argsEnv ρ charChr.specArgs [.int n]).env.unary
              .value .value "char_chr" = charChrSym.interp := by
            simpa [Env.respects, charChrSym] using hargs
          show charChrVal n =
            (Spec.argsEnv ρ charChr.specArgs [.int n]).env.unary
              .value .value "char_chr" (.int n)
          simp [charChrVal, charChrSym, hun, valInt]
        refine (assert_ret_apply Θ _ "ret" _ _ (charChrVal n) hassert).trans ?_
        iintro Hwand
        iapply Hwand
        exact TinyML.ValHasType.char_intro Θ (charChrByte n)
  axiomWf := by
    intro Δ hsub hwf a hφ
    simp only [charChr, List.mem_cons, List.not_mem_nil, _root_.or_false] at hφ
    rcases hφ with rfl | rfl
    · exact Formula.wfIn_mono _ (by apply Formula.checkWf_ok; rfl) hsub hwf
    · exact Formula.wfIn_mono _ (by apply Formula.checkWf_ok; rfl) hsub hwf
  proof := by
    intro ρ hdeps a hφ
    simp only [charChr, List.mem_cons, List.not_mem_nil, _root_.or_false] at hφ
    have hresp : ρ.respects (some charChrSym) := by
      have h := hdeps charChr (by simp)
      simpa [charChr] using h
    rcases hφ with rfl | rfl
    · simp only [charChrDefAxiom, Formula.eval]
      intro x hpre
      have hun : (ρ.updateConst .value "n" x).unary .value .value "char_chr" =
          charChrSym.interp := by
        rw [Env.updateConst_unary]
        simpa [Env.respects] using hresp
      have hbounds : 0 ≤ valInt x ∧ valInt x < 256 := by
        simpa [charChrPre, Formula.eval, Term.eval, Const.denote,
          Env.lookupConst_updateConst_same, valInt] using hpre
      simp [unTerm, Term.eval, Env.lookupConst_updateConst_same, hun, charChrSym]
      cases x <;> simp [valInt, charChrByte] at hbounds ⊢
      rw [if_pos hbounds.1, if_pos hbounds.2, Int.emod_eq_of_lt hbounds.1 hbounds.2]
    · simp only [charChrTypeAxiom, Formula.eval]
      intro x
      have hun : (ρ.updateConst .value "n" x).unary .value .value "char_chr" =
          charChrSym.interp := by
        rw [Env.updateConst_unary]
        simpa [Env.respects] using hresp
      simp [charChrTerm, unTerm, Term.eval, Env.lookupConst_updateConst_same,
        hun, charChrSym, valInt]

/-! ## `Char.equal` -/

def charEqualDefAxiom : Formula :=
  .all "a" .value <| .forall_ "b" .value
    [.term (binTerm "char_equal" (.var .value "a") (.var .value "b"))] <|
    .eq .bool
      (.unop .toBool (binTerm "char_equal" (.var .value "a") (.var .value "b")))
      (.binop (.eq (τ := .char)) (.unop .toChar (.var .value "a")) (.unop .toChar (.var .value "b")))

/-- `Char.equal`: byte equality. -/
def charEqualB : Pure.Binary where
  name     := "char_equal"
  path     := some ("Char", ["equal"])
  arg      := .char
  res      := .bool
  f        := (fun x y => x == y : UInt8 → UInt8 → Bool)
  defAxiom := charEqualDefAxiom

def charEqual : Intrinsic := charEqualB.toIntrinsic

@[simp] theorem charEqual_arity : charEqual.arity = .two := rfl
@[simp] theorem charEqual_folSym : charEqual.folSym = some charEqualSym := rfl

def charEqualLawful : charEqualB.Lawful where
  argL       := Embedding.lawfulChar
  resL       := Embedding.lawfulBool
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by
    intrinsic_def_eval [binTerm, charEqualB, charEqualDefAxiom, Bool.beq_eq_decide_eq]
    intros; rfl

instance : IntrinsicSound [charEqual] charEqual := charEqualLawful.sound

end Intrinsics
end Stdlib
