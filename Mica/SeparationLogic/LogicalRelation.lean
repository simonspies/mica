-- SUMMARY: Iris logical relations for TinyML values and types, together with formula generation for type constraints.
import Mica.TinyML.Common
import Mica.TinyML.Types
import Mica.TinyML.RuntimeExpr
import Mica.TinyML.OpSem
import Mica.FOL.Formulas
import Mica.SeparationLogic.Axioms
import Iris.BI.Lib.Fixpoint

open Iris Iris.BI Iris.OFE

namespace TinyML

/-!
The logical relation in this file mixes two kinds of recursion:

* an outer guarded/step-indexed fixpoint for references; and
* an inner order-theoretic least fixpoint for recursive type names.

The point is to keep recursive type unfolding immediate while putting the
non-monotone invariant boundary in the outer, contractive recursion.
-/

/-- Continuation type for the inner recursive interpretation of named types. -/
abbrev RecCont := Runtime.Val → TypeName → List Typ → iProp

/-- Index of the inner recursive type environment fixpoint. -/
abbrev RecIdx := LeibnizO (Runtime.Val × TypeName × List Typ)

/-- Reinterpret a predicate over `RecIdx` as a curried continuation. -/
@[reducible] def RecCont.ofPred (Φ : RecIdx → iProp) : RecCont :=
  fun v T args => Φ ⟨(v, T, args)⟩

/-- The outer approximation ranges over closed value relations. -/
abbrev ValShape := Runtime.Val → Typ → iProp

/- One structural layer of the value relation.

References use the outer approximation `R`; named types use the inner
continuation `k`. Tuples and sums are structural and mutually recursive with
the list/sum helpers below.
-/
mutual
  def ValRelBody (R : ValShape) (v : Runtime.Val) (t : Typ) (k : RecCont) : iProp :=
    match t with
    | .unit       => iprop(⌜v = .unit⌝)
    | .bool       => iprop(⌜∃ b, v = .bool b⌝)
    | .int        => iprop(⌜∃ n, v = .int n⌝)
    | .value      => iprop(True)
    | .empty      => iprop(False)
    | .arrow _ _  => iprop(False)
    | .tvar _     => iprop(False)
    | .ref t      => iprop(∃ l, ⌜v = .loc l⌝ ∗ locinv l (fun w => R w t))
    | .named T args => k v T args
    | .tuple ts   => iprop(∃ vs, ⌜v = .tuple vs⌝ ∗ ValsRelBody R vs ts k)
    | .sum ts     =>
        iprop(∃ tag payload, ⌜v = .inj tag ts.length payload⌝ ∗
          ValSumRelBody R tag payload ts k)

  def ValsRelBody : ValShape → List Runtime.Val → List Typ → RecCont → iProp
    | _, [], [], _ => iprop(emp)
    | R, v :: vs, t :: ts, k => iprop(ValRelBody R v t k ∗ ValsRelBody R vs ts k)
    | _, _, _, _ => iprop(False)

  def ValSumRelBody : ValShape → Nat → Runtime.Val → List Typ → RecCont → iProp
    | _, _, _, [], _ => iprop(False)
    | R, 0, payload, t :: _, k => ValRelBody R payload t k
    | R, n + 1, payload, _ :: ts, k => ValSumRelBody R n payload ts k
end

/-! Monotonicity in the inner continuation. -/

mutual
  theorem ValRelBody.mono_int (R : ValShape) (t : Typ) (v : Runtime.Val) {k k' : RecCont} :
      ⊢ □ (∀ v T args, k v T args -∗ k' v T args) -∗
        (ValRelBody R v t k -∗ ValRelBody R v t k' : iProp) := by
    unfold ValRelBody
    match t with
    | .named T args =>
        iintro #Hk Hv
        iapply Hk
        iexact Hv
    | .tuple ts =>
        iintro #Hk ⟨%vs, %heq, Hvs⟩
        iexists vs
        isplitr
        · ipure_intro
          exact heq
        · iapply (ValsRelBody.mono_int R ts vs)
          · iexact Hk
          · iexact Hvs
    | .sum ts =>
        iintro #Hk ⟨%tag, %payload, %heq, Hsum⟩
        iexists tag, payload
        isplitr
        · ipure_intro
          exact heq
        · iapply (ValSumRelBody.mono_int R ts tag payload)
          · iexact Hk
          · iexact Hsum
    | .unit | .bool | .int | .value | .empty | .arrow _ _ | .tvar _ | .ref _ =>
        iintro _ H
        iexact H

  theorem ValsRelBody.mono_int (R : ValShape) (ts : List Typ) (vs : List Runtime.Val)
      {k k' : RecCont} :
      ⊢ □ (∀ v T args, k v T args -∗ k' v T args) -∗
        (ValsRelBody R vs ts k -∗ ValsRelBody R vs ts k' : iProp) := by
    unfold ValsRelBody
    match vs, ts with
    | [], [] =>
        iintro _ H
        iexact H
    | v :: vs, t :: ts =>
        iintro #Hk ⟨Hv, Hvs⟩
        isplitl [Hv]
        · iapply (ValRelBody.mono_int R t v)
          · iexact Hk
          · iexact Hv
        · iapply (ValsRelBody.mono_int R ts vs)
          · iexact Hk
          · iexact Hvs
    | [], _ :: _ | _ :: _, [] =>
        iintro _ H
        iexact H

  theorem ValSumRelBody.mono_int (R : ValShape) (ts : List Typ) (tag : Nat)
      (payload : Runtime.Val) {k k' : RecCont} :
      ⊢ □ (∀ v T args, k v T args -∗ k' v T args) -∗
        (ValSumRelBody R tag payload ts k -∗ ValSumRelBody R tag payload ts k' : iProp) := by
    unfold ValSumRelBody
    match tag, ts with
    | _, [] =>
        iintro _ H
        iexact H
    | 0, t :: _ =>
        iintro #Hk Hv
        iapply (ValRelBody.mono_int R t payload)
        · iexact Hk
        · iexact Hv
    | n + 1, _ :: ts =>
        iintro #Hk Hv
        iapply (ValSumRelBody.mono_int R ts n payload)
        · iexact Hk
        · iexact Hv
end

/-! Mixed OFE continuity in the outer approximation and inner continuation. -/

mutual
  theorem ValRelBody.dist {n : Nat} {R S : ValShape} {k k' : RecCont}
      (hR : DistLater n R S) (hk : k ≡{n}≡ k') (t : Typ) (v : Runtime.Val) :
      ValRelBody R v t k ≡{n}≡ ValRelBody S v t k' := by
    unfold ValRelBody
    match t with
    | .ref t =>
        refine exists_ne fun l => ?_
        refine sep_ne.ne (.of_eq rfl) ?_
        apply Contractive.distLater_dist (f := fun I : Runtime.Val → iProp => locinv l I)
        intro m hm w
        exact hR m hm w t
    | .named T args =>
        exact hk v T args
    | .tuple ts =>
        refine exists_ne fun vs => ?_
        refine sep_ne.ne (.of_eq rfl) ?_
        exact ValsRelBody.dist hR hk ts vs
    | .sum ts =>
        refine exists_ne fun tag => ?_
        refine exists_ne fun payload => ?_
        refine sep_ne.ne (.of_eq rfl) ?_
        exact ValSumRelBody.dist hR hk ts tag payload
    | .unit | .bool | .int | .value | .empty | .arrow _ _ | .tvar _ =>
        exact Dist.rfl

  theorem ValsRelBody.dist {n : Nat} {R S : ValShape} {k k' : RecCont}
      (hR : DistLater n R S) (hk : k ≡{n}≡ k') (ts : List Typ) (vs : List Runtime.Val) :
      ValsRelBody R vs ts k ≡{n}≡ ValsRelBody S vs ts k' := by
    unfold ValsRelBody
    match vs, ts with
    | [], [] =>
        exact Dist.rfl
    | v :: vs, t :: ts =>
        refine sep_ne.ne ?_ ?_
        · exact ValRelBody.dist hR hk t v
        · exact ValsRelBody.dist hR hk ts vs
    | [], _ :: _ | _ :: _, [] =>
        exact Dist.rfl

  theorem ValSumRelBody.dist {n : Nat} {R S : ValShape} {k k' : RecCont}
      (hR : DistLater n R S) (hk : k ≡{n}≡ k') (ts : List Typ) (tag : Nat)
      (payload : Runtime.Val) :
      ValSumRelBody R tag payload ts k ≡{n}≡ ValSumRelBody S tag payload ts k' := by
    unfold ValSumRelBody
    match tag, ts with
    | _, [] =>
        exact Dist.rfl
    | 0, t :: _ =>
        exact ValRelBody.dist hR hk t payload
    | n + 1, _ :: ts =>
        exact ValSumRelBody.dist hR hk ts n payload
end

instance ValRelBody.contractive (k : RecCont) (v : Runtime.Val) (t : Typ) :
    Contractive (fun R : ValShape => ValRelBody R v t k) where
  distLater_dist hR := ValRelBody.dist hR Dist.rfl t v

/-- One unfolding of the inner recursive type interpretation. -/
def ValRelIndF (Θ : TypeEnv) (R : ValShape) (Φ : RecIdx → iProp) (x : RecIdx) : iProp :=
  match x with
  | ⟨(v, T, args)⟩ =>
      iprop(∃ ty, ⌜TypeName.unfold Θ T args = some ty⌝ ∗
        ValRelBody R v ty (RecCont.ofPred Φ))

instance (Θ : TypeEnv) (R : ValShape) (Φ : RecIdx → iProp) :
    NonExpansive (ValRelIndF Θ R Φ) where
  ne {_ x y} h := by
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    cases LeibnizO.dist_inj h
    exact Dist.of_eq rfl

theorem ValRelIndF.contractive (Θ : TypeEnv) (Φ : RecIdx → iProp) (x : RecIdx) :
    Contractive (fun R : ValShape => ValRelIndF Θ R Φ x) where
  distLater_dist {n R S} hR := by
    obtain ⟨v, T, args⟩ := x
    simp only [ValRelIndF]
    refine exists_ne fun ty => ?_
    refine sep_ne.ne (.of_eq rfl) ?_
    exact Contractive.distLater_dist
      (f := fun R : ValShape => ValRelBody R v ty (RecCont.ofPred Φ)) hR

instance (Θ : TypeEnv) (R : ValShape) : BIMonoPred (ValRelIndF Θ R) where
  mono_pred := by
    intro Φ Ψ _ _
    iintro #HΦΨ %x HF
    obtain ⟨v, T, args⟩ := x
    simp only [ValRelIndF]
    icases HF with ⟨%ty, %hunfold, Hv⟩
    iexists ty
    isplitr
    · ipure_intro
      exact hunfold
    · iapply (ValRelBody.mono_int R ty v
        (k := RecCont.ofPred Φ) (k' := RecCont.ofPred Ψ))
      · imodintro
        iintro %v' %T' %args'
        iapply HΦΨ
      · iexact Hv
  mono_pred_ne.ne {_ x y} h := by
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    cases LeibnizO.dist_inj h
    exact Dist.of_eq rfl

/-- The inner least fixpoint for named types, with the outer approximation fixed. -/
def ValRelInd (Θ : TypeEnv) (R : ValShape) : RecCont :=
  fun v T args => Iris.bi_least_fixpoint (ValRelIndF Θ R) ⟨(v, T, args)⟩

theorem ValRelInd.unfold {Θ : TypeEnv} {R : ValShape}
    {v : Runtime.Val} {T : TypeName} {args : List Typ} :
    ValRelInd Θ R v T args ⊣⊢
      iprop(∃ ty, ⌜TypeName.unfold Θ T args = some ty⌝ ∗
        ValRelBody R v ty (ValRelInd Θ R)) := by
  have h := Iris.least_fixpoint_unfold (ValRelIndF Θ R) (x := ⟨(v, T, args)⟩)
  simp only [ValRelIndF] at h
  exact equiv_iff.mp h

instance ValRelInd.contractive (Θ : TypeEnv) :
    Contractive (fun R : ValShape => ValRelInd Θ R) where
  distLater_dist {n R S} hR v T args := by
    unfold ValRelInd Iris.bi_least_fixpoint
    refine forall_ne fun Φ => ?_
    refine wand_ne.ne ?_ (.of_eq rfl)
    refine intuitionistically_ne.ne ?_
    refine forall_ne fun x => ?_
    refine wand_ne.ne ?_ (.of_eq rfl)
    exact (ValRelIndF.contractive Θ (fun x => Φ x) x).distLater_dist hR

/-- The outer functional. It closes the named-type continuation using `ValRelInd`. -/
def ValRelF (Θ : TypeEnv) (R : ValShape) : ValShape :=
  fun v t => ValRelBody R v t (ValRelInd Θ R)

instance ValRelF.contractive (Θ : TypeEnv) : Contractive (ValRelF Θ) where
  distLater_dist {n R S} hR v t := by
    unfold ValRelF
    have hk : ValRelInd Θ R ≡{n}≡ ValRelInd Θ S :=
      Contractive.distLater_dist (f := fun R : ValShape => ValRelInd Θ R) hR
    exact ValRelBody.dist hR hk t v

/-- The mixed recursive value relation. -/
def ValHasType (Θ : TypeEnv) : ValShape :=
  fixpoint (ValRelF Θ)

/-- Final tuple/list relation induced by the mixed recursive value relation. -/
def ValsHaveTypes (Θ : TypeEnv) (vs : List Runtime.Val) (ts : List Typ) : iProp :=
  ValsRelBody (ValHasType Θ) vs ts (ValRelInd Θ (ValHasType Θ))

/-- Final sum-payload relation induced by the mixed recursive value relation. -/
def ValSumRel (Θ : TypeEnv) (tag : Nat) (payload : Runtime.Val)
    (ts : List Typ) : iProp :=
  ValSumRelBody (ValHasType Θ) tag payload ts (ValRelInd Θ (ValHasType Θ))

theorem ValHasType.unfold (Θ : TypeEnv) (v : Runtime.Val) (t : Typ) :
    ValHasType Θ v t ≡ ValRelBody (ValHasType Θ) v t (ValRelInd Θ (ValHasType Θ)) := by
  let F : ValShape -c> ValShape := {
    f := ValRelF Θ
    contractive := inferInstance
  }
  exact (fixpoint_unfold F) v t


/-! Persistence of the mixed value relation. -/

mutual
  theorem ValRelBody.persistent (R : ValShape) (t : Typ) (v : Runtime.Val) {k : RecCont}
      (hk : ∀ v T args, Persistent (k v T args)) : Persistent (ValRelBody R v t k) := by
    unfold ValRelBody
    match t with
    | .unit | .bool | .int | .value | .empty | .arrow _ _ | .tvar _ =>
        infer_instance
    | .ref _ =>
        have := locinv_persistent
        infer_instance
    | .named T args =>
        exact hk v T args
    | .tuple ts =>
        have : ∀ vs, Persistent (ValsRelBody R vs ts k) :=
          fun vs => ValsRelBody.persistent R ts vs hk
        infer_instance
    | .sum ts =>
        have : ∀ n payload, Persistent (ValSumRelBody R n payload ts k) :=
          fun n payload => ValSumRelBody.persistent R ts n payload hk
        infer_instance

  theorem ValsRelBody.persistent (R : ValShape) (ts : List Typ) (vs : List Runtime.Val)
      {k : RecCont} (hk : ∀ v T args, Persistent (k v T args)) :
      Persistent (ValsRelBody R vs ts k) := by
    unfold ValsRelBody
    match vs, ts with
    | [], [] =>
        infer_instance
    | v :: vs, t :: ts =>
        have := ValRelBody.persistent R t v hk
        have := ValsRelBody.persistent R ts vs hk
        infer_instance
    | [], _ :: _ | _ :: _, [] =>
        infer_instance

  theorem ValSumRelBody.persistent (R : ValShape) (ts : List Typ) (n : Nat)
      (payload : Runtime.Val) {k : RecCont} (hk : ∀ v T args, Persistent (k v T args)) :
      Persistent (ValSumRelBody R n payload ts k) := by
    unfold ValSumRelBody
    match n, ts with
    | _, [] =>
        infer_instance
    | 0, t :: _ =>
        exact ValRelBody.persistent R t payload hk
    | n + 1, _ :: ts =>
        exact ValSumRelBody.persistent R ts n payload hk
end

instance ValRelIndF.persistent (Θ : TypeEnv) (R : ValShape) (Φ : RecIdx → iProp)
    [∀ x, Persistent (Φ x)] (x : RecIdx) : Persistent (ValRelIndF Θ R Φ x) := by
  obtain ⟨v, T, args⟩ := x
  simp only [ValRelIndF]
  have : ∀ ty, Persistent (ValRelBody R v ty (RecCont.ofPred Φ)) :=
    fun ty => ValRelBody.persistent R ty v (fun _ _ _ => inferInstance)
  infer_instance

instance ValRelIndF.absorbing (Θ : TypeEnv) (R : ValShape) (Φ : RecIdx → iProp)
    [∀ x, Absorbing (Φ x)] (x : RecIdx) : Absorbing (ValRelIndF Θ R Φ x) := by
  obtain ⟨v, T, args⟩ := x
  simp only [ValRelIndF]
  infer_instance

instance (Θ : TypeEnv) (R : ValShape) (v : Runtime.Val) (T : TypeName)
    (args : List Typ) : Persistent (ValRelInd Θ R v T args) :=
  @Iris.least_fixpoint_persistent_absorbing iProp RecIdx _ _ (ValRelIndF Θ R) _
    (fun _ _ _ => inferInstance) (fun _ _ _ => inferInstance) ⟨(v, T, args)⟩

instance (Θ : TypeEnv) (v : Runtime.Val) (t : Typ) : Persistent (ValHasType Θ v t) :=
  (persistent_congr (equiv_iff.mp (ValHasType.unfold Θ v t))).mpr
    (ValRelBody.persistent (ValHasType Θ) t v (fun _ _ _ => inferInstance))

instance (Θ : TypeEnv) (vs : List Runtime.Val) (ts : List Typ) :
    Persistent (ValsHaveTypes Θ vs ts) :=
  ValsRelBody.persistent (ValHasType Θ) ts vs (fun _ _ _ => inferInstance)

instance (Θ : TypeEnv) (tag : Nat) (payload : Runtime.Val) (ts : List Typ) :
    Persistent (ValSumRel Θ tag payload ts) :=
  ValSumRelBody.persistent (ValHasType Θ) ts tag payload (fun _ _ _ => inferInstance)


/-! Per-type unfoldings -/

theorem ValHasType.unit (Θ : TypeEnv) (v : Runtime.Val) :
    ValHasType Θ v .unit ⊣⊢ iprop(⌜v = .unit⌝) := by
  exact equiv_iff.mp (ValHasType.unfold Θ v .unit)

theorem ValHasType.bool (Θ : TypeEnv) (v : Runtime.Val) :
    ValHasType Θ v .bool ⊣⊢ iprop(⌜∃ b, v = .bool b⌝) := by
  exact equiv_iff.mp (ValHasType.unfold Θ v .bool)

theorem ValHasType.int (Θ : TypeEnv) (v : Runtime.Val) :
    ValHasType Θ v .int ⊣⊢ iprop(⌜∃ n, v = .int n⌝) := by
  exact equiv_iff.mp (ValHasType.unfold Θ v .int)

theorem ValHasType.value (Θ : TypeEnv) (v : Runtime.Val) :
    ValHasType Θ v .value ⊣⊢ iprop(True) := by
  exact equiv_iff.mp (ValHasType.unfold Θ v .value)

theorem ValHasType.empty (Θ : TypeEnv) (v : Runtime.Val) :
    ValHasType Θ v .empty ⊣⊢ iprop(False) := by
  exact equiv_iff.mp (ValHasType.unfold Θ v .empty)

theorem ValHasType.arrow (Θ : TypeEnv) (v : Runtime.Val) (t1 t2 : Typ) :
    ValHasType Θ v (.arrow t1 t2) ⊣⊢ iprop(False) := by
  exact equiv_iff.mp (ValHasType.unfold Θ v (.arrow t1 t2))

theorem ValHasType.tvar (Θ : TypeEnv) (v : Runtime.Val) (x : TyVar) :
    ValHasType Θ v (.tvar x) ⊣⊢ iprop(False) := by
  exact equiv_iff.mp (ValHasType.unfold Θ v (.tvar x))

theorem ValHasType.ref (Θ : TypeEnv) (v : Runtime.Val) (t : Typ) :
    ValHasType Θ v (.ref t) ⊣⊢
      iprop(∃ l, ⌜v = .loc l⌝ ∗ locinv l (fun w => ValHasType Θ w t)) := by
  exact equiv_iff.mp (ValHasType.unfold Θ v (.ref t))

theorem ValHasType.tuple (Θ : TypeEnv) (v : Runtime.Val) (ts : List Typ) :
    ValHasType Θ v (.tuple ts) ⊣⊢
      iprop(∃ vs, ⌜v = .tuple vs⌝ ∗ ValsHaveTypes Θ vs ts) := by
  exact equiv_iff.mp (ValHasType.unfold Θ v (.tuple ts))

theorem ValHasType.sum (Θ : TypeEnv) (v : Runtime.Val) (ts : List Typ) :
    ValHasType Θ v (.sum ts) ⊣⊢
      iprop(∃ tag payload, ⌜v = .inj tag ts.length payload⌝ ∗
        ValSumRel Θ tag payload ts) := by
  exact equiv_iff.mp (ValHasType.unfold Θ v (.sum ts))

theorem ValHasType.named (Θ : TypeEnv) (v : Runtime.Val) (T : TypeName) (args : List Typ) :
    ValHasType Θ v (.named T args) ⊣⊢
      iprop(∃ ty, ⌜TypeName.unfold Θ T args = some ty⌝ ∗ ValHasType Θ v ty) := by
  refine (equiv_iff.mp (ValHasType.unfold Θ v (.named T args))).trans ?_
  refine ValRelInd.unfold.trans ?_
  apply equiv_iff.mp
  refine equiv_dist.mpr fun _ => ?_
  refine exists_ne fun ty => ?_
  refine sep_ne.ne (.of_eq rfl) ?_
  exact (ValHasType.unfold Θ v ty).symm.dist

theorem ValHasType.named_of_unfold {Θ : TypeEnv} {v : Runtime.Val}
    {T : TypeName} {args : List Typ} {ty : Typ}
    (hunfold : TypeName.unfold Θ T args = some ty) :
    ValHasType Θ v (.named T args) ⊣⊢ ValHasType Θ v ty := by
  refine (ValHasType.named Θ v T args).trans ?_
  constructor
  · iintro H
    icases H with ⟨%ty', %hunfold', Hty⟩
    rw [hunfold] at hunfold'
    cases hunfold'
    iexact Hty
  · iintro Hty
    iexists ty
    isplitr
    · ipure_intro
      exact hunfold
    · iexact Hty

theorem ValsHaveTypes.nil (Θ : TypeEnv) :
    ValsHaveTypes Θ [] [] ⊣⊢ iprop(emp) := by
  unfold ValsHaveTypes ValsRelBody
  exact .rfl

theorem ValsHaveTypes.cons (Θ : TypeEnv) (v : Runtime.Val) (vs : List Runtime.Val)
    (t : Typ) (ts : List Typ) :
    ValsHaveTypes Θ (v :: vs) (t :: ts) ⊣⊢ ValHasType Θ v t ∗ ValsHaveTypes Θ vs ts := by
  unfold ValsHaveTypes
  change iprop(ValRelBody (ValHasType Θ) v t (ValRelInd Θ (ValHasType Θ)) ∗
      ValsRelBody (ValHasType Θ) vs ts (ValRelInd Θ (ValHasType Θ))) ⊣⊢
    iprop(ValHasType Θ v t ∗ ValsRelBody (ValHasType Θ) vs ts (ValRelInd Θ (ValHasType Θ)))
  exact sep_congr (equiv_iff.mp (ValHasType.unfold Θ v t).symm) .rfl

theorem ValsHaveTypes.nil_cons (Θ : TypeEnv) (t : Typ) (ts : List Typ) :
    ValsHaveTypes Θ [] (t :: ts) ⊣⊢ iprop(False) := by
  unfold ValsHaveTypes ValsRelBody
  exact .rfl

theorem ValsHaveTypes.cons_nil (Θ : TypeEnv) (v : Runtime.Val) (vs : List Runtime.Val) :
    ValsHaveTypes Θ (v :: vs) [] ⊣⊢ iprop(False) := by
  unfold ValsHaveTypes ValsRelBody
  exact .rfl

theorem ValSumRel.nil (Θ : TypeEnv) (tag : Nat) (payload : Runtime.Val) :
    ValSumRel Θ tag payload [] ⊣⊢ iprop(False) := by
  unfold ValSumRel ValSumRelBody
  exact .rfl

theorem ValSumRel.zero (Θ : TypeEnv) (payload : Runtime.Val) (t : Typ) (ts : List Typ) :
    ValSumRel Θ 0 payload (t :: ts) ⊣⊢ ValHasType Θ payload t := by
  unfold ValSumRel ValSumRelBody
  exact equiv_iff.mp (ValHasType.unfold Θ payload t).symm

theorem ValSumRel.succ (Θ : TypeEnv) (tag : Nat) (payload : Runtime.Val)
    (t : Typ) (ts : List Typ) :
    ValSumRel Θ (tag + 1) payload (t :: ts) ⊣⊢ ValSumRel Θ tag payload ts := by
  unfold ValSumRel
  change ValSumRelBody (ValHasType Θ) tag payload ts (ValRelInd Θ (ValHasType Θ)) ⊣⊢
    ValSumRelBody (ValHasType Θ) tag payload ts (ValRelInd Θ (ValHasType Θ))
  exact .rfl

/-! Indexing and subtyping compatibility. -/

/-- `ValSumRel Θ tag payload ts` is the value relation at `ts[tag]`, when that
index exists. -/
theorem ValSumRel.of_getElem? {Θ : TypeEnv} {payload : Runtime.Val} :
    ∀ {ts : List Typ} {tag : Nat} {s : Typ}, ts[tag]? = some s →
      ValSumRel Θ tag payload ts ⊢ ValHasType Θ payload s
  | [], _, _, h => by
      simp at h
  | _ :: _, 0, _, h => by
      simp at h
      subst h
      exact (ValSumRel.zero Θ payload _ _).1
  | _ :: ts, n + 1, _, h => by
      exact (ValSumRel.succ Θ n payload _ ts).1.trans
        (ValSumRel.of_getElem? (Θ := Θ) (payload := payload) (ts := ts) (by simpa using h))

theorem ValSumRel.to_getElem? {Θ : TypeEnv} {payload : Runtime.Val} :
    ∀ {ts : List Typ} {tag : Nat} {s : Typ}, ts[tag]? = some s →
      ValHasType Θ payload s ⊢ ValSumRel Θ tag payload ts
  | [], _, _, h => by
      simp at h
  | _ :: _, 0, _, h => by
      simp at h
      subst h
      exact (ValSumRel.zero Θ payload _ _).2
  | _ :: ts, n + 1, _, h => by
      exact (ValSumRel.to_getElem? (Θ := Θ) (payload := payload) (ts := ts) (by simpa using h)).trans
        (ValSumRel.succ Θ n payload _ ts).2

/-- `ValSumRel` implies the tag is in range. -/
theorem ValSumRel.bound {Θ : TypeEnv} {payload : Runtime.Val} :
    ∀ {ts : List Typ} {tag : Nat},
      ValSumRel Θ tag payload ts ⊢ iprop(⌜tag < ts.length⌝)
  | [], tag => (ValSumRel.nil Θ tag payload).1.trans false_elim
  | _ :: _, 0 => true_intro.trans <| pure_intro (by simp)
  | _ :: ts, tag + 1 =>
      (ValSumRel.succ Θ tag payload _ ts).1.trans <|
        (ValSumRel.bound (Θ := Θ) (payload := payload) (ts := ts) (tag := tag)).trans <|
        pure_mono (by simp)

/-- Inject a typed payload at tag `tag` into a sum type whose `tag`-th component matches. -/
theorem ValHasType.inj {Θ : TypeEnv} {payload : Runtime.Val}
    {tag arity : Nat} {ts : List Typ} {s : Typ}
    (hlen : ts.length = arity) (hget : ts[tag]? = some s) :
    ValHasType Θ payload s ⊢ ValHasType Θ (.inj tag arity payload) (.sum ts) := by
  refine Entails.trans ?_ (ValHasType.sum Θ (.inj tag arity payload) ts).2
  iintro Hpayload
  iexists tag, payload
  isplitr
  · ipure_intro; simp [hlen]
  · iapply (ValSumRel.to_getElem? (Θ := Θ) (payload := payload) (ts := ts)
      (tag := tag) (s := s) hget)
    iexact Hpayload

/-- The canonical proof that `unit` has type `unit`. -/
theorem ValHasType.unit_intro (Θ : TypeEnv) :
    ⊢ ValHasType Θ .unit .unit := by
  iapply (ValHasType.unit Θ .unit).2
  ipure_intro; rfl

mutual
  theorem ValHasType.sub {Θ : TypeEnv} {v : Runtime.Val} {t t' : Typ}
      (hsub : Typ.Sub Θ t t') :
      ValHasType Θ v t ⊢ ValHasType Θ v t' := by
    match hsub with
    | .refl =>
        exact .rfl
    | .bot =>
        exact (ValHasType.empty Θ v).1.trans false_elim
    | .top =>
        exact true_intro.trans (ValHasType.value Θ v).2
    | .trans h1 h2 =>
        exact (ValHasType.sub h1).trans (ValHasType.sub h2)
    | .sum hlist =>
        have hlen := hlist.length_eq
        refine (ValHasType.sum Θ v _).1.trans ?_
        refine .trans ?_ (ValHasType.sum Θ v _).2
        iintro H
        icases H with ⟨%tag, %payload, %heq, Hsum⟩
        iexists tag, payload
        isplitr
        · ipure_intro
          rw [heq, hlen]
        · iapply (ValSumRel.sub hlist payload tag)
          iexact Hsum
    | .arrow _ _ =>
        exact (ValHasType.arrow Θ v _ _).1.trans false_elim
    | .tuple hlist =>
        refine (ValHasType.tuple Θ v _).1.trans ?_
        refine .trans ?_ (ValHasType.tuple Θ v _).2
        iintro H
        icases H with ⟨%vs, %heq, Hvs⟩
        iexists vs
        isplitr
        · ipure_intro
          exact heq
        · iapply (ValsHaveTypes.sub (vs := vs) hlist)
          iexact Hvs
    | .named_left hunfold hsub' =>
        exact (ValHasType.named_of_unfold (v := v) hunfold).1.trans (ValHasType.sub hsub')
    | .named_right hunfold hsub' =>
        exact (ValHasType.sub hsub').trans (ValHasType.named_of_unfold (v := v) hunfold).2

  theorem ValsHaveTypes.sub {Θ : TypeEnv} {vs : List Runtime.Val} {ts ts' : List Typ}
      (hsub : Typ.SubList Θ ts ts') :
      ValsHaveTypes Θ vs ts ⊢ ValsHaveTypes Θ vs ts' := by
    match hsub, vs with
    | .nil, _ =>
        exact .rfl
    | .cons (s := s) (ss := ss) _ _, [] =>
        exact (ValsHaveTypes.nil_cons Θ s ss).1.trans false_elim
    | .cons (s := s) (t := t) (ss := ss) (ts := ts) hst hrest, v :: vs =>
        refine (ValsHaveTypes.cons Θ v vs s ss).1.trans ?_
        refine .trans ?_ (ValsHaveTypes.cons Θ v vs t ts).2
        exact sep_mono (ValHasType.sub hst) (ValsHaveTypes.sub (vs := vs) hrest)

  theorem ValSumRel.sub {Θ : TypeEnv} {ss ts : List Typ}
      (hsub : Typ.SubList Θ ss ts) (payload : Runtime.Val) (tag : Nat) :
      ValSumRel Θ tag payload ss ⊢ ValSumRel Θ tag payload ts := by
    match hsub, tag with
    | .nil, _ =>
        exact .rfl
    | .cons (s := s) (t := t) (ss := ss) (ts := ts) hst _, 0 =>
        exact (ValSumRel.zero Θ payload s ss).1.trans
          ((ValHasType.sub hst).trans (ValSumRel.zero Θ payload t ts).2)
    | .cons (s := s) (t := t) (ss := ss) (ts := ts) _ hrest, n + 1 =>
        exact (ValSumRel.succ Θ n payload s ss).1.trans
          ((ValSumRel.sub hrest payload n).trans (ValSumRel.succ Θ n payload t ts).2)

  theorem ValHasType.subList {Θ : TypeEnv} {payload : Runtime.Val} {s : Typ}
      {ss ts : List Typ} (hsub : Typ.SubList Θ ss ts) {tag : Nat}
      (hs : ss[tag]? = some s) :
      ValHasType Θ payload s ⊢
        iprop(∃ t, ⌜ts[tag]? = some t⌝ ∗ ValHasType Θ payload t) := by
    match hsub, tag, hs with
    | .nil, _, h =>
        simp at h
    | .cons (t := t') hst _, 0, h =>
        simp at h
        subst h
        iintro Hv
        iexists t'
        isplitr
        · ipure_intro
          simp
        · iapply (ValHasType.sub hst)
          iexact Hv
    | .cons (ss := ss') _ hrest, n + 1, h =>
        have h' : ss'[n]? = some s := by
          simpa using h
        refine (ValHasType.subList hrest h').trans ?_
        iintro H
        icases H with ⟨%t, %hget, Ht⟩
        iexists t
        isplitr
        · ipure_intro
          simpa using hget
        · iexact Ht
end

/-- Length agreement for `ValsHaveTypes`, as an entailment. -/
theorem ValsHaveTypes.length_eq {Θ : TypeEnv} {vs : List Runtime.Val} {ts : List Typ} :
    ValsHaveTypes Θ vs ts ⊢ iprop(⌜vs.length = ts.length⌝) := by
  match vs, ts with
  | [], [] =>
      exact (ValsHaveTypes.nil Θ).1.trans (pure_intro rfl)
  | v :: vs, t :: ts =>
      exact ((ValsHaveTypes.cons Θ v vs t ts).1.trans sep_elim_r).trans
        ((ValsHaveTypes.length_eq (Θ := Θ) (vs := vs) (ts := ts)).trans
          (pure_mono (fun h => by simp [h])))
  | [], t :: ts =>
      exact (ValsHaveTypes.nil_cons Θ t ts).1.trans false_elim
  | v :: vs, [] =>
      exact (ValsHaveTypes.cons_nil Θ v vs).1.trans false_elim

/-- If `ts[n]? = some t`, then a related list of values contains a value at
index `n` related at type `t`. -/
theorem ValsHaveTypes.of_getElem? {Θ : TypeEnv} :
    ∀ {vs : List Runtime.Val} {ts : List Typ} {n : Nat} {t : Typ},
      ts[n]? = some t →
      ValsHaveTypes Θ vs ts ⊢ iprop(∃ v, ⌜vs[n]? = some v⌝ ∗ ValHasType Θ v t)
  | [], [], _, _, h => by
      simp at h
  | [], t :: ts, _, _, _ => by
      exact (ValsHaveTypes.nil_cons Θ t ts).1.trans false_elim
  | v :: vs, [], _, _, _ => by
      exact (ValsHaveTypes.cons_nil Θ v vs).1.trans false_elim
  | v :: vs, t :: ts, 0, t', h => by
      simp at h
      subst h
      refine (ValsHaveTypes.cons Θ v vs t ts).1.trans ?_
      iintro H
      icases H with ⟨Hv, _⟩
      iexists v
      isplitr
      · ipure_intro
        simp
      · iexact Hv
  | v :: vs, t :: ts, n + 1, t', h => by
      have h' : ts[n]? = some t' := by
        simpa using h
      refine (ValsHaveTypes.cons Θ v vs t ts).1.trans ?_
      iintro H
      icases H with ⟨_, Hvs⟩
      iapply
        (show iprop(∃ w, ⌜vs[n]? = some w⌝ ∗ ValHasType Θ w t') ⊢
            iprop(∃ w, ⌜(v :: vs)[n + 1]? = some w⌝ ∗ ValHasType Θ w t') by
          iintro H'
          icases H' with ⟨%w, %hget, Hwitness⟩
          iexists w
          isplitr
          · ipure_intro
            simpa using hget
          · iexact Hwitness)
      iapply (ValsHaveTypes.of_getElem? (Θ := Θ) (vs := vs) (ts := ts) (n := n) (t := t') h')
      iexact Hvs


/-! Type preservation for primitive operations. -/

theorem evalBinOp_typed {Θ : TypeEnv} {op : BinOp}
    {v1 v2 : Runtime.Val} {t1 t2 ty : Typ}
    (hndiv : op ≠ .div) (hnmod : op ≠ .mod)
    (hty : BinOp.typeOf op t1 t2 = some ty) :
    iprop(ValHasType Θ v1 t1 ∗ ValHasType Θ v2 t2) ⊢
      iprop(∃ w, ⌜evalBinOp op v1 v2 = some w⌝ ∗ ValHasType Θ w ty) := by
  cases op with
  | add =>
      cases t1 <;> cases t2 <;> simp [BinOp.typeOf] at hty
      subst hty
      refine (sep_mono (ValHasType.int Θ v1).1 (ValHasType.int Θ v2).1).trans ?_
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1
      subst v2
      iexists Runtime.Val.int (a + b)
      isplitr
      · ipure_intro
        simp [evalBinOp]
      · iapply (ValHasType.int Θ (Runtime.Val.int (a + b))).2
        ipure_intro
        exact ⟨a + b, rfl⟩
  | sub =>
      cases t1 <;> cases t2 <;> simp [BinOp.typeOf] at hty
      subst hty
      refine (sep_mono (ValHasType.int Θ v1).1 (ValHasType.int Θ v2).1).trans ?_
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1
      subst v2
      iexists Runtime.Val.int (a - b)
      isplitr
      · ipure_intro
        simp [evalBinOp]
      · iapply (ValHasType.int Θ (Runtime.Val.int (a - b))).2
        ipure_intro
        exact ⟨a - b, rfl⟩
  | mul =>
      cases t1 <;> cases t2 <;> simp [BinOp.typeOf] at hty
      subst hty
      refine (sep_mono (ValHasType.int Θ v1).1 (ValHasType.int Θ v2).1).trans ?_
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1
      subst v2
      iexists Runtime.Val.int (a * b)
      isplitr
      · ipure_intro
        simp [evalBinOp]
      · iapply (ValHasType.int Θ (Runtime.Val.int (a * b))).2
        ipure_intro
        exact ⟨a * b, rfl⟩
  | div =>
      cases (hndiv rfl)
  | mod =>
      cases (hnmod rfl)
  | eq =>
      cases t1 <;> cases t2 <;> simp [BinOp.typeOf] at hty
      subst hty
      refine (sep_mono (ValHasType.int Θ v1).1 (ValHasType.int Θ v2).1).trans ?_
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1
      subst v2
      iexists Runtime.Val.bool (a == b)
      isplitr
      · ipure_intro
        simp [evalBinOp]
      · iapply (ValHasType.bool Θ (Runtime.Val.bool (a == b))).2
        ipure_intro
        exact ⟨a == b, rfl⟩
  | lt =>
      cases t1 <;> cases t2 <;> simp [BinOp.typeOf] at hty
      subst hty
      refine (sep_mono (ValHasType.int Θ v1).1 (ValHasType.int Θ v2).1).trans ?_
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1
      subst v2
      iexists Runtime.Val.bool (a < b)
      isplitr
      · ipure_intro
        simp [evalBinOp]
      · iapply (ValHasType.bool Θ (Runtime.Val.bool (a < b))).2
        ipure_intro
        exact ⟨a < b, rfl⟩
  | le =>
      cases t1 <;> cases t2 <;> simp [BinOp.typeOf] at hty
      subst hty
      refine (sep_mono (ValHasType.int Θ v1).1 (ValHasType.int Θ v2).1).trans ?_
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1
      subst v2
      iexists Runtime.Val.bool (a ≤ b)
      isplitr
      · ipure_intro
        simp [evalBinOp]
      · iapply (ValHasType.bool Θ (Runtime.Val.bool (a ≤ b))).2
        ipure_intro
        exact ⟨a ≤ b, rfl⟩
  | gt =>
      cases t1 <;> cases t2 <;> simp [BinOp.typeOf] at hty
      subst hty
      refine (sep_mono (ValHasType.int Θ v1).1 (ValHasType.int Θ v2).1).trans ?_
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1
      subst v2
      iexists Runtime.Val.bool (a > b)
      isplitr
      · ipure_intro
        simp [evalBinOp]
      · iapply (ValHasType.bool Θ (Runtime.Val.bool (a > b))).2
        ipure_intro
        exact ⟨a > b, rfl⟩
  | ge =>
      cases t1 <;> cases t2 <;> simp [BinOp.typeOf] at hty
      subst hty
      refine (sep_mono (ValHasType.int Θ v1).1 (ValHasType.int Θ v2).1).trans ?_
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1
      subst v2
      iexists Runtime.Val.bool (a ≥ b)
      isplitr
      · ipure_intro
        simp [evalBinOp]
      · iapply (ValHasType.bool Θ (Runtime.Val.bool (a ≥ b))).2
        ipure_intro
        exact ⟨a ≥ b, rfl⟩
  | and =>
      cases t1 <;> cases t2 <;> simp [BinOp.typeOf] at hty
      subst hty
      refine (sep_mono (ValHasType.bool Θ v1).1 (ValHasType.bool Θ v2).1).trans ?_
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1
      subst v2
      iexists Runtime.Val.bool (a && b)
      isplitr
      · ipure_intro
        simp [evalBinOp]
      · iapply (ValHasType.bool Θ (Runtime.Val.bool (a && b))).2
        ipure_intro
        exact ⟨a && b, rfl⟩
  | or =>
      cases t1 <;> cases t2 <;> simp [BinOp.typeOf] at hty
      subst hty
      refine (sep_mono (ValHasType.bool Θ v1).1 (ValHasType.bool Θ v2).1).trans ?_
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1
      subst v2
      iexists Runtime.Val.bool (a || b)
      isplitr
      · ipure_intro
        simp [evalBinOp]
      · iapply (ValHasType.bool Θ (Runtime.Val.bool (a || b))).2
        ipure_intro
        exact ⟨a || b, rfl⟩

theorem evalUnOp_typed {Θ : TypeEnv} {op : UnOp}
    {v : Runtime.Val} {t ty : Typ}
    (hty : UnOp.typeOf op t = some ty) :
    ValHasType Θ v t ⊢
      iprop(∃ w, ⌜evalUnOp op v = some w⌝ ∗ ValHasType Θ w ty) := by
  cases op with
  | neg =>
      cases t <;> simp [UnOp.typeOf] at hty
      subst hty
      refine (ValHasType.int Θ v).1.trans ?_
      iintro Hv
      icases Hv with ⟨%n, %hv⟩
      subst v
      iexists Runtime.Val.int (-n)
      isplitr
      · ipure_intro
        simp [evalUnOp]
      · iapply (ValHasType.int Θ (Runtime.Val.int (-n))).2
        ipure_intro
        exact ⟨-n, rfl⟩
  | not =>
      cases t <;> simp [UnOp.typeOf] at hty
      subst hty
      refine (ValHasType.bool Θ v).1.trans ?_
      iintro Hv
      icases Hv with ⟨%b, %hv⟩
      subst v
      iexists Runtime.Val.bool (!b)
      isplitr
      · ipure_intro
        simp [evalUnOp]
      · iapply (ValHasType.bool Θ (Runtime.Val.bool (!b))).2
        ipure_intro
        exact ⟨!b, rfl⟩
  | proj n =>
      cases t with
      | tuple ts =>
          simp [UnOp.typeOf] at hty
          refine (ValHasType.tuple Θ v ts).1.trans ?_
          iintro H
          icases H with ⟨%vs, %hv, Hvs⟩
          subst v
          iapply
            (show iprop(∃ w, ⌜vs[n]? = some w⌝ ∗ ValHasType Θ w ty) ⊢
                iprop(∃ w, ⌜evalUnOp (.proj n) (.tuple vs) = some w⌝ ∗ ValHasType Θ w ty) by
              iintro H'
              icases H' with ⟨%w, %hget, Hwitness⟩
              iexists w
              isplitr
              · ipure_intro
                simpa [evalUnOp] using hget
              · iexact Hwitness)
          iapply (ValsHaveTypes.of_getElem? (Θ := Θ) (vs := vs) (ts := ts) (n := n) (t := ty) hty)
          iexact Hvs
      | unit | bool | int | sum _ | arrow _ _ | ref _ | empty | value | tvar _ | named _ _ =>
          simp [UnOp.typeOf] at hty

end TinyML


-- ---------------------------------------------------------------------------
-- Type constraints
-- ---------------------------------------------------------------------------

mutual
/-- Generate SMT formulas asserting that a value-sorted term has a given TinyML type.
    For `int`: `is-of_int(t)`, for `bool`: `is-of_bool(t)`,
    for `tuple ts`: `is-of_tuple(t)` plus recursive constraints on elements. -/
def typeConstraints (ty : TinyML.Typ) (t : Term .value) : List Formula :=
  match ty with
  | .int   => [.unpred .isInt t]
  | .bool  => [.unpred .isBool t]
  | .tuple ts =>
      .unpred .isTuple t ::
      typeConstraintsList ts (.unop .toValList t)
  | _ => []

def typeConstraintsList (ts : List TinyML.Typ) (tl : Term .vallist) : List Formula :=
    match ts with
    | [] => []
    | ty :: rest =>
        typeConstraints ty (.unop .vhead tl) ++
        typeConstraintsList rest (.unop .vtail tl)
end


mutual
  /-- All formulas in `typeConstraints ty t` only reference free variables of `t`. -/
  theorem typeConstraints_wfIn {ty : TinyML.Typ} {t : Term .value} {Δ : Signature}
      (ht : t.wfIn Δ) : ∀ φ ∈ typeConstraints ty t, φ.wfIn Δ := by
    cases ty with
    | int =>
      simp [typeConstraints]
      simp only [Formula.wfIn]; exact ht
    | bool =>
      simp [typeConstraints]
      simp only [Formula.wfIn]; exact ht
    | tuple ts =>
      simp only [typeConstraints]
      intro φ hφ
      cases hφ with
      | head =>
        simp only [Formula.wfIn]; exact ht
      | tail _ hφ =>
        exact typeConstraintsList_wfIn (by simp only [Term.wfIn]; exact ⟨trivial, ht⟩) φ hφ
    | _ => simp [typeConstraints]

  theorem typeConstraintsList_wfIn {ts : List TinyML.Typ} {tl : Term .vallist} {Δ : Signature}
      (htl : tl.wfIn Δ) : ∀ φ ∈ typeConstraintsList ts tl, φ.wfIn Δ := by
    cases ts with
    | nil => simp [typeConstraintsList]
    | cons ty rest =>
      simp only [typeConstraintsList]
      intro φ hφ
      cases List.mem_append.mp hφ with
      | inl h =>
        exact typeConstraints_wfIn (by simp only [Term.wfIn]; exact ⟨trivial, htl⟩) φ h
      | inr h =>
        exact typeConstraintsList_wfIn (by simp only [Term.wfIn]; exact ⟨trivial, htl⟩) φ h
end

mutual
  /-- If `ValHasType v ty` and `t.eval ρ = v`, then all formulas in `typeConstraints ty t` hold. -/
  theorem typeConstraints_hold {ty : TinyML.Typ} {t : Term .value} {ρ : Env}
      {Θ : TinyML.TypeEnv} {v : Runtime.Val} (ht : t.eval ρ = v) :
      TinyML.ValHasType Θ v ty ⊢ ⌜∀ φ ∈ typeConstraints ty t, φ.eval ρ⌝ := by
    cases ty with
    | int =>
      refine (TinyML.ValHasType.int Θ v).1.trans ?_
      iintro %h
      rcases h with ⟨n, rfl⟩
      ipure_intro
      intro φ hφ
      simp [typeConstraints] at hφ
      subst hφ
      simp [Formula.eval, ht]
    | bool =>
      refine (TinyML.ValHasType.bool Θ v).1.trans ?_
      iintro %h
      rcases h with ⟨b, rfl⟩
      ipure_intro
      intro φ hφ
      simp [typeConstraints] at hφ
      subst hφ
      simp [Formula.eval, ht]
    | tuple ts =>
      refine (TinyML.ValHasType.tuple Θ v ts).1.trans ?_
      iintro Hty
      icases Hty with ⟨%vs, Hty'⟩
      icases Hty' with ⟨%hv, hvs⟩
      ihave %htail := (typeConstraintsList_hold (ts := ts) (tl := .unop .toValList t)
        (ρ := ρ) (Θ := Θ) (vs := vs) (by simp [Term.eval, UnOp.eval, ht, hv])) $$ hvs
      iclear hvs
      ipure_intro
      intro φ hφ
      cases hφ with
      | head =>
        simp [Formula.eval, ht, hv]
      | tail _ hφ =>
        exact htail φ hφ
    | unit | sum _ | ref _ | value | named _ _ =>
      iintro _; ipure_intro; simp [typeConstraints]
    | arrow t1 t2 => exact (TinyML.ValHasType.arrow Θ v t1 t2).1.trans false_elim
    | empty => exact (TinyML.ValHasType.empty Θ v).1.trans false_elim
    | tvar x => exact (TinyML.ValHasType.tvar Θ v x).1.trans false_elim

  theorem typeConstraintsList_hold {ts : List TinyML.Typ} {tl : Term .vallist} {ρ : Env}
      {Θ : TinyML.TypeEnv} {vs : List Runtime.Val} (htl : tl.eval ρ = vs) :
      TinyML.ValsHaveTypes Θ vs ts ⊢ ⌜∀ φ ∈ typeConstraintsList ts tl, φ.eval ρ⌝ := by
    match vs, ts with
    | [], [] =>
        refine (TinyML.ValsHaveTypes.nil Θ).1.trans ?_
        iintro _
        ipure_intro
        simp [typeConstraintsList]
    | v :: vs, ty :: ts =>
        refine (TinyML.ValsHaveTypes.cons Θ v vs ty ts).1.trans ?_
        iintro hvals
        icases hvals with ⟨hv, hvs⟩
        ihave %hhead := (typeConstraints_hold (ty := ty) (t := .unop .vhead tl)
          (ρ := ρ) (Θ := Θ) (v := v) (by simp [Term.eval, UnOp.eval, htl])) $$ hv
        ihave %htail := (typeConstraintsList_hold (ts := ts) (tl := .unop .vtail tl)
          (ρ := ρ) (Θ := Θ) (vs := vs) (by simp [Term.eval, UnOp.eval, htl])) $$ hvs
        iclear hv hvs
        ipure_intro
        intro φ hφ
        cases List.mem_append.mp hφ with
        | inl h => exact hhead φ h
        | inr h => exact htail φ h
    | [], ty :: ts =>
        exact (TinyML.ValsHaveTypes.nil_cons Θ ty ts).1.trans false_elim
    | v :: vs, [] =>
        exact (TinyML.ValsHaveTypes.cons_nil Θ v vs).1.trans false_elim
end
