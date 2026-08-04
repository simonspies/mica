-- SUMMARY: Iris logical relations for TinyML values and types, together with soundness proofs for type constraints.
import Mica.TinyML.Common
import Mica.SourceTinyML.Types
import Mica.SourceTinyML.TypeConstraints
import Mica.TinyML.RuntimeExpr
import Mica.TinyML.OpSem
import Mica.FOL.Formulas
import Mica.Base.Fresh
import Mica.SeparationLogic.Wp
import Mica.SourceTinyML.World
import Mica.SourceTinyML.Semantics
import Iris.BI.Lib.Fixpoint

open Iris Iris.BI Iris.OFE

variable [MicaGS HasLC.hasLC Sig]

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

/-- Interpret one primitive type as an Iris assertion over a runtime value. -/
def PrimitiveType.valRelBody : PrimitiveType → Runtime.Val → iProp
  | .unit, v => iprop(⌜v = .unit⌝)
  | .bool, v => iprop(⌜∃ b, v = .bool b⌝)
  | .int, v => iprop(⌜∃ n, v = .int n⌝)
  | .char, v => iprop(⌜∃ c, v = .char c⌝)
  | .string, v => iprop(⌜∃ s, v = .str s⌝)
  | .float, v => iprop(⌜∃ b, v = .float b⌝)

omit [MicaGS HasLC.hasLC Sig] in
theorem PrimitiveType.valRelBody_persistent (p : PrimitiveType) (v : Runtime.Val) :
    Persistent (p.valRelBody v) := by
  unfold PrimitiveType.valRelBody
  cases p <;> infer_instance

/- One structural layer of the value relation.

References use the outer approximation `R`; named types use the inner
continuation `k`. Tuples and sums are structural and mutually recursive with
the list/sum helpers below. Vectors are a big separating conjunction over the
elements.

An unspecified function type is uninhabited. A specified one is interpreted by
its specification, taken at the outer approximation `R`: the specification
mentions types, which `isPrecondFor` interprets through the relation being
defined. `R` rather than `k`, because `R` occurs both negatively (arguments) and
positively (result), so the body is neither monotone nor antitone in the inner
continuation. The guard that makes this well-defined sits inside
`isPrecondFor`, on its resource premises.
-/
mutual
  def ValRelBody (W : World) (R : ValueRelation) (v : Runtime.Val) (t : Typ) (k : RecCont) : iProp :=
    match t with
    | .prim p     => p.valRelBody v
    | .value      => iprop(True)
    | .empty      => iprop(False)
    | .arrow _ _ none     => iprop(False)
    | .arrow args ret (some s) => s.isPrecondFor W R args ret v
    | .tvar _     => iprop(False)
    | .ref t      => iprop(∃ l, ⌜v = .loc l⌝ ∗ locinv l (fun w => R w t))
    | .array t    => iprop(∃ len l, ⌜v = .array len l⌝ ∗ arrayinv len l (fun w => R w t))
    | .ownedArray _ => iprop(∃ len l, ⌜v = .array len l⌝)
    | .vec t      =>
        iprop(∃ vs, ⌜v = .vec vs⌝ ∗ [∗list] w ∈ vs, ValRelBody W R w t k)
    | .owned _    => iprop(∃ l, ⌜v = .loc l⌝)
    | .named T args => k v T args
    | .tuple ts   => iprop(∃ vs, ⌜v = .tuple vs⌝ ∗ ValsRelBody W R vs ts k)
    | .sum ts     =>
        iprop(∃ tag payload, ⌜v = .inj tag ts.length payload⌝ ∗
          ValSumRelBody W R tag payload ts k)

  def ValsRelBody (W : World) : ValueRelation → List Runtime.Val → List Typ → RecCont → iProp
    | _, [], [], _ => iprop(emp)
    | R, v :: vs, t :: ts, k => iprop(ValRelBody W R v t k ∗ ValsRelBody W R vs ts k)
    | _, _, _, _ => iprop(False)

  def ValSumRelBody (W : World) : ValueRelation → Nat → Runtime.Val → List Typ → RecCont → iProp
    | _, _, _, [], _ => iprop(False)
    | R, 0, payload, t :: _, k => ValRelBody W R payload t k
    | R, n + 1, payload, _ :: ts, k => ValSumRelBody W R n payload ts k
end

/-! Monotonicity in the inner continuation. -/

mutual
  private theorem ValRelBody.mono_int (W : World) (R : ValueRelation) (t : Typ) (v : Runtime.Val) {k k' : RecCont} :
      ⊢ □ (∀ v T args, k v T args -∗ k' v T args) -∗
        (ValRelBody W R v t k -∗ ValRelBody W R v t k' : iProp) := by
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
        · ipureintro
          exact heq
        · iapply (ValsRelBody.mono_int W R ts vs)
          · iexact Hk
          · iexact Hvs
    | .vec t =>
        iintro #Hk ⟨%vs, %heq, Hvs⟩
        iexists vs
        isplitr
        · ipureintro
          exact heq
        · iapply BigSepL.bigSepL_impl $$ Hvs
          imodintro
          iintro %i %w %hget
          iapply (ValRelBody.mono_int W R t w)
          iexact Hk
    | .sum ts =>
        iintro #Hk ⟨%tag, %payload, %heq, Hsum⟩
        iexists tag, payload
        isplitr
        · ipureintro
          exact heq
        · iapply (ValSumRelBody.mono_int W R ts tag payload)
          · iexact Hk
          · iexact Hsum
    | .prim _ =>
        iintro _ H
        iexact H
    | .value | .empty | .arrow _ _ none | .arrow _ _ (some _) | .tvar _ | .ref _ | .array _
    | .ownedArray _ | .owned _ =>
        iintro _ H
        iexact H

  private theorem ValsRelBody.mono_int (W : World) (R : ValueRelation) (ts : List Typ) (vs : List Runtime.Val)
      {k k' : RecCont} :
      ⊢ □ (∀ v T args, k v T args -∗ k' v T args) -∗
        (ValsRelBody W R vs ts k -∗ ValsRelBody W R vs ts k' : iProp) := by
    unfold ValsRelBody
    match vs, ts with
    | [], [] =>
        iintro _ H
        iexact H
    | v :: vs, t :: ts =>
        iintro #Hk ⟨Hv, Hvs⟩
        isplitl [Hv]
        · iapply (ValRelBody.mono_int W R t v)
          · iexact Hk
          · iexact Hv
        · iapply (ValsRelBody.mono_int W R ts vs)
          · iexact Hk
          · iexact Hvs
    | [], _ :: _ | _ :: _, [] =>
        iintro _ H
        iexact H

  private theorem ValSumRelBody.mono_int (W : World) (R : ValueRelation) (ts : List Typ) (tag : Nat)
      (payload : Runtime.Val) {k k' : RecCont} :
      ⊢ □ (∀ v T args, k v T args -∗ k' v T args) -∗
        (ValSumRelBody W R tag payload ts k -∗ ValSumRelBody W R tag payload ts k' : iProp) := by
    unfold ValSumRelBody
    match tag, ts with
    | _, [] =>
        iintro _ H
        iexact H
    | 0, t :: _ =>
        iintro #Hk Hv
        iapply (ValRelBody.mono_int W R t payload)
        · iexact Hk
        · iexact Hv
    | n + 1, _ :: ts =>
        iintro #Hk Hv
        iapply (ValSumRelBody.mono_int W R ts n payload)
        · iexact Hk
        · iexact Hv
end

/-! Mixed OFE continuity in the outer approximation and inner continuation. -/

mutual
  private theorem ValRelBody.dist {n : Nat} {W : World} {R S : ValueRelation} {k k' : RecCont}
      (hR : DistLater n R S) (hk : k ≡{n}≡ k') (t : Typ) (v : Runtime.Val) :
      ValRelBody W R v t k ≡{n}≡ ValRelBody W S v t k' := by
    unfold ValRelBody
    match t with
    | .ref t =>
        refine exists_ne fun l => ?_
        refine sep_ne.ne (.of_eq rfl) ?_
        apply Contractive.distLater_dist (f := fun I : Runtime.Val → iProp => locinv l I)
        intro m hm w
        exact hR m hm w t
    | .array t =>
        refine exists_ne fun len => ?_
        refine exists_ne fun l => ?_
        refine sep_ne.ne (.of_eq rfl) ?_
        apply Contractive.distLater_dist (f := fun I : Runtime.Val → iProp => arrayinv len l I)
        intro m hm w
        exact hR m hm w t
    | .ownedArray _ =>
        exact Dist.rfl
    | .named T args =>
        exact hk v T args
    | .tuple ts =>
        refine exists_ne fun vs => ?_
        refine sep_ne.ne (.of_eq rfl) ?_
        exact ValsRelBody.dist hR hk ts vs
    | .vec t =>
        refine exists_ne fun vs => ?_
        refine sep_ne.ne (.of_eq rfl) ?_
        exact Iris.Algebra.BigOpL.bigOpL_gen_proper (· ≡{n}≡ ·) Dist.rfl (sep_ne.ne · ·)
          (fun _ => ValRelBody.dist hR hk t _)
    | .sum ts =>
        refine exists_ne fun tag => ?_
        refine exists_ne fun payload => ?_
        refine sep_ne.ne (.of_eq rfl) ?_
        exact ValSumRelBody.dist hR hk ts tag payload
    | .arrow args ret (some s) =>
        exact Spec.isPrecondFor_contractive hR args ret v s
    | .prim _ =>
        exact Dist.rfl
    | .value | .empty | .arrow _ _ none | .tvar _ | .owned _ =>
        exact Dist.rfl

  private theorem ValsRelBody.dist {n : Nat} {W : World} {R S : ValueRelation} {k k' : RecCont}
      (hR : DistLater n R S) (hk : k ≡{n}≡ k') (ts : List Typ) (vs : List Runtime.Val) :
      ValsRelBody W R vs ts k ≡{n}≡ ValsRelBody W S vs ts k' := by
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

  private theorem ValSumRelBody.dist {n : Nat} {W : World} {R S : ValueRelation} {k k' : RecCont}
      (hR : DistLater n R S) (hk : k ≡{n}≡ k') (ts : List Typ) (tag : Nat)
      (payload : Runtime.Val) :
      ValSumRelBody W R tag payload ts k ≡{n}≡ ValSumRelBody W S tag payload ts k' := by
    unfold ValSumRelBody
    match tag, ts with
    | _, [] =>
        exact Dist.rfl
    | 0, t :: _ =>
        exact ValRelBody.dist hR hk t payload
    | n + 1, _ :: ts =>
        exact ValSumRelBody.dist hR hk ts n payload
end

private instance ValRelBody.contractive (W : World) (k : RecCont) (v : Runtime.Val) (t : Typ) :
    Contractive (fun R : ValueRelation => ValRelBody W R v t k) where
  distLater_dist hR := ValRelBody.dist hR Dist.rfl t v

/-- One unfolding of the inner recursive type interpretation. -/
private def ValRelIndF (W : World) (R : ValueRelation) (Φ : RecIdx → iProp) (x : RecIdx) : iProp :=
  match x with
  | ⟨(v, T, args)⟩ =>
      iprop(∃ ty, ⌜TypeName.unfold W.Θ T args = some ty⌝ ∗
        ValRelBody W R v ty (RecCont.ofPred Φ))

private instance (W : World) (R : ValueRelation) (Φ : RecIdx → iProp) :
    NonExpansive (ValRelIndF W R Φ) where
  ne {_ x y} h := by
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    cases LeibnizO.dist_inj h
    exact Dist.of_eq rfl

private theorem ValRelIndF.contractive (W : World) (Φ : RecIdx → iProp) (x : RecIdx) :
    Contractive (fun R : ValueRelation => ValRelIndF W R Φ x) where
  distLater_dist {n R S} hR := by
    obtain ⟨v, T, args⟩ := x
    simp only [ValRelIndF]
    refine exists_ne fun ty => ?_
    refine sep_ne.ne (.of_eq rfl) ?_
    exact Contractive.distLater_dist
      (f := fun R : ValueRelation => ValRelBody W R v ty (RecCont.ofPred Φ)) hR

private instance (W : World) (R : ValueRelation) : BIMonoPred (ValRelIndF W R) where
  mono_pred := by
    intro Φ Ψ _ _
    iintro #HΦΨ %x HF
    obtain ⟨v, T, args⟩ := x
    simp only [ValRelIndF]
    icases HF with ⟨%ty, %hunfold, Hv⟩
    iexists ty
    isplitr
    · ipureintro
      exact hunfold
    · iapply (ValRelBody.mono_int W R ty v
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
private def ValRelInd (W : World) (R : ValueRelation) : RecCont :=
  fun v T args => Iris.bi_least_fixpoint (ValRelIndF W R) ⟨(v, T, args)⟩

private theorem ValRelInd.unfold {W : World} {R : ValueRelation}
    {v : Runtime.Val} {T : TypeName} {args : List Typ} :
    ValRelInd W R v T args ⊣⊢
      iprop(∃ ty, ⌜TypeName.unfold W.Θ T args = some ty⌝ ∗
        ValRelBody W R v ty (ValRelInd W R)) := by
  have h := Iris.least_fixpoint_unfold (ValRelIndF W R) (x := ⟨(v, T, args)⟩)
  simp only [ValRelIndF] at h
  exact equiv_iff.mp h

private instance ValRelInd.contractive (W : World) :
    Contractive (fun R : ValueRelation => ValRelInd W R) where
  distLater_dist {n R S} hR v T args := by
    unfold ValRelInd Iris.bi_least_fixpoint
    refine forall_ne fun Φ => ?_
    refine wand_ne.ne ?_ (.of_eq rfl)
    refine intuitionistically_ne.ne ?_
    refine forall_ne fun x => ?_
    refine wand_ne.ne ?_ (.of_eq rfl)
    exact (ValRelIndF.contractive W (fun x => Φ x) x).distLater_dist hR

/-- The outer functional. It closes the named-type continuation using `ValRelInd`. -/
private def ValRelF (W : World) (R : ValueRelation) : ValueRelation :=
  fun v t => ValRelBody W R v t (ValRelInd W R)

private instance ValRelF.contractive (W : World) : Contractive (ValRelF W) where
  distLater_dist {n R S} hR v t := by
    unfold ValRelF
    have hk : ValRelInd W R ≡{n}≡ ValRelInd W S :=
      Contractive.distLater_dist (f := fun R : ValueRelation => ValRelInd W R) hR
    exact ValRelBody.dist hR hk t v

/-- The mixed recursive value relation. -/
def ValHasType (W : World) : ValueRelation :=
  fixpoint (ValRelF W)

/-- Final tuple/list relation induced by the mixed recursive value relation.
    Reducible so that it unifies with `ValsRel` at an instantiated `V`. -/
@[reducible] def ValsHaveTypes (W : World) (vs : List Runtime.Val) (ts : List Typ) : iProp :=
  ValsRel (ValHasType W) vs ts

/-- Final sum-payload relation induced by the mixed recursive value relation. -/
def ValSumRel (W : World) (tag : Nat) (payload : Runtime.Val)
    (ts : List Typ) : iProp :=
  ValSumRelBody W (ValHasType W) tag payload ts (ValRelInd W (ValHasType W))

theorem ValHasType.unfold (W : World) (v : Runtime.Val) (t : Typ) :
    ValHasType W v t ≡ ValRelBody W (ValHasType W) v t (ValRelInd W (ValHasType W)) := by
  let F : ValueRelation -c> ValueRelation := {
    f := ValRelF W
    contractive := inferInstance
  }
  exact (fixpoint_unfold F) v t

/-- At the fixpoint, the pointwise lifting agrees with the structural list
    layer of the value relation. -/
theorem ValsHaveTypes.unfold (W : World) :
    ∀ (vs : List Runtime.Val) (ts : List Typ),
      ValsHaveTypes W vs ts ⊣⊢ ValsRelBody W (ValHasType W) vs ts (ValRelInd W (ValHasType W))
  | [], [] => .rfl
  | [], _ :: _ | _ :: _, [] => .rfl
  | v :: vs, t :: ts => by
      show iprop(ValHasType W v t ∗ ValsRel (ValHasType W) vs ts) ⊣⊢
        iprop(ValRelBody W (ValHasType W) v t (ValRelInd W (ValHasType W)) ∗
          ValsRelBody W (ValHasType W) vs ts (ValRelInd W (ValHasType W)))
      exact sep_congr (equiv_iff.mp (ValHasType.unfold W v t)) (ValsHaveTypes.unfold W vs ts)


/-! Persistence of the mixed value relation. -/

mutual
  theorem ValRelBody.persistent (W : World) (R : ValueRelation) (t : Typ) (v : Runtime.Val) {k : RecCont}
      (hk : ∀ v T args, Persistent (k v T args)) : Persistent (ValRelBody W R v t k) := by
    unfold ValRelBody
    match t with
    | .prim _ =>
        exact PrimitiveType.valRelBody_persistent _ v
    | .value | .empty | .arrow _ _ none | .arrow _ _ (some _) | .tvar _ | .owned _
    | .ownedArray _ =>
        infer_instance
    | .ref _ =>
        have := locinv_persistent
        infer_instance
    | .array _ =>
        have := arrayinv_persistent
        infer_instance
    | .named T args =>
        exact hk v T args
    | .tuple ts =>
        have : ∀ vs, Persistent (ValsRelBody W R vs ts k) :=
          fun vs => ValsRelBody.persistent W R ts vs hk
        infer_instance
    | .vec t =>
        have hw : ∀ (w : Runtime.Val), Persistent (ValRelBody W R w t k) :=
          fun w => ValRelBody.persistent W R t w hk
        have : ∀ vs : List Runtime.Val,
            Persistent (iprop([∗list] w ∈ vs, ValRelBody W R w t k)) :=
          fun _ => BigSepL.bigSepL_persistent (fun _ w _ => hw w)
        infer_instance
    | .sum ts =>
        have : ∀ n payload, Persistent (ValSumRelBody W R n payload ts k) :=
          fun n payload => ValSumRelBody.persistent W R ts n payload hk
        infer_instance

  theorem ValsRelBody.persistent (W : World) (R : ValueRelation) (ts : List Typ) (vs : List Runtime.Val)
      {k : RecCont} (hk : ∀ v T args, Persistent (k v T args)) :
      Persistent (ValsRelBody W R vs ts k) := by
    unfold ValsRelBody
    match vs, ts with
    | [], [] =>
        infer_instance
    | v :: vs, t :: ts =>
        have := ValRelBody.persistent W R t v hk
        have := ValsRelBody.persistent W R ts vs hk
        infer_instance
    | [], _ :: _ | _ :: _, [] =>
        infer_instance

  theorem ValSumRelBody.persistent (W : World) (R : ValueRelation) (ts : List Typ) (n : Nat)
      (payload : Runtime.Val) {k : RecCont} (hk : ∀ v T args, Persistent (k v T args)) :
      Persistent (ValSumRelBody W R n payload ts k) := by
    unfold ValSumRelBody
    match n, ts with
    | _, [] =>
        infer_instance
    | 0, t :: _ =>
        exact ValRelBody.persistent W R t payload hk
    | n + 1, _ :: ts =>
        exact ValSumRelBody.persistent W R ts n payload hk
end

private instance ValRelIndF.persistent (W : World) (R : ValueRelation) (Φ : RecIdx → iProp)
    [∀ x, Persistent (Φ x)] (x : RecIdx) : Persistent (ValRelIndF W R Φ x) := by
  obtain ⟨v, T, args⟩ := x
  simp only [ValRelIndF]
  have : ∀ ty, Persistent (ValRelBody W R v ty (RecCont.ofPred Φ)) :=
    fun ty => ValRelBody.persistent W R ty v (fun _ _ _ => inferInstance)
  infer_instance

private instance ValRelIndF.absorbing (W : World) (R : ValueRelation) (Φ : RecIdx → iProp)
    [∀ x, Absorbing (Φ x)] (x : RecIdx) : Absorbing (ValRelIndF W R Φ x) := by
  obtain ⟨v, T, args⟩ := x
  simp only [ValRelIndF]
  infer_instance

instance (W : World) (R : ValueRelation) (v : Runtime.Val) (T : TypeName)
    (args : List Typ) : Persistent (ValRelInd W R v T args) :=
  @Iris.least_fixpoint_persistent_absorbing iProp RecIdx _ _ (ValRelIndF W R) _
    (fun _ _ _ => inferInstance) (fun _ _ _ => inferInstance) ⟨(v, T, args)⟩

instance (W : World) (v : Runtime.Val) (t : Typ) : Persistent (ValHasType W v t) :=
  (persistent_congr (equiv_iff.mp (ValHasType.unfold W v t))).mpr
    (ValRelBody.persistent W (ValHasType W) t v (fun _ _ _ => inferInstance))

instance (W : World) (vs : List Runtime.Val) (ts : List Typ) :
    Persistent (ValsHaveTypes W vs ts) :=
  ValsRel.persistent (ValHasType W) (fun _ _ => inferInstance) vs ts

instance (W : World) (tag : Nat) (payload : Runtime.Val) (ts : List Typ) :
    Persistent (ValSumRel W tag payload ts) :=
  ValSumRelBody.persistent W (ValHasType W) ts tag payload (fun _ _ _ => inferInstance)


/-! Per-type unfoldings -/

theorem ValHasType.unit (W : World) (v : Runtime.Val) :
    ValHasType W v Typ.unit ⊣⊢ iprop(⌜v = .unit⌝) := by
  change ValHasType W v (.prim .unit) ⊣⊢ iprop(⌜v = .unit⌝)
  exact equiv_iff.mp (ValHasType.unfold W v Typ.unit)

theorem ValHasType.bool (W : World) (v : Runtime.Val) :
    ValHasType W v Typ.bool ⊣⊢ iprop(⌜∃ b, v = .bool b⌝) := by
  change ValHasType W v (.prim .bool) ⊣⊢ iprop(⌜∃ b, v = .bool b⌝)
  exact equiv_iff.mp (ValHasType.unfold W v Typ.bool)

theorem ValHasType.int (W : World) (v : Runtime.Val) :
    ValHasType W v Typ.int ⊣⊢ iprop(⌜∃ n, v = .int n⌝) := by
  change ValHasType W v (.prim .int) ⊣⊢ iprop(⌜∃ n, v = .int n⌝)
  exact equiv_iff.mp (ValHasType.unfold W v Typ.int)

theorem ValHasType.char (W : World) (v : Runtime.Val) :
    ValHasType W v Typ.char ⊣⊢ iprop(⌜∃ c, v = .char c⌝) := by
  change ValHasType W v (.prim .char) ⊣⊢ iprop(⌜∃ c, v = .char c⌝)
  exact equiv_iff.mp (ValHasType.unfold W v Typ.char)

theorem ValHasType.string (W : World) (v : Runtime.Val) :
    ValHasType W v Typ.string ⊣⊢ iprop(⌜∃ s, v = .str s⌝) := by
  change ValHasType W v (.prim .string) ⊣⊢ iprop(⌜∃ s, v = .str s⌝)
  exact equiv_iff.mp (ValHasType.unfold W v Typ.string)

theorem ValHasType.float (W : World) (v : Runtime.Val) :
    ValHasType W v Typ.float ⊣⊢ iprop(⌜∃ b, v = .float b⌝) := by
  change ValHasType W v (.prim .float) ⊣⊢ iprop(⌜∃ b, v = .float b⌝)
  exact equiv_iff.mp (ValHasType.unfold W v Typ.float)

theorem ValHasType.value (W : World) (v : Runtime.Val) :
    ValHasType W v .value ⊣⊢ iprop(True) := by
  exact equiv_iff.mp (ValHasType.unfold W v .value)

theorem ValHasType.empty (W : World) (v : Runtime.Val) :
    ValHasType W v .empty ⊣⊢ iprop(False) := by
  exact equiv_iff.mp (ValHasType.unfold W v .empty)

/-- An unspecified function type is uninhabited: nothing is known about a
    function that carries no specification. -/
theorem ValHasType.arrow_none (W : World) (v : Runtime.Val) (args : List Typ) (ret : Typ) :
    ValHasType W v (.arrow args ret none) ⊣⊢ iprop(False) := by
  exact equiv_iff.mp (ValHasType.unfold W v (.arrow args ret none))

/-- A specified function type holds of exactly the values that satisfy its
    specification, with the specification's types interpreted by the value
    relation itself. -/
theorem ValHasType.arrow_some (W : World) (v : Runtime.Val) (args : List Typ) (ret : Typ)
    (s : Spec Typ) :
    ValHasType W v (.arrow args ret (some s)) ⊣⊢
      s.isPrecondFor W (ValHasType W) args ret v := by
  exact equiv_iff.mp (ValHasType.unfold W v (.arrow args ret (some s)))

theorem ValHasType.ref (W : World) (v : Runtime.Val) (t : Typ) :
    ValHasType W v (.ref t) ⊣⊢
      iprop(∃ l, ⌜v = .loc l⌝ ∗ locinv l (fun w => ValHasType W w t)) := by
  exact equiv_iff.mp (ValHasType.unfold W v (.ref t))

theorem ValHasType.owned (W : World) (v : Runtime.Val) (t : Typ) :
    ValHasType W v (.owned t) ⊣⊢ iprop(∃ l, ⌜v = .loc l⌝) := by
  exact equiv_iff.mp (ValHasType.unfold W v (.owned t))

theorem ValHasType.array (W : World) (v : Runtime.Val) (t : Typ) :
    ValHasType W v (.array t) ⊣⊢
      iprop(∃ len l, ⌜v = .array len l⌝ ∗ arrayinv len l (fun w => ValHasType W w t)) := by
  exact equiv_iff.mp (ValHasType.unfold W v (.array t))

/-- Owned arrays expose their runtime shape; contents are carried by the
spatial owned-array assertion. -/
theorem ValHasType.ownedArray (W : World) (v : Runtime.Val) (t : Typ) :
    ValHasType W v (.ownedArray t) ⊣⊢ iprop(∃ len l, ⌜v = .array len l⌝) := by
  exact equiv_iff.mp (ValHasType.unfold W v (.ownedArray t))

theorem ValHasType.vec (W : World) (v : Runtime.Val) (t : Typ) :
    ValHasType W v (.vec t) ⊣⊢
      iprop(∃ vs, ⌜v = .vec vs⌝ ∗ [∗list] w ∈ vs, ValHasType W w t) := by
  refine (equiv_iff.mp (ValHasType.unfold W v (.vec t))).trans ?_
  apply equiv_iff.mp
  refine equiv_dist.mpr fun _ => ?_
  refine exists_ne fun vs => ?_
  refine sep_ne.ne (.of_eq rfl) ?_
  exact (BigSepL.bigSepL_eqv fun _ => (ValHasType.unfold W _ t).symm).dist

theorem ValHasType.tuple (W : World) (v : Runtime.Val) (ts : List Typ) :
    ValHasType W v (.tuple ts) ⊣⊢
      iprop(∃ vs, ⌜v = .tuple vs⌝ ∗ ValsHaveTypes W vs ts) := by
  refine (equiv_iff.mp (ValHasType.unfold W v (.tuple ts))).trans ?_
  exact exists_congr fun vs => sep_congr .rfl (ValsHaveTypes.unfold W vs ts).symm

theorem ValHasType.sum (W : World) (v : Runtime.Val) (ts : List Typ) :
    ValHasType W v (.sum ts) ⊣⊢
      iprop(∃ tag payload, ⌜v = .inj tag ts.length payload⌝ ∗
        ValSumRel W tag payload ts) := by
  exact equiv_iff.mp (ValHasType.unfold W v (.sum ts))

theorem ValHasType.named (W : World) (v : Runtime.Val) (T : TypeName) (args : List Typ) :
    ValHasType W v (.named T args) ⊣⊢
      iprop(∃ ty, ⌜TypeName.unfold W.Θ T args = some ty⌝ ∗ ValHasType W v ty) := by
  refine (equiv_iff.mp (ValHasType.unfold W v (.named T args))).trans ?_
  refine ValRelInd.unfold.trans ?_
  apply equiv_iff.mp
  refine equiv_dist.mpr fun _ => ?_
  refine exists_ne fun ty => ?_
  refine sep_ne.ne (.of_eq rfl) ?_
  exact (ValHasType.unfold W v ty).symm.dist

theorem ValHasType.named_of_unfold {W : World} {v : Runtime.Val}
    {T : TypeName} {args : List Typ} {ty : Typ}
    (hunfold : TypeName.unfold W.Θ T args = some ty) :
    ValHasType W v (.named T args) ⊣⊢ ValHasType W v ty := by
  refine (ValHasType.named W v T args).trans ?_
  constructor
  · iintro H
    icases H with ⟨%ty', %hunfold', Hty⟩
    rw [hunfold] at hunfold'
    cases hunfold'
    iexact Hty
  · iintro Hty
    iexists ty
    isplitr
    · ipureintro
      exact hunfold
    · iexact Hty

theorem ValsHaveTypes.nil (W : World) :
    ValsHaveTypes W [] [] ⊣⊢ iprop(emp) := by
  unfold ValsHaveTypes ValsRel
  exact .rfl

theorem ValsHaveTypes.cons (W : World) (v : Runtime.Val) (vs : List Runtime.Val)
    (t : Typ) (ts : List Typ) :
    ValsHaveTypes W (v :: vs) (t :: ts) ⊣⊢ ValHasType W v t ∗ ValsHaveTypes W vs ts := by
  simp only [ValsHaveTypes, ValsRel]
  exact .rfl

theorem ValsHaveTypes.nil_cons (W : World) (t : Typ) (ts : List Typ) :
    ValsHaveTypes W [] (t :: ts) ⊣⊢ iprop(False) := by
  unfold ValsHaveTypes ValsRel
  exact .rfl

theorem ValsHaveTypes.cons_nil (W : World) (v : Runtime.Val) (vs : List Runtime.Val) :
    ValsHaveTypes W (v :: vs) [] ⊣⊢ iprop(False) := by
  unfold ValsHaveTypes ValsRel
  exact .rfl

/-! ### The vector type -/

/-- The canonical proof that a vector of well-typed elements has vector type. -/
theorem ValHasType.vec_intro (W : World) (vs : List Runtime.Val) (t : Typ) :
    iprop([∗list] w ∈ vs, ValHasType W w t) ⊢ ValHasType W (.vec vs) (.vec t) := by
  refine .trans ?_ (ValHasType.vec W (.vec vs) t).2
  iintro Hvs
  iexists vs
  isplitr [Hvs]
  · ipureintro; rfl
  · iexact Hvs

/-- Overwriting an in-bounds slot with a well-typed value preserves well-typedness. -/
theorem ValHasType.vec_set (W : World) {vs : List Runtime.Val} {t : Typ}
    {n : Nat} {x w : Runtime.Val} (h : vs[n]? = some x) :
    iprop(([∗list] w' ∈ vs, ValHasType W w' t) ∗ ValHasType W w t) ⊢
      ValHasType W (.vec (vs.set n w)) (.vec t) := by
  refine .trans ?_ (ValHasType.vec_intro W (vs.set n w) t)
  refine (sep_mono_left (BigSepL.bigSepL_insert_acc h)).trans ?_
  refine (sep_mono_left sep_elim_right).trans ?_
  exact (sep_mono_left (forall_elim w)).trans wand_elim_left

/-- A replicated well-typed value gives a well-typed vector. -/
theorem ValHasType.vec_replicate (W : World) (n : Nat) (x : Runtime.Val) (t : Typ) :
    ValHasType W x t ⊢ ValHasType W (.vec (List.replicate n x)) (.vec t) := by
  refine .trans ?_ (ValHasType.vec_intro W (List.replicate n x) t)
  induction n with
  | zero => exact affine
  | succ n ih =>
    rw [List.replicate_succ]
    refine .trans ?_ BigSepL.bigSepL_cons.2
    istart
    iintro #Hx
    isplitr []
    · iexact Hx
    · iapply ih
      iexact Hx

theorem ValSumRel.nil (W : World) (tag : Nat) (payload : Runtime.Val) :
    ValSumRel W tag payload [] ⊣⊢ iprop(False) := by
  unfold ValSumRel ValSumRelBody
  exact .rfl

theorem ValSumRel.zero (W : World) (payload : Runtime.Val) (t : Typ) (ts : List Typ) :
    ValSumRel W 0 payload (t :: ts) ⊣⊢ ValHasType W payload t := by
  unfold ValSumRel ValSumRelBody
  exact equiv_iff.mp (ValHasType.unfold W payload t).symm

theorem ValSumRel.succ (W : World) (tag : Nat) (payload : Runtime.Val)
    (t : Typ) (ts : List Typ) :
    ValSumRel W (tag + 1) payload (t :: ts) ⊣⊢ ValSumRel W tag payload ts := by
  unfold ValSumRel
  change ValSumRelBody W (ValHasType W) tag payload ts (ValRelInd W (ValHasType W)) ⊣⊢
    ValSumRelBody W (ValHasType W) tag payload ts (ValRelInd W (ValHasType W))
  exact .rfl

/-! Indexing and subtyping compatibility. -/

/-- `ValSumRel W tag payload ts` is the value relation at `ts[tag]`, when that
index exists. -/
theorem ValSumRel.of_getElem? {W : World} {payload : Runtime.Val} :
    ∀ {ts : List Typ} {tag : Nat} {s : Typ}, ts[tag]? = some s →
      ValSumRel W tag payload ts ⊢ ValHasType W payload s
  | [], _, _, h => by
      simp at h
  | _ :: _, 0, _, h => by
      simp at h
      subst h
      exact (ValSumRel.zero W payload _ _).1
  | _ :: ts, n + 1, _, h => by
      exact (ValSumRel.succ W n payload _ ts).1.trans
        (ValSumRel.of_getElem? (W := W) (payload := payload) (ts := ts) (by simpa using h))

theorem ValSumRel.to_getElem? {W : World} {payload : Runtime.Val} :
    ∀ {ts : List Typ} {tag : Nat} {s : Typ}, ts[tag]? = some s →
      ValHasType W payload s ⊢ ValSumRel W tag payload ts
  | [], _, _, h => by
      simp at h
  | _ :: _, 0, _, h => by
      simp at h
      subst h
      exact (ValSumRel.zero W payload _ _).2
  | _ :: ts, n + 1, _, h => by
      exact (ValSumRel.to_getElem? (W := W) (payload := payload) (ts := ts) (by simpa using h)).trans
        (ValSumRel.succ W n payload _ ts).2

/-- `ValSumRel` implies the tag is in range. -/
theorem ValSumRel.bound {W : World} {payload : Runtime.Val} :
    ∀ {ts : List Typ} {tag : Nat},
      ValSumRel W tag payload ts ⊢ iprop(⌜tag < ts.length⌝)
  | [], tag => (ValSumRel.nil W tag payload).1.trans false_elim
  | _ :: _, 0 => true_intro.trans <| pure_intro (by simp)
  | _ :: ts, tag + 1 =>
      (ValSumRel.succ W tag payload _ ts).1.trans <|
        (ValSumRel.bound (W := W) (payload := payload) (ts := ts) (tag := tag)).trans <|
        pure_mono (by simp)

/-- Inject a typed payload at tag `tag` into a sum type whose `tag`-th component matches. -/
theorem ValHasType.inj {W : World} {payload : Runtime.Val}
    {tag arity : Nat} {ts : List Typ} {s : Typ}
    (hlen : ts.length = arity) (hget : ts[tag]? = some s) :
    ValHasType W payload s ⊢ ValHasType W (.inj tag arity payload) (.sum ts) := by
  refine Entails.trans ?_ (ValHasType.sum W (.inj tag arity payload) ts).2
  iintro Hpayload
  iexists tag, payload
  isplitr
  · ipureintro; simp [hlen]
  · iapply (ValSumRel.to_getElem? (W := W) (payload := payload) (ts := ts)
      (tag := tag) (s := s) hget)
    iexact Hpayload

/-- The canonical proof that `unit` has type `unit`. -/
theorem ValHasType.unit_intro (W : World) :
    ⊢ ValHasType W .unit Typ.unit := by
  iapply (ValHasType.unit W .unit).2
  ipureintro; rfl

/-- The canonical proof that a Boolean literal has type `bool`. -/
theorem ValHasType.bool_intro (W : World) (b : Bool) :
    ⊢ ValHasType W (.bool b) Typ.bool := by
  iapply (ValHasType.bool W (.bool b)).2
  ipureintro
  exact ⟨b, rfl⟩

/-- The canonical proof that an integer literal has type `int`. -/
theorem ValHasType.int_intro (W : World) (n : Int) :
    ⊢ ValHasType W (.int n) Typ.int := by
  iapply (ValHasType.int W (.int n)).2
  ipureintro
  exact ⟨n, rfl⟩

/-- The canonical proof that a character literal has type `char`. -/
theorem ValHasType.char_intro (W : World) (c : UInt8) :
    ⊢ ValHasType W (.char c) Typ.char := by
  iapply (ValHasType.char W (.char c)).2
  ipureintro
  exact ⟨c, rfl⟩

/-- The canonical proof that a string literal has type `string`. -/
theorem ValHasType.string_intro (W : World) (s : List UInt8) :
    ⊢ ValHasType W (.str s) Typ.string := by
  iapply (ValHasType.string W (.str s)).2
  ipureintro
  exact ⟨s, rfl⟩

/-- The canonical proof that a float literal has type `float`. -/
theorem ValHasType.float_intro (W : World) (b : UInt64) :
    ⊢ ValHasType W (.float b) Typ.float := by
  iapply (ValHasType.float W (.float b)).2
  ipureintro
  exact ⟨b, rfl⟩

/-- Length agreement for `ValsHaveTypes`, as an entailment. -/
theorem ValsHaveTypes.length_eq {W : World} {vs : List Runtime.Val} {ts : List Typ} :
    ValsHaveTypes W vs ts ⊢ iprop(⌜vs.length = ts.length⌝) :=
  ValsRel.length_eq

/-- If `ts[n]? = some t`, then a related list of values contains a value at
index `n` related at type `t`. -/
theorem ValsHaveTypes.of_getElem? {W : World} :
    ∀ {vs : List Runtime.Val} {ts : List Typ} {n : Nat} {t : Typ},
      ts[n]? = some t →
      ValsHaveTypes W vs ts ⊢ iprop(∃ v, ⌜vs[n]? = some v⌝ ∗ ValHasType W v t)
  | [], [], _, _, h => by
      simp at h
  | [], t :: ts, _, _, _ => by
      exact (ValsHaveTypes.nil_cons W t ts).1.trans false_elim
  | v :: vs, [], _, _, _ => by
      exact (ValsHaveTypes.cons_nil W v vs).1.trans false_elim
  | v :: vs, t :: ts, 0, t', h => by
      simp at h
      subst h
      refine (ValsHaveTypes.cons W v vs t ts).1.trans ?_
      iintro H
      icases H with ⟨Hv, _⟩
      iexists v
      isplitr
      · ipureintro
        simp
      · iexact Hv
  | v :: vs, t :: ts, n + 1, t', h => by
      have h' : ts[n]? = some t' := by
        simpa using h
      refine (ValsHaveTypes.cons W v vs t ts).1.trans ?_
      iintro H
      icases H with ⟨_, Hvs⟩
      iapply
        (show iprop(∃ w, ⌜vs[n]? = some w⌝ ∗ ValHasType W w t') ⊢
            iprop(∃ w, ⌜(v :: vs)[n + 1]? = some w⌝ ∗ ValHasType W w t') by
          iintro H'
          icases H' with ⟨%w, %hget, Hwitness⟩
          iexists w
          isplitr
          · ipureintro
            simpa using hget
          · iexact Hwitness)
      iapply (ValsHaveTypes.of_getElem? (W := W) (vs := vs) (ts := ts) (n := n) (t := t') h')
      iexact Hvs


/-! Type preservation for primitive operations. -/

theorem evalBinOp_typed {W : World} {op : BinOp}
    {v1 v2 : Runtime.Val} {t1 t2 ty : Typ}
    (hndiv : op ≠ .div) (hnmod : op ≠ .mod)
    (hty : BinOp.typeOf op t1 t2 = some ty) :
    iprop(ValHasType W v1 t1 ∗ ValHasType W v2 t2) ⊢
      iprop(∃ w, ⌜evalBinOp op v1 v2 = some w⌝ ∗ ValHasType W w ty) := by
  cases op with
  | add =>
      obtain ⟨rfl, rfl, rfl⟩ := BinOp.typeOf_arith (by simp) hty
      refine (sep_mono (ValHasType.int W v1).1 (ValHasType.int W v2).1).trans ?_
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1
      subst v2
      iexists Runtime.Val.int (a + b)
      isplitr
      · ipureintro
        simp [evalBinOp]
      · exact ValHasType.int_intro W (a + b)
  | sub =>
      obtain ⟨rfl, rfl, rfl⟩ := BinOp.typeOf_arith (by simp) hty
      refine (sep_mono (ValHasType.int W v1).1 (ValHasType.int W v2).1).trans ?_
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1
      subst v2
      iexists Runtime.Val.int (a - b)
      isplitr
      · ipureintro
        simp [evalBinOp]
      · exact ValHasType.int_intro W (a - b)
  | mul =>
      obtain ⟨rfl, rfl, rfl⟩ := BinOp.typeOf_arith (by simp) hty
      refine (sep_mono (ValHasType.int W v1).1 (ValHasType.int W v2).1).trans ?_
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1
      subst v2
      iexists Runtime.Val.int (a * b)
      isplitr
      · ipureintro
        simp [evalBinOp]
      · exact ValHasType.int_intro W (a * b)
  | div =>
      cases (hndiv rfl)
  | mod =>
      cases (hnmod rfl)
  | eq =>
      obtain ⟨rfl, rfl, rfl⟩ := BinOp.typeOf_compare (by simp) hty
      refine (sep_mono (ValHasType.int W v1).1 (ValHasType.int W v2).1).trans ?_
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1
      subst v2
      iexists Runtime.Val.bool (a == b)
      isplitr
      · ipureintro
        simp [evalBinOp]
      · exact ValHasType.bool_intro W (a == b)
  | lt =>
      obtain ⟨rfl, rfl, rfl⟩ := BinOp.typeOf_compare (by simp) hty
      refine (sep_mono (ValHasType.int W v1).1 (ValHasType.int W v2).1).trans ?_
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1
      subst v2
      iexists Runtime.Val.bool (a < b)
      isplitr
      · ipureintro
        simp [evalBinOp]
      · exact ValHasType.bool_intro W (a < b)
  | le =>
      obtain ⟨rfl, rfl, rfl⟩ := BinOp.typeOf_compare (by simp) hty
      refine (sep_mono (ValHasType.int W v1).1 (ValHasType.int W v2).1).trans ?_
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1
      subst v2
      iexists Runtime.Val.bool (a ≤ b)
      isplitr
      · ipureintro
        simp [evalBinOp]
      · exact ValHasType.bool_intro W (a ≤ b)
  | gt =>
      obtain ⟨rfl, rfl, rfl⟩ := BinOp.typeOf_compare (by simp) hty
      refine (sep_mono (ValHasType.int W v1).1 (ValHasType.int W v2).1).trans ?_
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1
      subst v2
      iexists Runtime.Val.bool (a > b)
      isplitr
      · ipureintro
        simp [evalBinOp]
      · exact ValHasType.bool_intro W (a > b)
  | ge =>
      obtain ⟨rfl, rfl, rfl⟩ := BinOp.typeOf_compare (by simp) hty
      refine (sep_mono (ValHasType.int W v1).1 (ValHasType.int W v2).1).trans ?_
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1
      subst v2
      iexists Runtime.Val.bool (a ≥ b)
      isplitr
      · ipureintro
        simp [evalBinOp]
      · exact ValHasType.bool_intro W (a ≥ b)
  | and =>
      obtain ⟨rfl, rfl, rfl⟩ := BinOp.typeOf_bool (by simp) hty
      refine (sep_mono (ValHasType.bool W v1).1 (ValHasType.bool W v2).1).trans ?_
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1
      subst v2
      iexists Runtime.Val.bool (a && b)
      isplitr
      · ipureintro
        simp [evalBinOp]
      · exact ValHasType.bool_intro W (a && b)
  | or =>
      obtain ⟨rfl, rfl, rfl⟩ := BinOp.typeOf_bool (by simp) hty
      refine (sep_mono (ValHasType.bool W v1).1 (ValHasType.bool W v2).1).trans ?_
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1
      subst v2
      iexists Runtime.Val.bool (a || b)
      isplitr
      · ipureintro
        simp [evalBinOp]
      · exact ValHasType.bool_intro W (a || b)

theorem evalUnOp_typed {W : World} {op : UnOp}
    {v : Runtime.Val} {t ty : Typ}
    (hty : UnOp.typeOf op t = some ty) :
    ValHasType W v t ⊢
      iprop(∃ w, ⌜evalUnOp op v = some w⌝ ∗ ValHasType W w ty) := by
  cases op with
  | neg =>
      obtain ⟨rfl, rfl⟩ := UnOp.typeOf_int rfl hty
      refine (ValHasType.int W v).1.trans ?_
      iintro Hv
      icases Hv with ⟨%n, %hv⟩
      subst v
      iexists Runtime.Val.int (-n)
      isplitr
      · ipureintro
        simp [evalUnOp]
      · exact ValHasType.int_intro W (-n)
  | not =>
      obtain ⟨rfl, rfl⟩ := UnOp.typeOf_bool rfl hty
      refine (ValHasType.bool W v).1.trans ?_
      iintro Hv
      icases Hv with ⟨%b, %hv⟩
      subst v
      iexists Runtime.Val.bool (!b)
      isplitr
      · ipureintro
        simp [evalUnOp]
      · exact ValHasType.bool_intro W (!b)
  | proj n =>
      cases t with
      | tuple ts =>
          simp [UnOp.typeOf] at hty
          refine (ValHasType.tuple W v ts).1.trans ?_
          iintro H
          icases H with ⟨%vs, %hv, Hvs⟩
          subst v
          iapply
            (show iprop(∃ w, ⌜vs[n]? = some w⌝ ∗ ValHasType W w ty) ⊢
                iprop(∃ w, ⌜evalUnOp (.proj n) (.tuple vs) = some w⌝ ∗ ValHasType W w ty) by
              iintro H'
              icases H' with ⟨%w, %hget, Hwitness⟩
              iexists w
              isplitr
              · ipureintro
                simpa [evalUnOp] using hget
              · iexact Hwitness)
          iapply (ValsHaveTypes.of_getElem? (W := W) (vs := vs) (ts := ts) (n := n) (t := ty) hty)
          iexact Hvs
      | prim _ | sum _ | arrow _ _ | ref _ | array _ | ownedArray _ | vec _ | owned _ | empty | value | tvar _
      | named _ _ =>
          simp [UnOp.typeOf, PrimitiveType.unOpTypeOf] at hty

end TinyML


-- ---------------------------------------------------------------------------
-- Type constraints
-- ---------------------------------------------------------------------------

/-! ### SMT type constraints -/
-- The generators live in `SourceTinyML/TypeConstraints.lean`; their soundness
-- lemmas stay here because their proofs depend on `ValHasType`.

namespace TinyML


/-- Primitive value typing entails the generated primitive type constraints. -/
theorem PrimitiveType.typeConstraints_hold {p : PrimitiveType} {t : Term .value} {ρ : Env}
    {W : TinyML.World} {v : Runtime.Val} (ht : t.eval ρ = v) :
    TinyML.ValHasType W v (.prim p) ⊢ ⌜∀ φ ∈ p.typeConstraints t, φ.eval ρ⌝ := by
  cases p
  · iintro _; ipureintro; simp [PrimitiveType.typeConstraints]
  · refine (TinyML.ValHasType.bool W v).1.trans ?_
    iintro %h
    rcases h with ⟨b, rfl⟩
    ipureintro
    intro φ hφ
    simp [PrimitiveType.typeConstraints] at hφ
    rcases hφ with rfl
    simp [Formula.eval, ht]
  · refine (TinyML.ValHasType.int W v).1.trans ?_
    iintro %h
    rcases h with ⟨n, rfl⟩
    ipureintro
    intro φ hφ
    simp [PrimitiveType.typeConstraints] at hφ
    rcases hφ with rfl
    simp [Formula.eval, ht]
  · refine (TinyML.ValHasType.char W v).1.trans ?_
    iintro %h
    rcases h with ⟨c, rfl⟩
    ipureintro
    intro φ hφ
    simp [PrimitiveType.typeConstraints] at hφ
    rcases hφ with rfl
    simp [Formula.eval, ht]
  · refine (TinyML.ValHasType.string W v).1.trans ?_
    iintro %h
    rcases h with ⟨s, rfl⟩
    ipureintro
    intro φ hφ
    simp [PrimitiveType.typeConstraints] at hφ
    rcases hφ with rfl
    simp [Formula.eval, ht]
  · refine (TinyML.ValHasType.float W v).1.trans ?_
    iintro %h
    rcases h with ⟨b, rfl⟩
    ipureintro
    intro φ hφ
    simp [PrimitiveType.typeConstraints] at hφ
    rcases hφ with rfl
    simp [Formula.eval, ht]

mutual
  /-- If `ValHasType v ty` and `t.eval ρ = v`, then all formulas in `typeConstraints ty t` hold. -/
  theorem typeConstraints_hold {ty : TinyML.Typ} {t : Term .value} {ρ : Env}
      {W : TinyML.World} {v : Runtime.Val} (ht : t.eval ρ = v) :
      TinyML.ValHasType W v ty ⊢ ⌜∀ φ ∈ typeConstraints ty t, φ.eval ρ⌝ := by
    cases ty with
    | prim p =>
      simpa [typeConstraints] using PrimitiveType.typeConstraints_hold (p := p) (W := W) (v := v) ht
    | owned inner =>
      refine (TinyML.ValHasType.owned W v inner).1.trans ?_
      iintro Hty
      icases Hty with ⟨%l, %hv⟩
      subst v
      ipureintro
      intro φ hφ
      simp [typeConstraints] at hφ
      subst hφ
      simp [Formula.eval, hv]
    | array inner =>
      refine (TinyML.ValHasType.array W v inner).1.trans ?_
      iintro Hty
      icases Hty with ⟨%len, %l, %hv, _⟩
      ipureintro
      intro φ hφ
      simp only [typeConstraints, List.mem_cons, List.not_mem_nil] at hφ
      rcases hφ with rfl | hfalse
      · simp [Formula.eval, Term.eval, UnOp.eval, ht, hv]
      · cases hfalse
    | ownedArray inner =>
      refine (TinyML.ValHasType.ownedArray W v inner).1.trans ?_
      iintro Hty
      icases Hty with ⟨%len, %l, %hv⟩
      ipureintro
      intro φ hφ
      simp only [typeConstraints, List.mem_cons, List.not_mem_nil] at hφ
      rcases hφ with rfl | hfalse
      · simp [Formula.eval, Term.eval, UnOp.eval, ht, hv]
      · cases hfalse
    | vec inner =>
      refine (TinyML.ValHasType.vec W v inner).1.trans ?_
      iintro Hty
      icases Hty with ⟨%vs, %hv, _⟩
      ipureintro
      intro φ hφ
      simp only [typeConstraints, List.mem_cons, List.not_mem_nil] at hφ
      rcases hφ with rfl | rfl | hfalse
      · simp [Formula.eval, ht, hv]
      · simp [Formula.eval, Term.eval, UnOp.eval, BinPred.eval, ht, hv]
      · cases hfalse
    | tuple ts =>
      refine (TinyML.ValHasType.tuple W v ts).1.trans ?_
      iintro Hty
      icases Hty with ⟨%vs, Hty'⟩
      icases Hty' with ⟨%hv, hvs⟩
      ihave %htail := (typeConstraintsList_hold (ts := ts) (tl := .unop .toValList t)
        (ρ := ρ) (W := W) (vs := vs) (by simp [Term.eval, UnOp.eval, ht, hv])) $$ hvs
      iclear hvs
      ipureintro
      intro φ hφ
      cases hφ with
      | head =>
        simp [Formula.eval, ht, hv]
      | tail _ hφ =>
        exact htail φ hφ
    | sum _ | ref _ | value | named _ _ =>
      iintro _; ipureintro; simp [typeConstraints]
    | arrow args ret spec =>
      cases spec with
      | none => exact (TinyML.ValHasType.arrow_none W v args ret).1.trans false_elim
      | some _ => iintro _; ipureintro; simp [typeConstraints]
    | empty => exact (TinyML.ValHasType.empty W v).1.trans false_elim
    | tvar x => nomatch x

  theorem typeConstraintsList_hold {ts : List TinyML.Typ} {tl : Term .vallist} {ρ : Env}
      {W : TinyML.World} {vs : List Runtime.Val} (htl : tl.eval ρ = vs) :
      TinyML.ValsHaveTypes W vs ts ⊢ ⌜∀ φ ∈ typeConstraintsList ts tl, φ.eval ρ⌝ := by
    match vs, ts with
    | [], [] =>
        refine (TinyML.ValsHaveTypes.nil W).1.trans ?_
        iintro _
        ipureintro
        simp [typeConstraintsList]
    | v :: vs, ty :: ts =>
        refine (TinyML.ValsHaveTypes.cons W v vs ty ts).1.trans ?_
        iintro hvals
        icases hvals with ⟨hv, hvs⟩
        ihave %hhead := (typeConstraints_hold (ty := ty) (t := .unop .vhead tl)
          (ρ := ρ) (W := W) (v := v) (by simp [Term.eval, UnOp.eval, htl])) $$ hv
        ihave %htail := (typeConstraintsList_hold (ts := ts) (tl := .unop .vtail tl)
          (ρ := ρ) (W := W) (vs := vs) (by simp [Term.eval, UnOp.eval, htl])) $$ hvs
        iclear hv hvs
        ipureintro
        intro φ hφ
        cases List.mem_append.mp hφ with
        | inl h => exact hhead φ h
        | inr h => exact htail φ h
    | [], ty :: ts =>
        exact (TinyML.ValsHaveTypes.nil_cons W ty ts).1.trans false_elim
    | v :: vs, [] =>
        exact (TinyML.ValsHaveTypes.cons_nil W v vs).1.trans false_elim
end

/-- A single element type constraint holds at every in-bounds index of a
well-typed vector snapshot. -/
private theorem elementConstraint_hold {ty : TinyML.Typ}
    {contents : Term .value} {ρ : Env} {W : TinyML.World}
    {vs : List Runtime.Val} {constraint : Formula}
    (hcontents : contents.eval ρ = .vec vs)
    (hconstraint : constraint ∈ typeConstraints ty
      (.binop .vecGet (.unop .toVec contents)
        (.var .int (Fresh.freshName contents.names "i")))) :
    TinyML.ValHasType W (.vec vs) (.vec ty) ⊢
      ⌜(elementConstraint contents (Fresh.freshName contents.names "i") constraint).eval ρ⌝ := by
  refine (TinyML.ValHasType.vec W (.vec vs) ty).1.trans ?_
  iintro Hvec
  icases Hvec with ⟨%ws, %hws, #Htys⟩
  have hws_eq : ws = vs := Runtime.Val.vec.inj hws.symm
  subst ws
  let name := Fresh.freshName contents.names "i"
  have hname : name ∉ contents.names := Fresh.freshName_not_in_avoid contents.names "i"
  simp only [elementConstraint, Formula.eval]
  iapply pure_forall.2
  iintro %i
  have hcontents_i : contents.eval (ρ.updateConst .int name i) = .vec vs :=
    (Term.eval_updateConst_of_fresh hname).trans hcontents
  by_cases hbounds : 0 ≤ i ∧ i < (vs.length : Int)
  · have hi_nat : (i.toNat : Int) = i := by simp [Int.toNat_of_nonneg hbounds.1]
    have hlt : i.toNat < vs.length :=
      Int.ofNat_lt.mp (hi_nat.trans_lt hbounds.2)
    have hlookup : vs[i.toNat]? = some vs[i.toNat] := List.getElem?_eq_getElem hlt
    ihave Hty :=
      (BigSepL.bigSepL_lookup (Φ := fun _ w => TinyML.ValHasType W w ty) hlookup) $$ Htys
    have helem :
        Term.eval (ρ.updateConst .int name i)
          (.binop .vecGet (.unop .toVec contents) (.var .int name)) = vs[i.toNat] := by
      simp [Term.eval, UnOp.eval, BinOp.eval, hcontents_i, hbounds.1, hlookup]
    ihave %hconstraints :=
      (typeConstraints_hold (ty := ty)
        (t := .binop .vecGet (.unop .toVec contents) (.var .int name))
        (ρ := ρ.updateConst .int name i) (W := W) helem) $$ Hty
    iclear Htys
    ipureintro
    intro _
    exact hconstraints constraint (by simpa [name] using hconstraint)
  · iclear Htys
    ipureintro
    intro hante
    exfalso
    apply hbounds
    simpa [name, Formula.eval, Term.eval, UnOp.eval, BinPred.eval, hcontents_i] using hante

/-- A well-typed vector snapshot entails the bounded solver constraints for
all of its in-bounds elements. -/
theorem elementConstraints_hold {ty : TinyML.Typ} {contents : Term .value}
    {ρ : Env} {W : TinyML.World} {vs : List Runtime.Val}
    (hcontents : contents.eval ρ = .vec vs) :
    TinyML.ValHasType W (.vec vs) (.vec ty) ⊢
      ⌜∀ φ ∈ elementConstraints ty contents, φ.eval ρ⌝ := by
  iintro #Hvec
  iapply pure_forall.2
  iintro %φ
  by_cases hφ : φ ∈ elementConstraints ty contents
  · simp only [elementConstraints, List.mem_map] at hφ
    obtain ⟨constraint, hconstraint, rfl⟩ := hφ
    ihave %heval :=
      (elementConstraint_hold (W := W) hcontents hconstraint) $$ Hvec
    iclear Hvec
    ipureintro
    exact fun _ => heval
  · iclear Hvec
    ipureintro
    exact fun hmem => (hφ hmem).elim

end TinyML
