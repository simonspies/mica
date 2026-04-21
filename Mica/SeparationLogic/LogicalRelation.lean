import Mica.TinyML.Common
import Mica.TinyML.Types
import Mica.TinyML.RuntimeExpr
import Mica.TinyML.OpSem
import Mica.SeparationLogic.Axioms
import Iris.BI.Lib.Fixpoint

open Iris Iris.BI Iris.OFE

axiom locinv : Runtime.Location → iProp
axiom locinv_persistent l : Persistent (locinv l)
axiom locinv_from_pointsto l v : l ↦ v ⊢ locinv l

namespace TinyML

/-- Continuation type for the recursive interpretation of named types. -/
abbrev RecCont := Runtime.Val → TypeName → List Typ → iProp

-- Value relation, parametric in a continuation `k` for named types.
mutual
  def ValRel (v : Runtime.Val) (t : Typ) (k : RecCont) : iProp :=
    match t with
    | .unit       => iprop(⌜v = .unit⌝)
    | .bool       => iprop(⌜∃ b, v = .bool b⌝)
    | .int        => iprop(⌜∃ n, v = .int n⌝)
    | .value      => iprop(True)
    | .empty      => iprop(False)
    | .arrow _ _  => iprop(False)
    | .tvar _     => iprop(False)
    | .ref _      => iprop(∃ l, ⌜v = .loc l⌝ ∗ locinv l)
    | .named T args => k v T args
    | .tuple ts   => iprop(∃ vs, ⌜v = .tuple vs⌝ ∗ ValsRel vs ts k)
    | .sum ts     =>
        iprop(∃ tag payload, ⌜v = .inj tag ts.length payload⌝ ∗
              ValSumRel tag payload ts k)

  def ValsRel : List Runtime.Val → List Typ → RecCont → iProp
    | [], [], _ => iprop(emp)
    | v :: vs, t :: ts, k => iprop(ValRel v t k ∗ ValsRel vs ts k)
    | _, _, _ => iprop(False)

  def ValSumRel : Nat → Runtime.Val → List Typ → RecCont → iProp
    | _, _, [], _ => iprop(False)
    | 0, payload, t :: _, k => ValRel payload t k
    | n + 1, payload, _ :: ts, k => ValSumRel n payload ts k
end

mutual
  theorem ValRel.persistent (t : Typ) (v : Runtime.Val) {k : RecCont}
      (hk : ∀ v T args, Persistent (k v T args)) : Persistent (ValRel v t k) := by
    unfold ValRel
    match t with
    | .unit | .bool | .int | .value | .empty
    | .arrow _ _ | .tvar _ => infer_instance
    | .ref _ =>
        have := locinv_persistent
        infer_instance
    | .named T args => exact hk v T args
    | .tuple ts =>
        have : ∀ vs, Persistent (ValsRel vs ts k) := fun vs => ValsRel.persistent ts vs hk
        infer_instance
    | .sum ts =>
        have : ∀ n payload, Persistent (ValSumRel n payload ts k) :=
          fun n payload => ValSumRel.persistent ts n payload hk
        infer_instance

  theorem ValsRel.persistent (ts : List Typ) (vs : List Runtime.Val) {k : RecCont}
      (hk : ∀ v T args, Persistent (k v T args)) : Persistent (ValsRel vs ts k) := by
    unfold ValsRel
    match vs, ts with
    | [], [] => infer_instance
    | v :: vs, t :: ts =>
        have := ValRel.persistent t v hk
        have := ValsRel.persistent ts vs hk
        infer_instance
    | [], _ :: _ | _ :: _, [] => infer_instance

  theorem ValSumRel.persistent (ts : List Typ) (n : Nat) (payload : Runtime.Val) {k : RecCont}
      (hk : ∀ v T args, Persistent (k v T args)) : Persistent (ValSumRel n payload ts k) := by
    unfold ValSumRel
    match n, ts with
    | _, [] => infer_instance
    | 0, t :: _ => exact ValRel.persistent t payload hk
    | n + 1, _ :: ts => exact ValSumRel.persistent ts n payload hk
end

/-! ### Monotonicity in the continuation -/

mutual
  theorem ValRel.mono (t : Typ) (v : Runtime.Val) {k k' : RecCont}
      (hkk : ∀ v T args, k v T args ⊢ k' v T args) :
      ValRel v t k ⊢ ValRel v t k' := by
    unfold ValRel
    match t with
    | .unit | .bool | .int | .value | .empty
    | .arrow _ _ | .tvar _ | .ref _ => exact .rfl
    | .named T args => exact hkk v T args
    | .tuple ts =>
        refine exists_mono fun vs => ?_
        refine sep_mono_r ?_
        exact ValsRel.mono ts vs hkk
    | .sum ts =>
        refine exists_mono fun tag => ?_
        refine exists_mono fun payload => ?_
        refine sep_mono_r ?_
        exact ValSumRel.mono ts tag payload hkk

  theorem ValsRel.mono (ts : List Typ) (vs : List Runtime.Val) {k k' : RecCont}
      (hkk : ∀ v T args, k v T args ⊢ k' v T args) :
      ValsRel vs ts k ⊢ ValsRel vs ts k' := by
    unfold ValsRel
    match vs, ts with
    | [], [] => exact .rfl
    | v :: vs, t :: ts =>
        exact sep_mono (ValRel.mono t v hkk) (ValsRel.mono ts vs hkk)
    | [], _ :: _ | _ :: _, [] => exact .rfl

  theorem ValSumRel.mono (ts : List Typ) (n : Nat) (payload : Runtime.Val) {k k' : RecCont}
      (hkk : ∀ v T args, k v T args ⊢ k' v T args) :
      ValSumRel n payload ts k ⊢ ValSumRel n payload ts k' := by
    unfold ValSumRel
    match n, ts with
    | _, [] => exact .rfl
    | 0, t :: _ => exact ValRel.mono t payload hkk
    | n + 1, _ :: ts => exact ValSumRel.mono ts n payload hkk
end

/-! ### Internalized monotonicity in the continuation -/

mutual
  theorem ValRel.mono_int (t : Typ) (v : Runtime.Val) {k k' : RecCont} :
      ⊢ □ (∀ v T args, k v T args -∗ k' v T args) -∗
        (ValRel v t k -∗ ValRel v t k' : iProp) := by
    unfold ValRel
    match t with
    | .unit | .bool | .int | .value | .empty
    | .arrow _ _ | .tvar _ | .ref _ =>
        iintro _ H; iexact H
    | .named T args =>
        iintro #Hk Hv
        iapply Hk
        iexact Hv
    | .tuple ts =>
        iintro #Hk ⟨%vs, %heq, Hvs⟩
        iexists vs
        isplitr
        · ipure_intro; exact heq
        · iapply (ValsRel.mono_int ts vs)
          · iexact Hk
          · iexact Hvs
    | .sum ts =>
        iintro #Hk ⟨%tag, %payload, %heq, Hsum⟩
        iexists tag, payload
        isplitr
        · ipure_intro; exact heq
        · iapply (ValSumRel.mono_int ts tag payload)
          · iexact Hk
          · iexact Hsum

  theorem ValsRel.mono_int (ts : List Typ) (vs : List Runtime.Val) {k k' : RecCont} :
      ⊢ □ (∀ v T args, k v T args -∗ k' v T args) -∗
        (ValsRel vs ts k -∗ ValsRel vs ts k' : iProp) := by
    unfold ValsRel
    match vs, ts with
    | [], [] =>
        iintro _ H; iexact H
    | v :: vs, t :: ts =>
        iintro #Hk ⟨H1, H2⟩
        isplitl [H1]
        · iapply (ValRel.mono_int t v)
          · iexact Hk
          · iexact H1
        · iapply (ValsRel.mono_int ts vs)
          · iexact Hk
          · iexact H2
    | [], _ :: _ | _ :: _, [] =>
        iintro _ H; iexact H

  theorem ValSumRel.mono_int (ts : List Typ) (n : Nat) (payload : Runtime.Val) {k k' : RecCont} :
      ⊢ □ (∀ v T args, k v T args -∗ k' v T args) -∗
        (ValSumRel n payload ts k -∗ ValSumRel n payload ts k' : iProp) := by
    unfold ValSumRel
    match n, ts with
    | _, [] =>
        iintro _ H; iexact H
    | 0, t :: _ =>
        iintro #Hk Hv
        iapply (ValRel.mono_int t payload)
        · iexact Hk
        · iexact Hv
    | n + 1, _ :: ts =>
        iintro #Hk Hv
        iapply (ValSumRel.mono_int ts n payload)
        · iexact Hk
        · iexact Hv
end

/-! ### RecEnv as a least fixpoint -/

/-- Index of the recursive type environment fixpoint. Wrapped with `LeibnizO`
    so that `NonExpansive` constraints on functions out of it are trivial. -/
abbrev RecIdx := LeibnizO (Runtime.Val × TypeName × List Typ)

/-- Reinterpret a predicate over `RecIdx` as a curried `RecCont`. -/
@[reducible] def RecCont.ofPred (Φ : RecIdx → iProp) : RecCont :=
  fun v T args => Φ ⟨(v, T, args)⟩

/-- One unfolding of the recursive type environment: at index `(v, T, args)`,
    look up the unfolded type `ty` and assert that `v` has type `ty` under the
    interpretation `Φ` for nested named types. -/
def RecEnvF (Θ : TypeEnv) (Φ : RecIdx → iProp) (x : RecIdx) : iProp :=
  match x with
  | ⟨(v, T, args)⟩ =>
      iprop(∃ ty, ⌜TypeName.unfold Θ T args = some ty⌝ ∗
            ValRel v ty (RecCont.ofPred Φ))

instance (Θ Φ) : Iris.OFE.NonExpansive (RecEnvF Θ Φ) where
  ne {_ x y} h := by
    obtain ⟨x⟩ := x; obtain ⟨y⟩ := y
    cases LeibnizO.dist_inj h
    exact Iris.OFE.Dist.of_eq rfl

instance (Θ : TypeEnv) : Iris.BIMonoPred (RecEnvF Θ) where
  mono_pred := by
    intro Φ Ψ _ _
    iintro #HΦΨ %x HF
    obtain ⟨v, T, args⟩ := x
    simp only [RecEnvF]
    icases HF with ⟨%ty, %hunfold, Hv⟩
    iexists ty
    isplitr
    · ipure_intro; exact hunfold
    · iapply (ValRel.mono_int ty v (k := RecCont.ofPred _) (k' := RecCont.ofPred _))
      · imodintro
        iintro %v' %T' %args'
        iapply HΦΨ
      · iexact Hv
  mono_pred_ne.ne {_ x y} h := by
    obtain ⟨x⟩ := x; obtain ⟨y⟩ := y
    cases LeibnizO.dist_inj h
    exact Iris.OFE.Dist.of_eq rfl

/-- The fixpoint interpretation of named types under the type environment `Θ`. -/
def RecEnv (Θ : TypeEnv) (v : Runtime.Val) (T : TypeName) (args : List Typ) : iProp :=
  Iris.bi_least_fixpoint (RecEnvF Θ) ⟨(v, T, args)⟩

/-- The unfolding equation of `RecEnv`. Follows from
    `Iris.least_fixpoint_unfold` once the BIMonoPred instance is real. -/
theorem RecEnv.unfold {Θ : TypeEnv} {v : Runtime.Val} {T : TypeName} {args : List Typ} :
    RecEnv Θ v T args ⊣⊢
      iprop(∃ ty, ⌜TypeName.unfold Θ T args = some ty⌝ ∗
            ValRel v ty (RecEnv Θ)) := by
  have h := Iris.least_fixpoint_unfold (RecEnvF Θ) (x := ⟨(v, T, args)⟩)
  simp only [RecEnvF] at h
  exact Iris.BI.equiv_iff.mp h

/-! ### Final value typing -/

def ValHasType (Θ : TypeEnv) (v : Runtime.Val) (t : Typ) : iProp :=
  ValRel v t (RecEnv Θ)

def ValsHaveTypes (Θ : TypeEnv) (vs : List Runtime.Val) (ts : List Typ) : iProp :=
  ValsRel vs ts (RecEnv Θ)

instance RecEnvF.persistent (Θ : TypeEnv) (Φ : RecIdx → iProp)
    [∀ x, Persistent (Φ x)] (x : RecIdx) : Persistent (RecEnvF Θ Φ x) := by
  obtain ⟨v, T, args⟩ := x
  simp only [RecEnvF]
  have : ∀ ty, Persistent (ValRel v ty (RecCont.ofPred Φ)) :=
    fun ty => ValRel.persistent ty v (fun _ _ _ => inferInstance)
  infer_instance

instance RecEnvF.absorbing (Θ : TypeEnv) (Φ : RecIdx → iProp)
    [∀ x, Absorbing (Φ x)] (x : RecIdx) : Absorbing (RecEnvF Θ Φ x) := by
  obtain ⟨v, T, args⟩ := x
  simp only [RecEnvF]
  infer_instance

instance (Θ v T args) : Persistent (RecEnv Θ v T args) :=
  @Iris.least_fixpoint_persistent_absorbing iProp RecIdx _ _ (RecEnvF Θ) _
    (fun _ _ _ => inferInstance) (fun _ _ _ => inferInstance) ⟨(v, T, args)⟩

instance (Θ v t) : Persistent (ValHasType Θ v t) :=
  ValRel.persistent t v (fun _ _ _ => inferInstance)

instance (Θ vs ts) : Persistent (ValsHaveTypes Θ vs ts) :=
  ValsRel.persistent ts vs (fun _ _ _ => inferInstance)

theorem ValsHaveTypes.cons {Θ : TypeEnv} {v : Runtime.Val} {vs : List Runtime.Val}
    {t : Typ} {ts : List Typ} :
    ValsHaveTypes Θ (v :: vs) (t :: ts) ⊣⊢ ValHasType Θ v t ∗ ValsHaveTypes Θ vs ts := by
  unfold ValsHaveTypes ValHasType
  simp [ValsRel]

/-! ### Subtyping (entailments). `Typ.Sub` stays in `Prop`. -/

/-- `ValSumRel tag payload ts k` is defined by navigating to `ts[tag]`. This
    lemma exposes that characterization from one direction. -/
theorem ValSumRel.of_getElem? {k : RecCont} {payload : Runtime.Val} :
    ∀ {ts : List Typ} {tag : Nat} {s : Typ}, ts[tag]? = some s →
      ValSumRel tag payload ts k ⊢ ValRel payload s k
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, h => by
      unfold ValSumRel; simp at h; subst h; exact .rfl
  | _ :: ts, n + 1, _, h => by
      unfold ValSumRel
      exact ValSumRel.of_getElem? (ts := ts) (by simpa using h)

theorem ValSumRel.to_getElem? {k : RecCont} {payload : Runtime.Val} :
    ∀ {ts : List Typ} {tag : Nat} {s : Typ}, ts[tag]? = some s →
      ValRel payload s k ⊢ ValSumRel tag payload ts k
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, h => by
      unfold ValSumRel; simp at h; subst h; exact .rfl
  | _ :: ts, n + 1, _, h => by
      unfold ValSumRel
      exact ValSumRel.to_getElem? (ts := ts) (by simpa using h)

mutual
  theorem ValHasType_sub {Θ : TypeEnv} {v : Runtime.Val} {t t' : Typ}
      (hsub : Typ.Sub Θ t t') :
      ValHasType Θ v t ⊢ ValHasType Θ v t' := by
    match hsub with
    | .refl => exact .rfl
    | .bot => unfold ValHasType ValRel; exact false_elim
    | .top => unfold ValHasType ValRel; exact true_intro
    | .trans h1 h2 => exact (ValHasType_sub h1).trans (ValHasType_sub h2)
    | .sum hlist =>
        unfold ValHasType ValRel
        have hlen := hlist.length_eq
        iintro ⟨%tag, %payload, %heq, Hsum⟩
        iexists tag, payload
        isplitr
        · ipure_intro; rw [heq, hlen]
        · iapply (ValsHaveTypes_sub_sum hlist payload tag); iexact Hsum
    | .arrow _ _ => unfold ValHasType ValRel; exact false_elim
    | .tuple hlist =>
        unfold ValHasType ValRel
        refine exists_mono fun vs => ?_
        refine sep_mono_r ?_
        exact ValsHaveTypes_sub (vs := vs) hlist
    | .named_left hunfold hsub' =>
        refine .trans ?_ (ValHasType_sub hsub')
        unfold ValHasType
        change RecEnv _ v _ _ ⊢ _
        refine RecEnv.unfold.1.trans ?_
        iintro ⟨%ty', %hunfold', Hv⟩
        rw [hunfold] at hunfold'
        cases hunfold'
        iexact Hv
    | .named_right hunfold hsub' =>
        refine (ValHasType_sub hsub').trans ?_
        unfold ValHasType
        change _ ⊢ RecEnv _ v _ _
        refine .trans ?_ RecEnv.unfold.2
        iintro Hv
        iexists _
        isplitr
        · ipure_intro; exact hunfold
        · iexact Hv

  theorem ValsHaveTypes_sub {Θ : TypeEnv} {vs : List Runtime.Val} {ts ts' : List Typ}
      (hsub : Typ.SubList Θ ts ts') :
      ValsHaveTypes Θ vs ts ⊢ ValsHaveTypes Θ vs ts' := by
    match hsub, vs with
    | .nil, _ => exact .rfl
    | .cons _ _, [] => unfold ValsHaveTypes ValsRel; exact .rfl
    | .cons hst hrest, v :: vs =>
        unfold ValsHaveTypes ValsRel
        exact sep_mono (ValHasType_sub hst) (ValsHaveTypes_sub (vs := vs) hrest)

  theorem ValsHaveTypes_sub_sum {Θ : TypeEnv} {ss ts : List Typ}
      (hlist : Typ.SubList Θ ss ts) (payload : Runtime.Val) (tag : Nat) :
      ValSumRel tag payload ss (RecEnv Θ) ⊢ ValSumRel tag payload ts (RecEnv Θ) := by
    match hlist, tag with
    | .nil, _ => exact .rfl
    | .cons hst _, 0 =>
        unfold ValSumRel; exact ValHasType_sub (v := payload) hst
    | .cons _ hrest, n + 1 =>
        unfold ValSumRel; exact ValsHaveTypes_sub_sum hrest payload n

  theorem ValHasType_subList {Θ : TypeEnv} {payload : Runtime.Val} {s : Typ}
      {ss ts : List Typ}
      (hlist : Typ.SubList Θ ss ts) {tag : Nat} (hs : ss[tag]? = some s) :
      ValHasType Θ payload s ⊢
        iprop(∃ t, ⌜ts[tag]? = some t⌝ ∗ ValHasType Θ payload t) := by
    match hlist, tag, hs with
    | .nil, _, h => simp at h
    | .cons (t := t') hst _, 0, h =>
        simp at h; subst h
        iintro Hv
        iexists t'
        isplitr
        · ipure_intro; simp
        · iapply (ValHasType_sub hst); iexact Hv
    | .cons (ss := ss') hst hrest, n + 1, h =>
        have h' : ss'[n]? = some s := by simpa using h
        refine (ValHasType_subList hrest h').trans ?_
        iintro ⟨%t, %hget, Hv⟩
        iexists t
        isplitr
        · ipure_intro; simpa using hget
        · iexact Hv
end

/-- Length agreement for `ValsHaveTypes`, as an entailment. -/
theorem ValsHaveTypes.length_eq {Θ : TypeEnv} {vs : List Runtime.Val} {ts : List Typ} :
    ValsHaveTypes Θ vs ts ⊢ iprop(⌜vs.length = ts.length⌝) := by
  unfold ValsHaveTypes
  match vs, ts with
  | [], [] => exact pure_intro rfl
  | v :: vs, t :: ts =>
      unfold ValsRel
      have ih := ValsHaveTypes.length_eq (Θ := Θ) (vs := vs) (ts := ts)
      unfold ValsHaveTypes at ih
      iintro ⟨_, H⟩
      iapply (ih.trans (pure_mono (fun h => by simp [h])))
      iexact H
  | [], _ :: _ | _ :: _, [] => unfold ValsRel; exact false_elim

/-- If `ts[n]? = some t`, then a related list of values contains a value at
    index `n` related at type `t`. -/
theorem ValsRel.of_getElem? {Θ : TypeEnv} :
    ∀ {vs : List Runtime.Val} {ts : List Typ} {n : Nat} {t : Typ},
      ts[n]? = some t →
      ValsRel vs ts (RecEnv Θ) ⊢ iprop(∃ v, ⌜vs[n]? = some v⌝ ∗ ValRel v t (RecEnv Θ))
  | [], [], _, _, h => by
      simp at h
  | [], _ :: _, _, _, _ => by
      unfold ValsRel
      exact false_elim
  | _ :: _, [], _, _, _ => by
      unfold ValsRel
      exact false_elim
  | v :: vs, t :: ts, 0, t', h => by
      simp at h
      subst h
      unfold ValsRel
      iintro H
      icases H with ⟨Hv, Htail⟩
      iexists v
      isplitr
      · ipure_intro
        simp
      · iexact Hv
  | v :: vs, t :: ts, n + 1, t', h => by
      have h' : ts[n]? = some t' := by
        simpa using h
      refine (show ValsRel (v :: vs) (t :: ts) (RecEnv Θ) ⊢
          iprop(∃ w, ⌜(v :: vs)[n + 1]? = some w⌝ ∗ ValRel w t' (RecEnv Θ)) by
        unfold ValsRel
        iintro H
        icases H with ⟨Hhead, Hvs⟩
        iapply
          (show iprop(∃ w, ⌜vs[n]? = some w⌝ ∗ ValRel w t' (RecEnv Θ)) ⊢
              iprop(∃ w, ⌜(v :: vs)[n + 1]? = some w⌝ ∗ ValRel w t' (RecEnv Θ)) by
            iintro H'
            icases H' with ⟨%w, %hget, Hwitness⟩
            iexists w
            isplitr
            · ipure_intro
              simpa using hget
            · iexact Hwitness)
        iapply (ValsRel.of_getElem? (Θ := Θ) (vs := vs) (ts := ts) (n := n) (t := t') h')
        iexact Hvs)

end TinyML

/-! ### Type preservation for primitive operations (entailments). -/

theorem evalBinOp_typed {Θ : TinyML.TypeEnv} {op : TinyML.BinOp}
    {v1 v2 : Runtime.Val} {t1 t2 ty : TinyML.Typ}
    (hndiv : op ≠ .div) (hnmod : op ≠ .mod)
    (hty : TinyML.BinOp.typeOf op t1 t2 = some ty) :
    iprop(TinyML.ValHasType Θ v1 t1 ∗ TinyML.ValHasType Θ v2 t2) ⊢
      iprop(∃ w, ⌜TinyML.evalBinOp op v1 v2 = some w⌝ ∗ TinyML.ValHasType Θ w ty) := by
  cases op with
  | add =>
      cases t1 <;> cases t2 <;> simp [TinyML.BinOp.typeOf] at hty
      subst hty
      unfold TinyML.ValHasType TinyML.ValRel
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1; subst v2
      iexists Runtime.Val.int (a + b)
      isplitr
      · ipure_intro
        simp [TinyML.evalBinOp]
      · ipure_intro
        exact ⟨a + b, rfl⟩
  | sub =>
      cases t1 <;> cases t2 <;> simp [TinyML.BinOp.typeOf] at hty
      subst hty
      unfold TinyML.ValHasType TinyML.ValRel
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1; subst v2
      iexists Runtime.Val.int (a - b)
      isplitr
      · ipure_intro
        simp [TinyML.evalBinOp]
      · ipure_intro
        exact ⟨a - b, rfl⟩
  | mul =>
      cases t1 <;> cases t2 <;> simp [TinyML.BinOp.typeOf] at hty
      subst hty
      unfold TinyML.ValHasType TinyML.ValRel
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1; subst v2
      iexists Runtime.Val.int (a * b)
      isplitr
      · ipure_intro
        simp [TinyML.evalBinOp]
      · ipure_intro
        exact ⟨a * b, rfl⟩
  | div =>
      cases (hndiv rfl)
  | mod =>
      cases (hnmod rfl)
  | eq =>
      cases t1 <;> cases t2 <;> simp [TinyML.BinOp.typeOf] at hty
      subst hty
      unfold TinyML.ValHasType TinyML.ValRel
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1; subst v2
      iexists Runtime.Val.bool (a == b)
      isplitr
      · ipure_intro
        simp [TinyML.evalBinOp]
      · ipure_intro
        exact ⟨a == b, rfl⟩
  | lt =>
      cases t1 <;> cases t2 <;> simp [TinyML.BinOp.typeOf] at hty
      subst hty
      unfold TinyML.ValHasType TinyML.ValRel
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1; subst v2
      iexists Runtime.Val.bool (a < b)
      isplitr
      · ipure_intro
        simp [TinyML.evalBinOp]
      · ipure_intro
        exact ⟨a < b, rfl⟩
  | le =>
      cases t1 <;> cases t2 <;> simp [TinyML.BinOp.typeOf] at hty
      subst hty
      unfold TinyML.ValHasType TinyML.ValRel
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1; subst v2
      iexists Runtime.Val.bool (a ≤ b)
      isplitr
      · ipure_intro
        simp [TinyML.evalBinOp]
      · ipure_intro
        exact ⟨a ≤ b, rfl⟩
  | gt =>
      cases t1 <;> cases t2 <;> simp [TinyML.BinOp.typeOf] at hty
      subst hty
      unfold TinyML.ValHasType TinyML.ValRel
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1; subst v2
      iexists Runtime.Val.bool (a > b)
      isplitr
      · ipure_intro
        simp [TinyML.evalBinOp]
      · ipure_intro
        exact ⟨a > b, rfl⟩
  | ge =>
      cases t1 <;> cases t2 <;> simp [TinyML.BinOp.typeOf] at hty
      subst hty
      unfold TinyML.ValHasType TinyML.ValRel
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1; subst v2
      iexists Runtime.Val.bool (a ≥ b)
      isplitr
      · ipure_intro
        simp [TinyML.evalBinOp]
      · ipure_intro
        exact ⟨a ≥ b, rfl⟩
  | and =>
      cases t1 <;> cases t2 <;> simp [TinyML.BinOp.typeOf] at hty
      subst hty
      unfold TinyML.ValHasType TinyML.ValRel
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1; subst v2
      iexists Runtime.Val.bool (a && b)
      isplitr
      · ipure_intro
        simp [TinyML.evalBinOp]
      · ipure_intro
        exact ⟨a && b, rfl⟩
  | or =>
      cases t1 <;> cases t2 <;> simp [TinyML.BinOp.typeOf] at hty
      subst hty
      unfold TinyML.ValHasType TinyML.ValRel
      iintro H
      icases H with ⟨H1, H2⟩
      icases H1 with ⟨%a, %hv1⟩
      icases H2 with ⟨%b, %hv2⟩
      subst v1; subst v2
      iexists Runtime.Val.bool (a || b)
      isplitr
      · ipure_intro
        simp [TinyML.evalBinOp]
      · ipure_intro
        exact ⟨a || b, rfl⟩

theorem evalUnOp_typed {Θ : TinyML.TypeEnv} {op : TinyML.UnOp}
    {v : Runtime.Val} {t ty : TinyML.Typ}
    (hty : TinyML.UnOp.typeOf op t = some ty) :
    TinyML.ValHasType Θ v t ⊢
      iprop(∃ w, ⌜TinyML.evalUnOp op v = some w⌝ ∗ TinyML.ValHasType Θ w ty) := by
  cases op with
  | neg =>
      cases t <;> simp [TinyML.UnOp.typeOf] at hty
      subst hty
      unfold TinyML.ValHasType TinyML.ValRel
      iintro Hv
      icases Hv with ⟨%n, %hv⟩
      subst v
      iexists Runtime.Val.int (-n)
      isplitr
      · ipure_intro
        simp [TinyML.evalUnOp]
      · ipure_intro
        exact ⟨-n, rfl⟩
  | not =>
      cases t <;> simp [TinyML.UnOp.typeOf] at hty
      subst hty
      unfold TinyML.ValHasType TinyML.ValRel
      iintro Hv
      icases Hv with ⟨%b, %hv⟩
      subst v
      iexists Runtime.Val.bool (!b)
      isplitr
      · ipure_intro
        simp [TinyML.evalUnOp]
      · ipure_intro
        exact ⟨!b, rfl⟩
  | proj n =>
      cases t with
      | tuple ts =>
          simp [TinyML.UnOp.typeOf] at hty
          have hproj :
              iprop(∃ vs, ⌜v = Runtime.Val.tuple vs⌝ ∗ TinyML.ValsRel vs ts (TinyML.RecEnv Θ)) ⊢
                iprop(∃ w, ⌜TinyML.evalUnOp (.proj n) v = some w⌝ ∗ TinyML.ValHasType Θ w ty) := by
            iintro H
            icases H with ⟨%vs, %hv, Hvs⟩
            subst v
            iapply
              (show iprop(∃ w, ⌜vs[n]? = some w⌝ ∗ TinyML.ValRel w ty (TinyML.RecEnv Θ)) ⊢
                  iprop(∃ w, ⌜TinyML.evalUnOp (.proj n) (.tuple vs) = some w⌝ ∗ TinyML.ValHasType Θ w ty) by
                iintro H'
                icases H' with ⟨%w, %hget, Hwitness⟩
                iexists w
                isplitr
                · ipure_intro
                  simpa [TinyML.evalUnOp] using hget
                · simp [TinyML.ValHasType])
            iapply (TinyML.ValsRel.of_getElem? (Θ := Θ) (vs := vs) (ts := ts) (n := n) (t := ty) hty)
            iexact Hvs
          simpa [TinyML.ValHasType, TinyML.ValRel] using hproj
      | unit | bool | int | sum _ | arrow _ _ | ref _ | empty | value | tvar _ | named _ _ =>
          simp [TinyML.UnOp.typeOf] at hty
