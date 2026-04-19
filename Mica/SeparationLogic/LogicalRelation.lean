import Mica.TinyML.Common
import Mica.TinyML.Types
import Mica.TinyML.RuntimeExpr
import Mica.TinyML.OpSem
import Mica.SeparationLogic.Axioms

open Iris Iris.BI

axiom locinv : Runtime.Location → iProp
axiom locinv_persistent l : Persistent (locinv l)
axiom locinv_from_pointsto l v : l ↦ v ⊢ locinv l

namespace TinyML

mutual
  inductive ValHasType (Θ : TypeEnv) : Runtime.Val → Typ → Prop where
    | int  (n : Int)  : ValHasType Θ (.int n)  .int
    | bool (b : Bool) : ValHasType Θ (.bool b) .bool
    | unit            : ValHasType Θ .unit      .unit
    | ref l τ         : ValHasType Θ (.loc l)   (.ref τ)
    | inj  : (ht : ts[tag]? = some t)
            → ValHasType Θ payload t
            → ValHasType Θ (.inj tag ts.length payload) (.sum ts)
    | tuple : ValsHaveTypes Θ vs ts
            → ValHasType Θ (Runtime.Val.tuple vs) (Typ.tuple ts)
    | named : TypeName.unfold Θ T args = some ty
            → ValHasType Θ v ty
            → ValHasType Θ v (.named T args)
    -- Any value has type .value
    | any : ValHasType Θ v .value

  inductive ValsHaveTypes (Θ : TypeEnv) : List Runtime.Val → List Typ → Prop where
    | nil  : ValsHaveTypes Θ [] []
    | cons : ValHasType Θ v t → ValsHaveTypes Θ vs ts → ValsHaveTypes Θ (v :: vs) (t :: ts)
end


mutual
  theorem ValHasType_sub {Θ : TypeEnv} {v : Runtime.Val} {t t' : Typ} (h : ValHasType Θ v t) (hsub : Typ.Sub Θ t t') :
      ValHasType Θ v t' := by
    match hsub with
    | .refl => exact h
    | .bot => cases h
    | .top => exact .any
    | .trans h1 h2 => exact ValHasType_sub (ValHasType_sub h h1) h2
    | .sum hlist =>
      cases h with
      | inj ht hpayload =>
        obtain ⟨t', ht', hvt'⟩ := ValHasType_subList hpayload hlist ht
        rw [hlist.length_eq]
        exact .inj ht' hvt'
    | .arrow _ _ => cases h
    | .tuple hsub =>
      cases h with
      | tuple hvs => exact .tuple (ValsHaveTypes_sub hvs hsub)
    | .named_left hunfold hsub =>
      cases h with
      | named hunfold' hv =>
        rw [hunfold] at hunfold'
        injection hunfold' with hty
        subst hty
        exact ValHasType_sub hv hsub
    | .named_right hunfold hsub =>
        exact .named hunfold (ValHasType_sub h hsub)

  theorem ValsHaveTypes_sub {Θ : TypeEnv} {vs : List Runtime.Val} {ts ts' : List Typ}
      (h : ValsHaveTypes Θ vs ts) (hsub : Typ.SubList Θ ts ts') :
      ValsHaveTypes Θ vs ts' := by
    match hsub with
    | .nil => cases h; exact .nil
    | .cons hs hss =>
      cases h with
      | cons hv hvs => exact .cons (ValHasType_sub hv hs) (ValsHaveTypes_sub hvs hss)

  /-- Lift a payload through a `SubList`: if `ss[tag]? = some s` and `payload : s`,
      find `ts[tag]? = some t` and produce `ValHasType payload t`. -/
  theorem ValHasType_subList {Θ : TypeEnv} {payload : Runtime.Val} {s : Typ} {ss ts : List Typ}
      (hpayload : ValHasType Θ payload s) (hlist : Typ.SubList Θ ss ts)
      {tag : Nat} (hs : ss[tag]? = some s) :
      ∃ t, ts[tag]? = some t ∧ ValHasType Θ payload t :=
    match hlist, tag with
    | .nil, _ => absurd hs (by simp)
    | .cons hsub _, 0 => by simp at hs; exact ⟨_, rfl, ValHasType_sub (hs ▸ hpayload) hsub⟩
    | .cons _ hss, n + 1 => ValHasType_subList hpayload hss (by simpa using hs)
end

theorem ValsHaveTypes.length_eq {Θ : TypeEnv} : ValsHaveTypes Θ vs ts → vs.length = ts.length
  | .nil => rfl
  | .cons _ h => congrArg (· + 1) h.length_eq

end TinyML


/-- Type preservation for `evalBinOp`: if the inputs are well-typed, the operation returns
    `some w` for a well-typed result `w`. -/
theorem evalBinOp_typed {Θ : TinyML.TypeEnv} {op : TinyML.BinOp} {v1 v2 : Runtime.Val} {t1 t2 ty : TinyML.Typ}
    (hndiv : op ≠ .div) (hnmod : op ≠ .mod)
    (hty : TinyML.BinOp.typeOf op t1 t2 = some ty)
    (ht1 : TinyML.ValHasType Θ v1 t1)
    (ht2 : TinyML.ValHasType Θ v2 t2) :
    ∃ w, TinyML.evalBinOp op v1 v2 = some w ∧ TinyML.ValHasType Θ w ty := by
  cases op
  case div => exact absurd rfl hndiv
  case mod => exact absurd rfl hnmod
  -- All ops (add/sub/mul/eq/lt/le/gt/ge/and/or) require specific input types.
  -- Case-split on the ValHasType witnesses; simp_all eliminates contradictions from typeOf
  -- and substitutes the result type, leaving simple ValHasType goals.
  all_goals
    cases ht1 <;> cases ht2 <;>
    simp only [TinyML.BinOp.typeOf, TinyML.evalBinOp,
               Option.some.injEq, eq_comm] at * <;>
    simp_all
    first | exact .int _ | exact .bool _

private theorem evalUnOp_proj_typed {Θ : TinyML.TypeEnv} {n : Nat} {vs : List Runtime.Val} {ts : List TinyML.Typ} {ty : TinyML.Typ}
    (hty : ts[n]? = some ty) (hvs : TinyML.ValsHaveTypes Θ vs ts) :
    ∃ w, vs[n]? = some w ∧ TinyML.ValHasType Θ w ty := by
  induction n generalizing vs ts with
  | zero =>
    cases hvs with
    | nil => simp at hty
    | cons hv _ =>
      simp at hty ⊢; subst hty; exact hv
  | succ n ih =>
    cases hvs with
    | nil => simp at hty
    | cons _ hvs => simp at hty ⊢; exact ih hty hvs

theorem evalUnOp_typed {op : TinyML.UnOp} {v : Runtime.Val} {t ty : TinyML.Typ}
    (hty : TinyML.UnOp.typeOf op t = some ty)
    (ht : TinyML.ValHasType Θ v t) :
    ∃ w, TinyML.evalUnOp op v = some w ∧ TinyML.ValHasType Θ w ty := by
  cases op
  case proj n =>
    cases ht with
    | tuple hvs =>
      simp only [TinyML.UnOp.typeOf] at hty
      simp only [TinyML.evalUnOp]
      exact evalUnOp_proj_typed hty hvs
    | any => simp [TinyML.UnOp.typeOf] at hty
    | _ => simp [TinyML.UnOp.typeOf] at hty
  -- Remaining ops (neg, not) require specific value shapes.
  all_goals (cases ht <;>
    simp only [TinyML.UnOp.typeOf, TinyML.evalUnOp, Option.some.injEq] at * <;>
    first
    | (obtain rfl := hty; exact ⟨_, rfl, .int _⟩)
    | (obtain rfl := hty; exact ⟨_, rfl, .bool _⟩)
    | simp_all)
