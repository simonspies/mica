import Mica.TinyML.Expr
import Mica.TinyML.OpSem

namespace TinyML

/-! ## Type contexts -/

abbrev TyCtx := Var → Option Type_

def TyCtx.empty : TyCtx := fun _ => none

def TyCtx.extend (Γ : TyCtx) (x : Var) (t : Type_) : TyCtx :=
  fun y => if y == x then some t else Γ y

def TyCtx.extendBinder (Γ : TyCtx) (b : Binder) (t : Type_) : TyCtx :=
  match b with
  | .none    => Γ
  | .named x => Γ.extend x t

@[simp] theorem TyCtx.extend_eq (Γ : TyCtx) (x : Var) (t : Type_) :
    (Γ.extend x t) x = some t := by simp [TyCtx.extend]

@[simp] theorem TyCtx.extend_ne (Γ : TyCtx) (x y : Var) (t : Type_) (h : y ≠ x) :
    (Γ.extend x t) y = Γ y := by
  simp [TyCtx.extend, h]

/-- Γ ≤ Γ': Γ' extends Γ pointwise. -/
def TyCtx.le (Γ Γ' : TyCtx) : Prop := ∀ x t, Γ x = some t → Γ' x = some t

instance : LE TyCtx := ⟨TyCtx.le⟩

theorem TyCtx.le_refl (Γ : TyCtx) : Γ ≤ Γ := fun _ _ h => h

theorem TyCtx.le_trans {Γ₁ Γ₂ Γ₃ : TyCtx} (h12 : Γ₁ ≤ Γ₂) (h23 : Γ₂ ≤ Γ₃) : Γ₁ ≤ Γ₃ :=
  fun x t h => h23 x t (h12 x t h)

/-- Monotonicity of `extendBinder` w.r.t. context ordering. -/
theorem TyCtx.le_extendBinder_congr {Γ Γ' : TyCtx} (b : Binder) (t : Type_)
    (hle : Γ ≤ Γ') : Γ.extendBinder b t ≤ Γ'.extendBinder b t := by
  intro y ty hy
  cases b with
  | none => exact hle y ty hy
  | named x =>
    simp only [TyCtx.extendBinder, TyCtx.extend] at hy ⊢
    by_cases h : y == x
    · simp [h] at hy ⊢; exact hy
    · simp [h] at hy ⊢; exact hle y ty hy

/-! ## Subtyping -/

inductive Type_.Sub : Type_ → Type_ → Prop where
  | refl  : Type_.Sub t t
  | bot   : Type_.Sub .empty t
  | top   : Type_.Sub t .value
  | trans : Type_.Sub s t → Type_.Sub t u → Type_.Sub s u
  | prod  : Type_.Sub s1 t1 → Type_.Sub s2 t2
          → Type_.Sub (.prod s1 s2) (.prod t1 t2)
  | sum   : Type_.Sub s1 t1 → Type_.Sub s2 t2
          → Type_.Sub (.sum s1 s2) (.sum t1 t2)
  | arrow : Type_.Sub t1 s1 → Type_.Sub s2 t2
          → Type_.Sub (.arrow s1 s2) (.arrow t1 t2)

mutual
  def Type_.join : Type_ → Type_ → Type_
    | .empty, t | t, .empty => t
    | .value, _ | _, .value => .value
    | .prod s1 s2,  .prod t1 t2  => .prod (Type_.join s1 t1) (Type_.join s2 t2)
    | .sum  s1 s2,  .sum  t1 t2  => .sum  (Type_.join s1 t1) (Type_.join s2 t2)
    | .arrow s1 s2, .arrow t1 t2 => .arrow (Type_.meet s1 t1) (Type_.join s2 t2)
    | .ref s,       .ref t       => if s == t then .ref s else .value
    | t, t'                      => if t == t' then t else .value

  def Type_.meet : Type_ → Type_ → Type_
    | .value, t | t, .value => t
    | .empty, _ | _, .empty => .empty
    | .prod s1 s2,  .prod t1 t2  => .prod (Type_.meet s1 t1) (Type_.meet s2 t2)
    | .sum  s1 s2,  .sum  t1 t2  => .sum  (Type_.meet s1 t1) (Type_.meet s2 t2)
    | .arrow s1 s2, .arrow t1 t2 => .arrow (Type_.join s1 t1) (Type_.meet s2 t2)
    | .ref s,       .ref t       => if s == t then .ref s else .empty
    | t, t'                      => if t == t' then t else .empty
end

def Type_.sub : Type_ → Type_ → Bool
  | .empty, _      => true
  | _, .value      => true
  | .prod s1 s2,  .prod t1 t2  => Type_.sub s1 t1 && Type_.sub s2 t2
  | .sum  s1 s2,  .sum  t1 t2  => Type_.sub s1 t1 && Type_.sub s2 t2
  | .arrow s1 s2, .arrow t1 t2 => Type_.sub t1 s1 && Type_.sub s2 t2
  | t, t'                      => t == t'
termination_by s t => sizeOf s + sizeOf t

-- Forward direction: decision procedure is sound.
-- We use `cases s` at the top so that every recursive sub-call has a concrete first arg,
-- allowing `simp [Type_.sub]` to reduce.  The arrow case calls sub_sound with swapped args
-- so we need a well-founded measure.
private theorem Type_.sub_sound {s t : Type_} (h : Type_.sub s t = true) : Type_.Sub s t := by
  cases s with
  | empty => exact .bot
  | prod s1 s2 =>
      cases t with
      | value => exact .top
      | prod t1 t2 =>
          simp [Type_.sub, Bool.and_eq_true] at h
          exact .prod (sub_sound h.1) (sub_sound h.2)
      | _ => simp [Type_.sub] at h
  | sum s1 s2 =>
      cases t with
      | value => exact .top
      | sum t1 t2 =>
          simp [Type_.sub, Bool.and_eq_true] at h
          exact .sum (sub_sound h.1) (sub_sound h.2)
      | _ => simp [Type_.sub] at h
  | arrow s1 s2 =>
      cases t with
      | value => exact .top
      | arrow t1 t2 =>
          simp [Type_.sub, Bool.and_eq_true] at h
          exact .arrow (sub_sound h.1) (sub_sound h.2)
      | _ => simp [Type_.sub] at h
  | _ =>
      -- unit, bool, int, ref, value: base types, sub reduces to s == t
      cases t with
      | value => exact .top
      | _ => simp_all [Type_.sub] <;> exact .refl
termination_by sizeOf s + sizeOf t

-- Reflexivity of the decision procedure (needed for completeness)
private theorem Type_.sub_refl : ∀ (t : Type_), Type_.sub t t = true
  | .unit | .bool | .int | .empty | .value => by simp [Type_.sub]
  | .prod t1 t2  => by simp [Type_.sub, sub_refl t1, sub_refl t2]
  | .sum  t1 t2  => by simp [Type_.sub, sub_refl t1, sub_refl t2]
  | .arrow t1 t2 => by simp [Type_.sub, sub_refl t1, sub_refl t2]
  | .ref t       => by simp [Type_.sub]

-- Transitivity of the decision procedure (needed for completeness of trans rule).
-- Proved by induction on t (the middle type).
private theorem Type_.sub_trans {s t u : Type_}
    (h1 : Type_.sub s t = true) (h2 : Type_.sub t u = true) :
    Type_.sub s u = true := by
  induction t generalizing s u with
  | empty | value | unit | bool | int => cases s <;> cases u <;> simp_all [Type_.sub]
  | ref _ ih => cases s <;> cases u <;> simp_all [Type_.sub]
  | prod t1 t2 ih1 ih2 =>
      cases s with
      | empty => simp [Type_.sub]
      | prod ss1 ss2 =>
          cases u with
          | value => simp [Type_.sub]
          | prod u1 u2 =>
              simp [Type_.sub, Bool.and_eq_true] at h1 h2 ⊢
              exact ⟨ih1 h1.1 h2.1, ih2 h1.2 h2.2⟩
          | _ => simp [Type_.sub] at h2
      | _ => simp [Type_.sub] at h1
  | sum t1 t2 ih1 ih2 =>
      cases s with
      | empty => simp [Type_.sub]
      | sum ss1 ss2 =>
          cases u with
          | value => simp [Type_.sub]
          | sum u1 u2 =>
              simp [Type_.sub, Bool.and_eq_true] at h1 h2 ⊢
              exact ⟨ih1 h1.1 h2.1, ih2 h1.2 h2.2⟩
          | _ => simp [Type_.sub] at h2
      | _ => simp [Type_.sub] at h1
  | arrow t1 t2 ih1 ih2 =>
      -- domain is contravariant: trans flips s and u for the domain IH
      cases s with
      | empty => simp [Type_.sub]
      | arrow ss1 ss2 =>
          cases u with
          | value => simp [Type_.sub]
          | arrow u1 u2 =>
              simp [Type_.sub, Bool.and_eq_true] at h1 h2 ⊢
              -- h1 : sub t1 ss1 ∧ sub ss2 t2,  h2 : sub u1 t1 ∧ sub t2 u2
              -- need: sub u1 ss1 (via ih1 contravariant) and sub ss2 u2 (via ih2)
              exact ⟨ih1 h2.1 h1.1, ih2 h1.2 h2.2⟩
          | _ => simp [Type_.sub] at h2
      | _ => simp [Type_.sub] at h1

-- Backward direction: derivable subtyping is decided
private theorem Type_.Sub_complete {s t : Type_} : Type_.Sub s t → Type_.sub s t = true
  | .refl        => sub_refl _
  | .bot         => by cases t <;> simp [Type_.sub]
  | .top         => by cases s <;> simp [Type_.sub]
  | .trans h1 h2 => sub_trans (Sub_complete h1) (Sub_complete h2)
  | .prod h1 h2  => by simp [Type_.sub, Sub_complete h1, Sub_complete h2]
  | .sum  h1 h2  => by simp [Type_.sub, Sub_complete h1, Sub_complete h2]
  | .arrow h1 h2 => by simp [Type_.sub, Sub_complete h1, Sub_complete h2]

theorem Type_.sub_iff {s t : Type_} : Type_.sub s t = true ↔ Type_.Sub s t :=
  ⟨sub_sound, Sub_complete⟩

/-! ## Operator typing -/

def BinOp.typeOf : BinOp → Type_ → Type_ → Option Type_
  | .add,  .int,  .int  => some .int
  | .sub,  .int,  .int  => some .int
  | .mul,  .int,  .int  => some .int
  | .div,  .int,  .int  => some .int
  | .eq,   .int,  .int  => some .bool
  | .lt,   .int,  .int  => some .bool
  | .le,   .int,  .int  => some .bool
  | .gt,   .int,  .int  => some .bool
  | .ge,   .int,  .int  => some .bool
  | .and,  .bool, .bool => some .bool
  | .or,   .bool, .bool => some .bool
  | .pair, t1, t2       => some (.prod t1 t2)
  | _, _, _             => none

def UnOp.typeOf : UnOp → Type_ → Option Type_
  | .neg, .int       => some .int
  | .not, .bool      => some .bool
  | .fst, .prod t1 _ => some t1
  | .snd, .prod _ t2 => some t2
  | .inl, t          => some (.sum t .empty)
  | .inr, t          => some (.sum .empty t)
  | _, _             => none

inductive ValHasType : Val → Type_ → Prop where
  | int  (n : Int)  : ValHasType (.int n)  .int
  | bool (b : Bool) : ValHasType (.bool b) .bool
  | unit            : ValHasType .unit      .unit
  | pair : ValHasType v1 t1 → ValHasType v2 t2
          → ValHasType (.pair v1 v2) (.prod t1 t2)
  | inl  : ValHasType v t1
          → ValHasType (.inl v) (.sum t1 t2)
  | inr  : ValHasType v t2
          → ValHasType (.inr v) (.sum t1 t2)
  -- Any value has type .value
  | any : ValHasType v .value


theorem ValHasType_sub {v : Val} {t t' : Type_} (h : ValHasType v t) (hsub : Type_.Sub t t') :
    ValHasType v t' := by
  induction hsub generalizing v with
  | refl => exact h
  | bot => cases h
  | top => exact .any
  | trans _ _ ih1 ih2 => exact ih2 (ih1 h)
  | prod h1 h2 ih1 ih2 =>
    cases h with
    | pair hv1 hv2 => exact .pair (ih1 hv1) (ih2 hv2)
  | sum h1 h2 ih1 ih2 =>
    cases h with
    | inl hv => exact .inl (ih1 hv)
    | inr hv => exact .inr (ih2 hv)
  | arrow _ _ => cases h

end TinyML



/-- Type preservation for `evalBinOp`: if the inputs are well-typed, the operation returns
    `some w` for a well-typed result `w`. -/
theorem evalBinOp_typed {op : TinyML.BinOp} {v1 v2 : TinyML.Val} {t1 t2 ty : TinyML.Type_}
    (hndiv : op ≠ .div)
    (hty : TinyML.BinOp.typeOf op t1 t2 = some ty)
    (ht1 : TinyML.ValHasType v1 t1)
    (ht2 : TinyML.ValHasType v2 t2) :
    ∃ w, TinyML.evalBinOp op v1 v2 = some w ∧ TinyML.ValHasType w ty := by
  -- `.div` is excluded by hypothesis; `.pair` preserves ht1/ht2 so handle separately.
  cases op
  case div => exact absurd rfl hndiv
  case pair =>
    simp only [TinyML.BinOp.typeOf, Option.some.injEq] at hty
    exact ⟨.pair v1 v2, by simp [TinyML.evalBinOp], hty ▸ .pair ht1 ht2⟩
  -- All remaining ops (add/sub/mul/eq/lt/le/gt/ge/and/or) require specific input types.
  -- Case-split on the ValHasType witnesses; simp_all eliminates contradictions from typeOf
  -- and substitutes the result type, leaving simple ValHasType goals.
  all_goals
    cases ht1 <;> cases ht2 <;>
    simp only [TinyML.BinOp.typeOf, TinyML.evalBinOp,
               Option.some.injEq, eq_comm] at * <;>
    simp_all
    first | exact .int _ | exact .bool _

theorem evalUnOp_typed {op : TinyML.UnOp} {v : TinyML.Val} {t ty : TinyML.Type_}
    (hty : TinyML.UnOp.typeOf op t = some ty)
    (ht : TinyML.ValHasType v t) :
    ∃ w, TinyML.evalUnOp op v = some w ∧ TinyML.ValHasType w ty := by
  -- .inl/.inr: evalUnOp succeeds for any v; no need to case-split on ht
  cases op
  case inl =>
    simp only [TinyML.UnOp.typeOf, Option.some.injEq] at hty; subst hty
    exact ⟨_, rfl, .inl ht⟩
  case inr =>
    simp only [TinyML.UnOp.typeOf, Option.some.injEq] at hty; subst hty
    exact ⟨_, rfl, .inr ht⟩
  -- Remaining ops require specific value shapes; eliminate incompatible ht branches via hty
  all_goals (cases ht <;>
    simp only [TinyML.UnOp.typeOf, TinyML.evalUnOp, Option.some.injEq] at * <;>
    first
    | (obtain rfl := hty; exact ⟨_, rfl, .int _⟩)
    | (obtain rfl := hty; exact ⟨_, rfl, .bool _⟩)
    | (obtain ⟨rfl, rfl⟩ := hty; exact ⟨_, rfl, ‹_›⟩)  -- fst.pair, snd.pair
    | simp_all)
