import Mica.TinyML.Expr
import Mica.TinyML.RuntimeExpr
import Mica.TinyML.OpSem

namespace TinyML

/-! ## Type contexts -/

abbrev TyCtx := Var → Option Type_

def TyCtx.empty : TyCtx := fun _ => none

def TyCtx.extend (Γ : TyCtx) (x : Var) (t : Type_) : TyCtx :=
  fun y => if y == x then some t else Γ y

def TyCtx.extendBinder (Γ : TyCtx) (b : Binder) (t : Type_) : TyCtx :=
  match b with
  | .none      => Γ
  | .named x _ => Γ.extend x t

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
  | named x _ =>
    simp only [TyCtx.extendBinder, TyCtx.extend] at hy ⊢
    by_cases h : y == x
    · simp [h] at hy ⊢; exact hy
    · simp [h] at hy ⊢; exact hle y ty hy

-- foldl extend doesn't change the value at x if x doesn't appear in the list.
theorem TyCtx.foldl_extend_stable
    (args : List (Var × Type_)) (Γ : TyCtx) (x : Var)
    (hx : ∀ a ∈ args, a.1 ≠ x) :
    (args.foldl (fun ctx a => ctx.extend a.1 a.2) Γ) x = Γ x := by
  induction args generalizing Γ with
  | nil => rfl
  | cons a as ih =>
    simp only [List.foldl_cons]
    have := ih (Γ.extend a.1 a.2) (fun a' ha' => hx a' (.tail _ ha'))
    rw [this]
    have hne := hx a (.head _)
    simp [TyCtx.extend, beq_iff_eq, Ne.symm hne]

/-! ## Subtyping -/

mutual
  inductive Type_.Sub : Type_ → Type_ → Prop where
    | refl  : Type_.Sub t t
    | bot   : Type_.Sub (Type_.empty) t
    | top   : Type_.Sub t (Type_.value)
    | trans : Type_.Sub s t → Type_.Sub t u → Type_.Sub s u
    | sum   : Type_.SubList ss ts
            → Type_.Sub (Type_.sum ss) (Type_.sum ts)
    | arrow : Type_.Sub t1 s1 → Type_.Sub s2 t2
            → Type_.Sub (Type_.arrow s1 s2) (Type_.arrow t1 t2)
    | tuple : Type_.SubList ss ts
            → Type_.Sub (Type_.tuple ss) (Type_.tuple ts)

  inductive Type_.SubList : List Type_ → List Type_ → Prop where
    | nil  : Type_.SubList [] []
    | cons : Type_.Sub s t → Type_.SubList ss ts → Type_.SubList (s :: ss) (t :: ts)
end

theorem Type_.SubList.length_eq : Type_.SubList ss ts → ss.length = ts.length
  | .nil => rfl
  | .cons _ h => by simp [List.length_cons, h.length_eq]

mutual
  def Type_.join : Type_ → Type_ → Type_
    | .empty, t | t, .empty => t
    | .value, _ | _, .value => .value
    | .sum  ss,     .sum  ts     => if ss.length == ts.length
                                    then .sum (Type_.joinList ss ts)
                                    else .value
    | .arrow s1 s2, .arrow t1 t2 => .arrow (Type_.meet s1 t1) (Type_.join s2 t2)
    | .ref s,       .ref t       => if s == t then .ref s else .value
    | .tuple ss,    .tuple ts    => if ss.length == ts.length
                                    then .tuple (Type_.joinList ss ts)
                                    else .value
    | t, t'                      => if t == t' then t else .value

  def Type_.meet : Type_ → Type_ → Type_
    | .value, t | t, .value => t
    | .empty, _ | _, .empty => .empty
    | .sum  ss,     .sum  ts     => if ss.length == ts.length
                                    then .sum (Type_.meetList ss ts)
                                    else .empty
    | .arrow s1 s2, .arrow t1 t2 => .arrow (Type_.join s1 t1) (Type_.meet s2 t2)
    | .ref s,       .ref t       => if s == t then .ref s else .empty
    | .tuple ss,    .tuple ts    => if ss.length == ts.length
                                    then .tuple (Type_.meetList ss ts)
                                    else .empty
    | t, t'                      => if t == t' then t else .empty

  def Type_.joinList : List Type_ → List Type_ → List Type_
    | s :: ss, t :: ts => Type_.join s t :: Type_.joinList ss ts
    | _, _             => []

  def Type_.meetList : List Type_ → List Type_ → List Type_
    | s :: ss, t :: ts => Type_.meet s t :: Type_.meetList ss ts
    | _, _             => []
end

mutual
  def Type_.sub (s t : Type_) : Bool :=
    match s, t with
    | .empty, _      => true
    | _, .value      => true
    | .sum  ss,     .sum  ts     => Type_.subList ss ts
    | .arrow s1 s2, .arrow t1 t2 => Type_.sub t1 s1 && Type_.sub s2 t2
    | .tuple ss,    .tuple ts    => Type_.subList ss ts
    | t, t'                      => t == t'
  termination_by sizeOf s + sizeOf t
  decreasing_by all_goals simp +arith [*]

  def Type_.subList (ss ts : List Type_) : Bool :=
    match ss, ts with
    | [], [] => true
    | s :: ss, t :: ts => Type_.sub s t && Type_.subList ss ts
    | _, _ => false
  termination_by sizeOf ss + sizeOf ts
  decreasing_by all_goals simp +arith [*]
end

-- Forward direction: decision procedure is sound.
mutual
  private theorem Type_.sub_sound {s t : Type_} (h : Type_.sub s t = true) : Type_.Sub s t := by
    cases s with
    | empty => exact .bot
    | sum ss =>
        cases t with
        | value => exact .top
        | sum ts =>
            simp [Type_.sub] at h
            exact .sum (subList_sound h)
        | _ => exact absurd h (by simp [Type_.sub])
    | arrow s1 s2 =>
        cases t with
        | value => exact .top
        | arrow t1 t2 =>
            simp [Type_.sub, Bool.and_eq_true] at h
            exact .arrow (sub_sound h.1) (sub_sound h.2)
        | _ => exact absurd h (by simp [Type_.sub])
    | tuple ss =>
        cases t with
        | value => exact .top
        | tuple ts =>
            simp [Type_.sub] at h
            exact .tuple (subList_sound h)
        | _ => exact absurd h (by simp [Type_.sub])
    | _ =>
        cases t with
        | value => exact .top
        | _ => simp_all [Type_.sub] <;> exact .refl
  termination_by sizeOf s + sizeOf t
  decreasing_by all_goals simp +arith [*]

  private theorem Type_.subList_sound {ss ts : List Type_}
      (h : Type_.subList ss ts = true) : Type_.SubList ss ts := by
    match ss, ts with
    | [], [] => exact .nil
    | [], _ :: _ | _ :: _, [] => simp [Type_.subList] at h
    | s :: ss, t :: ts =>
      simp [Type_.subList, Bool.and_eq_true] at h
      exact .cons (sub_sound h.1) (subList_sound h.2)
  termination_by sizeOf ss + sizeOf ts
  decreasing_by all_goals simp +arith [*]
end

-- Reflexivity of the decision procedure (needed for completeness)
mutual
  private theorem Type_.sub_refl : ∀ (t : Type_), Type_.sub t t = true
    | .unit | .bool | .int | .empty | .value => by simp [Type_.sub]
    | .sum  ts     => by simp [Type_.sub, subList_refl ts]
    | .arrow t1 t2 => by simp [Type_.sub, sub_refl t1, sub_refl t2]
    | .ref t       => by simp [Type_.sub]
    | .tuple ts    => by simp [Type_.sub, subList_refl ts]

  private theorem Type_.subList_refl : ∀ (ts : List Type_), Type_.subList ts ts = true
    | [] => by simp [Type_.subList]
    | t :: ts => by simp [Type_.subList, sub_refl t, subList_refl ts]
end

-- Transitivity of the decision procedure (needed for completeness of trans rule).
-- Proved by recursion on t (the middle type).
mutual
  private theorem Type_.sub_trans {s t u : Type_}
      (h1 : Type_.sub s t = true) (h2 : Type_.sub t u = true) :
      Type_.sub s u = true := by
    match t with
    | .empty | .value | .unit | .bool | .int => cases s <;> cases u <;> simp_all [Type_.sub, beq_iff_eq]
    | .ref _ => cases s <;> cases u <;> simp_all [Type_.sub, beq_iff_eq]
    | .sum ts =>
        cases s with
        | empty => simp [Type_.sub]
        | sum ss =>
            cases u with
            | value => simp [Type_.sub]
            | sum us =>
                simp [Type_.sub] at h1 h2 ⊢
                exact subList_trans h1 h2
            | _ => simp [Type_.sub] at h2
        | _ => simp [Type_.sub] at h1
    | .arrow t1 t2 =>
        cases s with
        | empty => simp [Type_.sub]
        | arrow ss1 ss2 =>
            cases u with
            | value => simp [Type_.sub]
            | arrow u1 u2 =>
                simp [Type_.sub, Bool.and_eq_true] at h1 h2 ⊢
                exact ⟨sub_trans h2.1 h1.1, sub_trans h1.2 h2.2⟩
            | _ => simp [Type_.sub] at h2
        | _ => simp [Type_.sub] at h1
    | .tuple ts =>
        cases s with
        | empty => simp [Type_.sub]
        | tuple ss =>
            cases u with
            | value => simp [Type_.sub]
            | tuple us =>
                simp [Type_.sub] at h1 h2 ⊢
                exact subList_trans h1 h2
            | _ => simp [Type_.sub] at h2
        | _ => simp [Type_.sub] at h1
  termination_by sizeOf t
  decreasing_by all_goals simp +arith [*]

  private theorem Type_.subList_trans {ss ts us : List Type_}
      (h1 : Type_.subList ss ts = true) (h2 : Type_.subList ts us = true) :
      Type_.subList ss us = true := by
    match ss, ts, us with
    | [], [], [] => simp [Type_.subList]
    | [], [], _ :: _ => simp [Type_.subList] at h2
    | [], _ :: _, _ | _ :: _, [], _ => simp [Type_.subList] at h1
    | _ :: _, _ :: _, [] => simp [Type_.subList] at h2
    | s :: ss, t :: ts, u :: us =>
      simp [Type_.subList, Bool.and_eq_true] at h1 h2 ⊢
      exact ⟨sub_trans h1.1 h2.1, subList_trans h1.2 h2.2⟩
  termination_by sizeOf ts
  decreasing_by all_goals simp +arith [*]
end

-- Backward direction: derivable subtyping is decided
mutual
  private theorem Type_.Sub_complete {s t : Type_} (p : Type_.Sub s t) : Type_.sub s t = true := by
    match p with
    | .refl        => exact sub_refl _
    | .bot         => cases t <;> simp [Type_.sub]
    | .top         => cases s <;> simp [Type_.sub]
    | .trans h1 h2 => exact sub_trans (Sub_complete h1) (Sub_complete h2)
    | .sum  h      => simp [Type_.sub, SubList_complete h]
    | .arrow h1 h2 => simp [Type_.sub, Sub_complete h1, Sub_complete h2]
    | .tuple h     => simp [Type_.sub]; exact SubList_complete h

  private theorem Type_.SubList_complete {ss ts : List Type_}
      (ps : Type_.SubList ss ts) : Type_.subList ss ts = true := by
    match ps with
    | .nil => simp [Type_.subList]
    | .cons h hs => simp [Type_.subList, Sub_complete h, SubList_complete hs]
end

theorem Type_.sub_iff {s t : Type_} : Type_.sub s t = true ↔ Type_.Sub s t :=
  ⟨sub_sound, Sub_complete⟩

/-! ## Operator typing -/

def BinOp.typeOf : BinOp → Type_ → Type_ → Option Type_
  | .add,  .int,  .int  => some .int
  | .sub,  .int,  .int  => some .int
  | .mul,  .int,  .int  => some .int
  | .div,  .int,  .int  => some .int
  | .mod,  .int,  .int  => some .int
  | .eq,   .int,  .int  => some .bool
  | .lt,   .int,  .int  => some .bool
  | .le,   .int,  .int  => some .bool
  | .gt,   .int,  .int  => some .bool
  | .ge,   .int,  .int  => some .bool
  | .and,  .bool, .bool => some .bool
  | .or,   .bool, .bool => some .bool
  | _, _, _             => none

def UnOp.typeOf : UnOp → Type_ → Option Type_
  | .neg, .int       => some .int
  | .not, .bool      => some .bool
  | .proj n, .tuple ts => ts[n]?
  | _, _             => none

mutual
  inductive ValHasType : Runtime.Val → Type_ → Prop where
    | int  (n : Int)  : ValHasType (.int n)  .int
    | bool (b : Bool) : ValHasType (.bool b) .bool
    | unit            : ValHasType .unit      .unit
    | inj  : (ht : ts[tag]? = some t)
            → ValHasType payload t
            → ValHasType (.inj tag ts.length payload) (.sum ts)
    | tuple : ValsHaveTypes vs ts
            → ValHasType (Runtime.Val.tuple vs) (Type_.tuple ts)
    -- Any value has type .value
    | any : ValHasType v .value

  inductive ValsHaveTypes : List Runtime.Val → List Type_ → Prop where
    | nil  : ValsHaveTypes [] []
    | cons : ValHasType v t → ValsHaveTypes vs ts → ValsHaveTypes (v :: vs) (t :: ts)
end


mutual
  theorem ValHasType_sub {v : Runtime.Val} {t t' : Type_} (h : ValHasType v t) (hsub : Type_.Sub t t') :
      ValHasType v t' := by
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

  theorem ValsHaveTypes_sub {vs : List Runtime.Val} {ts ts' : List Type_}
      (h : ValsHaveTypes vs ts) (hsub : Type_.SubList ts ts') :
      ValsHaveTypes vs ts' := by
    match hsub with
    | .nil => cases h; exact .nil
    | .cons hs hss =>
      cases h with
      | cons hv hvs => exact .cons (ValHasType_sub hv hs) (ValsHaveTypes_sub hvs hss)

  /-- Lift a payload through a `SubList`: if `ss[tag]? = some s` and `payload : s`,
      find `ts[tag]? = some t` and produce `ValHasType payload t`. -/
  theorem ValHasType_subList {payload : Runtime.Val} {s : Type_} {ss ts : List Type_}
      (hpayload : ValHasType payload s) (hlist : Type_.SubList ss ts)
      {tag : Nat} (hs : ss[tag]? = some s) :
      ∃ t, ts[tag]? = some t ∧ ValHasType payload t :=
    match hlist, tag with
    | .nil, _ => absurd hs (by simp)
    | .cons hsub _, 0 => by simp at hs; exact ⟨_, rfl, ValHasType_sub (hs ▸ hpayload) hsub⟩
    | .cons _ hss, n + 1 => ValHasType_subList hpayload hss (by simpa using hs)
end

theorem ValsHaveTypes.length_eq : ValsHaveTypes vs ts → vs.length = ts.length
  | .nil => rfl
  | .cons _ h => congrArg (· + 1) h.length_eq

end TinyML



/-- Type preservation for `evalBinOp`: if the inputs are well-typed, the operation returns
    `some w` for a well-typed result `w`. -/
theorem evalBinOp_typed {op : TinyML.BinOp} {v1 v2 : Runtime.Val} {t1 t2 ty : TinyML.Type_}
    (hndiv : op ≠ .div) (hnmod : op ≠ .mod)
    (hty : TinyML.BinOp.typeOf op t1 t2 = some ty)
    (ht1 : TinyML.ValHasType v1 t1)
    (ht2 : TinyML.ValHasType v2 t2) :
    ∃ w, TinyML.evalBinOp op v1 v2 = some w ∧ TinyML.ValHasType w ty := by
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

private theorem evalUnOp_proj_typed {n : Nat} {vs : List Runtime.Val} {ts : List TinyML.Type_} {ty : TinyML.Type_}
    (hty : ts[n]? = some ty) (hvs : TinyML.ValsHaveTypes vs ts) :
    ∃ w, vs[n]? = some w ∧ TinyML.ValHasType w ty := by
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

theorem evalUnOp_typed {op : TinyML.UnOp} {v : Runtime.Val} {t ty : TinyML.Type_}
    (hty : TinyML.UnOp.typeOf op t = some ty)
    (ht : TinyML.ValHasType v t) :
    ∃ w, TinyML.evalUnOp op v = some w ∧ TinyML.ValHasType w ty := by
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
