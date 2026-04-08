import Mica.TinyML.Expr
import Mica.TinyML.RuntimeExpr
import Mica.TinyML.OpSem

namespace TinyML

/-! ## Type contexts -/

abbrev TyCtx := Var → Option Typ

def TyCtx.empty : TyCtx := fun _ => none

def TyCtx.extend (Γ : TyCtx) (x : Var) (t : Typ) : TyCtx :=
  fun y => if y == x then some t else Γ y

def TyCtx.extendBinder (Γ : TyCtx) (b : Binder) (t : Typ) : TyCtx :=
  match b with
  | .none      => Γ
  | .named x _ => Γ.extend x t

@[simp] theorem TyCtx.extend_eq (Γ : TyCtx) (x : Var) (t : Typ) :
    (Γ.extend x t) x = some t := by simp [TyCtx.extend]

@[simp] theorem TyCtx.extend_ne (Γ : TyCtx) (x y : Var) (t : Typ) (h : y ≠ x) :
    (Γ.extend x t) y = Γ y := by
  simp [TyCtx.extend, h]

/-- Γ ≤ Γ': Γ' extends Γ pointwise. -/
def TyCtx.le (Γ Γ' : TyCtx) : Prop := ∀ x t, Γ x = some t → Γ' x = some t

instance : LE TyCtx := ⟨TyCtx.le⟩

theorem TyCtx.le_refl (Γ : TyCtx) : Γ ≤ Γ := fun _ _ h => h

theorem TyCtx.le_trans {Γ₁ Γ₂ Γ₃ : TyCtx} (h12 : Γ₁ ≤ Γ₂) (h23 : Γ₂ ≤ Γ₃) : Γ₁ ≤ Γ₃ :=
  fun x t h => h23 x t (h12 x t h)

/-- Monotonicity of `extendBinder` w.r.t. context ordering. -/
theorem TyCtx.le_extendBinder_congr {Γ Γ' : TyCtx} (b : Binder) (t : Typ)
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
    (args : List (Var × Typ)) (Γ : TyCtx) (x : Var)
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
  inductive Typ.Sub : Typ → Typ → Prop where
    | refl  : Typ.Sub t t
    | bot   : Typ.Sub (Typ.empty) t
    | top   : Typ.Sub t (Typ.value)
    | trans : Typ.Sub s t → Typ.Sub t u → Typ.Sub s u
    | sum   : Typ.SubList ss ts
            → Typ.Sub (Typ.sum ss) (Typ.sum ts)
    | arrow : Typ.Sub t1 s1 → Typ.Sub s2 t2
            → Typ.Sub (Typ.arrow s1 s2) (Typ.arrow t1 t2)
    | tuple : Typ.SubList ss ts
            → Typ.Sub (Typ.tuple ss) (Typ.tuple ts)

  inductive Typ.SubList : List Typ → List Typ → Prop where
    | nil  : Typ.SubList [] []
    | cons : Typ.Sub s t → Typ.SubList ss ts → Typ.SubList (s :: ss) (t :: ts)
end

theorem Typ.SubList.length_eq : Typ.SubList ss ts → ss.length = ts.length
  | .nil => rfl
  | .cons _ h => by simp [List.length_cons, h.length_eq]

mutual
  def Typ.join : Typ → Typ → Typ
    | .empty, t | t, .empty => t
    | .value, _ | _, .value => .value
    | .sum  ss,     .sum  ts     => if ss.length == ts.length
                                    then .sum (Typ.joinList ss ts)
                                    else .value
    | .arrow s1 s2, .arrow t1 t2 => .arrow (Typ.meet s1 t1) (Typ.join s2 t2)
    | .ref s,       .ref t       => if s == t then .ref s else .value
    | .tuple ss,    .tuple ts    => if ss.length == ts.length
                                    then .tuple (Typ.joinList ss ts)
                                    else .value
    | t, t'                      => if t == t' then t else .value

  def Typ.meet : Typ → Typ → Typ
    | .value, t | t, .value => t
    | .empty, _ | _, .empty => .empty
    | .sum  ss,     .sum  ts     => if ss.length == ts.length
                                    then .sum (Typ.meetList ss ts)
                                    else .empty
    | .arrow s1 s2, .arrow t1 t2 => .arrow (Typ.join s1 t1) (Typ.meet s2 t2)
    | .ref s,       .ref t       => if s == t then .ref s else .empty
    | .tuple ss,    .tuple ts    => if ss.length == ts.length
                                    then .tuple (Typ.meetList ss ts)
                                    else .empty
    | t, t'                      => if t == t' then t else .empty

  def Typ.joinList : List Typ → List Typ → List Typ
    | s :: ss, t :: ts => Typ.join s t :: Typ.joinList ss ts
    | _, _             => []

  def Typ.meetList : List Typ → List Typ → List Typ
    | s :: ss, t :: ts => Typ.meet s t :: Typ.meetList ss ts
    | _, _             => []
end

mutual
  def Typ.sub (s t : Typ) : Bool :=
    match s, t with
    | .empty, _      => true
    | _, .value      => true
    | .sum  ss,     .sum  ts     => Typ.subList ss ts
    | .arrow s1 s2, .arrow t1 t2 => Typ.sub t1 s1 && Typ.sub s2 t2
    | .tuple ss,    .tuple ts    => Typ.subList ss ts
    | t, t'                      => t == t'
  termination_by sizeOf s + sizeOf t
  decreasing_by all_goals simp +arith [*]

  def Typ.subList (ss ts : List Typ) : Bool :=
    match ss, ts with
    | [], [] => true
    | s :: ss, t :: ts => Typ.sub s t && Typ.subList ss ts
    | _, _ => false
  termination_by sizeOf ss + sizeOf ts
  decreasing_by all_goals simp +arith [*]
end

-- Forward direction: decision procedure is sound.
mutual
  private theorem Typ.sub_sound {s t : Typ} (h : Typ.sub s t = true) : Typ.Sub s t := by
    cases s with
    | empty => exact .bot
    | sum ss =>
        cases t with
        | value => exact .top
        | sum ts =>
            simp [Typ.sub] at h
            exact .sum (subList_sound h)
        | _ => exact absurd h (by simp [Typ.sub])
    | arrow s1 s2 =>
        cases t with
        | value => exact .top
        | arrow t1 t2 =>
            simp [Typ.sub, Bool.and_eq_true] at h
            exact .arrow (sub_sound h.1) (sub_sound h.2)
        | _ => exact absurd h (by simp [Typ.sub])
    | tuple ss =>
        cases t with
        | value => exact .top
        | tuple ts =>
            simp [Typ.sub] at h
            exact .tuple (subList_sound h)
        | _ => exact absurd h (by simp [Typ.sub])
    | _ =>
        cases t with
        | value => exact .top
        | _ => simp_all [Typ.sub] <;> exact .refl
  termination_by sizeOf s + sizeOf t
  decreasing_by all_goals simp +arith [*]

  private theorem Typ.subList_sound {ss ts : List Typ}
      (h : Typ.subList ss ts = true) : Typ.SubList ss ts := by
    match ss, ts with
    | [], [] => exact .nil
    | [], _ :: _ | _ :: _, [] => simp [Typ.subList] at h
    | s :: ss, t :: ts =>
      simp [Typ.subList, Bool.and_eq_true] at h
      exact .cons (sub_sound h.1) (subList_sound h.2)
  termination_by sizeOf ss + sizeOf ts
  decreasing_by all_goals simp +arith [*]
end

-- Reflexivity of the decision procedure (needed for completeness)
mutual
  private theorem Typ.sub_refl : ∀ (t : Typ), Typ.sub t t = true
    | .unit | .bool | .int | .empty | .value => by simp [Typ.sub]
    | .sum  ts     => by simp [Typ.sub, subList_refl ts]
    | .arrow t1 t2 => by simp [Typ.sub, sub_refl t1, sub_refl t2]
    | .ref t       => by simp [Typ.sub]
    | .tuple ts    => by simp [Typ.sub, subList_refl ts]

  private theorem Typ.subList_refl : ∀ (ts : List Typ), Typ.subList ts ts = true
    | [] => by simp [Typ.subList]
    | t :: ts => by simp [Typ.subList, sub_refl t, subList_refl ts]
end

-- Transitivity of the decision procedure (needed for completeness of trans rule).
-- Proved by recursion on t (the middle type).
mutual
  private theorem Typ.sub_trans {s t u : Typ}
      (h1 : Typ.sub s t = true) (h2 : Typ.sub t u = true) :
      Typ.sub s u = true := by
    match t with
    | .empty | .value | .unit | .bool | .int => cases s <;> cases u <;> simp_all [Typ.sub, beq_iff_eq]
    | .ref _ => cases s <;> cases u <;> simp_all [Typ.sub, beq_iff_eq]
    | .sum ts =>
        cases s with
        | empty => simp [Typ.sub]
        | sum ss =>
            cases u with
            | value => simp [Typ.sub]
            | sum us =>
                simp [Typ.sub] at h1 h2 ⊢
                exact subList_trans h1 h2
            | _ => simp [Typ.sub] at h2
        | _ => simp [Typ.sub] at h1
    | .arrow t1 t2 =>
        cases s with
        | empty => simp [Typ.sub]
        | arrow ss1 ss2 =>
            cases u with
            | value => simp [Typ.sub]
            | arrow u1 u2 =>
                simp [Typ.sub, Bool.and_eq_true] at h1 h2 ⊢
                exact ⟨sub_trans h2.1 h1.1, sub_trans h1.2 h2.2⟩
            | _ => simp [Typ.sub] at h2
        | _ => simp [Typ.sub] at h1
    | .tuple ts =>
        cases s with
        | empty => simp [Typ.sub]
        | tuple ss =>
            cases u with
            | value => simp [Typ.sub]
            | tuple us =>
                simp [Typ.sub] at h1 h2 ⊢
                exact subList_trans h1 h2
            | _ => simp [Typ.sub] at h2
        | _ => simp [Typ.sub] at h1
  termination_by sizeOf t
  decreasing_by all_goals simp +arith [*]

  private theorem Typ.subList_trans {ss ts us : List Typ}
      (h1 : Typ.subList ss ts = true) (h2 : Typ.subList ts us = true) :
      Typ.subList ss us = true := by
    match ss, ts, us with
    | [], [], [] => simp [Typ.subList]
    | [], [], _ :: _ => simp [Typ.subList] at h2
    | [], _ :: _, _ | _ :: _, [], _ => simp [Typ.subList] at h1
    | _ :: _, _ :: _, [] => simp [Typ.subList] at h2
    | s :: ss, t :: ts, u :: us =>
      simp [Typ.subList, Bool.and_eq_true] at h1 h2 ⊢
      exact ⟨sub_trans h1.1 h2.1, subList_trans h1.2 h2.2⟩
  termination_by sizeOf ts
  decreasing_by all_goals simp +arith [*]
end

-- Backward direction: derivable subtyping is decided
mutual
  private theorem Typ.Sub_complete {s t : Typ} (p : Typ.Sub s t) : Typ.sub s t = true := by
    match p with
    | .refl        => exact sub_refl _
    | .bot         => cases t <;> simp [Typ.sub]
    | .top         => cases s <;> simp [Typ.sub]
    | .trans h1 h2 => exact sub_trans (Sub_complete h1) (Sub_complete h2)
    | .sum  h      => simp [Typ.sub, SubList_complete h]
    | .arrow h1 h2 => simp [Typ.sub, Sub_complete h1, Sub_complete h2]
    | .tuple h     => simp [Typ.sub]; exact SubList_complete h

  private theorem Typ.SubList_complete {ss ts : List Typ}
      (ps : Typ.SubList ss ts) : Typ.subList ss ts = true := by
    match ps with
    | .nil => simp [Typ.subList]
    | .cons h hs => simp [Typ.subList, Sub_complete h, SubList_complete hs]
end

theorem Typ.sub_iff {s t : Typ} : Typ.sub s t = true ↔ Typ.Sub s t :=
  ⟨sub_sound, Sub_complete⟩

/-! ## Operator typing -/

def BinOp.typeOf : BinOp → Typ → Typ → Option Typ
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

def UnOp.typeOf : UnOp → Typ → Option Typ
  | .neg, .int       => some .int
  | .not, .bool      => some .bool
  | .proj n, .tuple ts => ts[n]?
  | _, _             => none

mutual
  inductive ValHasType : Runtime.Val → Typ → Prop where
    | int  (n : Int)  : ValHasType (.int n)  .int
    | bool (b : Bool) : ValHasType (.bool b) .bool
    | unit            : ValHasType .unit      .unit
    | inj  : (ht : ts[tag]? = some t)
            → ValHasType payload t
            → ValHasType (.inj tag ts.length payload) (.sum ts)
    | tuple : ValsHaveTypes vs ts
            → ValHasType (Runtime.Val.tuple vs) (Typ.tuple ts)
    -- Any value has type .value
    | any : ValHasType v .value

  inductive ValsHaveTypes : List Runtime.Val → List Typ → Prop where
    | nil  : ValsHaveTypes [] []
    | cons : ValHasType v t → ValsHaveTypes vs ts → ValsHaveTypes (v :: vs) (t :: ts)
end


mutual
  theorem ValHasType_sub {v : Runtime.Val} {t t' : Typ} (h : ValHasType v t) (hsub : Typ.Sub t t') :
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

  theorem ValsHaveTypes_sub {vs : List Runtime.Val} {ts ts' : List Typ}
      (h : ValsHaveTypes vs ts) (hsub : Typ.SubList ts ts') :
      ValsHaveTypes vs ts' := by
    match hsub with
    | .nil => cases h; exact .nil
    | .cons hs hss =>
      cases h with
      | cons hv hvs => exact .cons (ValHasType_sub hv hs) (ValsHaveTypes_sub hvs hss)

  /-- Lift a payload through a `SubList`: if `ss[tag]? = some s` and `payload : s`,
      find `ts[tag]? = some t` and produce `ValHasType payload t`. -/
  theorem ValHasType_subList {payload : Runtime.Val} {s : Typ} {ss ts : List Typ}
      (hpayload : ValHasType payload s) (hlist : Typ.SubList ss ts)
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
theorem evalBinOp_typed {op : TinyML.BinOp} {v1 v2 : Runtime.Val} {t1 t2 ty : TinyML.Typ}
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

private theorem evalUnOp_proj_typed {n : Nat} {vs : List Runtime.Val} {ts : List TinyML.Typ} {ty : TinyML.Typ}
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

theorem evalUnOp_typed {op : TinyML.UnOp} {v : Runtime.Val} {t ty : TinyML.Typ}
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
