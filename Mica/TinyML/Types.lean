-- SUMMARY: TinyML types, type declarations, and subtyping structure.
import Mica.TinyML.Common

namespace TinyML

abbrev TyVar := String
abbrev TypeName := String

inductive Typ where
  | unit
  | bool
  | int
  | sum (ts : List Typ)
  | arrow (t1 t2 : Typ)
  | ref (t: Typ)
  | empty   -- bottom type (uninhabited)
  | value   -- top type (all runtime values)
  | tuple (ts : List Typ)
  | tvar (v : TyVar)
  | named (T : TypeName) (args : List Typ)
  deriving Repr

def Typ.decEq : (a b : Typ) → Decidable (a = b)
  | .unit, .unit | .bool, .bool | .int, .int | .empty, .empty | .value, .value => isTrue rfl
  | .sum ss, .sum ts => match typesDecEq ss ts with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .arrow s1 s2, .arrow t1 t2 =>
    match s1.decEq t1, s2.decEq t2 with
    | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
    | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
    | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .ref s, .ref t => match s.decEq t with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .tuple ss, .tuple ts => match typesDecEq ss ts with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .tvar v, .tvar w => match (inferInstance : DecidableEq TyVar) v w with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .named T args, .named U params =>
    match (inferInstance : DecidableEq TypeName) T U, typesDecEq args params with
    | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
    | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
    | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .unit, .bool | .unit, .int | .unit, .sum .. | .unit, .arrow ..
  | .unit, .ref .. | .unit, .empty | .unit, .value | .unit, .tuple ..
  | .unit, .tvar .. | .unit, .named ..
  | .bool, .unit | .bool, .int | .bool, .sum .. | .bool, .arrow ..
  | .bool, .ref .. | .bool, .empty | .bool, .value | .bool, .tuple ..
  | .bool, .tvar .. | .bool, .named ..
  | .int, .unit | .int, .bool | .int, .sum .. | .int, .arrow ..
  | .int, .ref .. | .int, .empty | .int, .value | .int, .tuple ..
  | .int, .tvar .. | .int, .named ..
  | .sum .., .unit | .sum .., .bool | .sum .., .int
  | .sum .., .arrow .. | .sum .., .ref .. | .sum .., .empty | .sum .., .value | .sum .., .tuple ..
  | .sum .., .tvar .. | .sum .., .named ..
  | .arrow .., .unit | .arrow .., .bool | .arrow .., .int
  | .arrow .., .sum .. | .arrow .., .ref .. | .arrow .., .empty | .arrow .., .value | .arrow .., .tuple ..
  | .arrow .., .tvar .. | .arrow .., .named ..
  | .ref .., .unit | .ref .., .bool | .ref .., .int
  | .ref .., .sum .. | .ref .., .arrow .. | .ref .., .empty | .ref .., .value | .ref .., .tuple ..
  | .ref .., .tvar .. | .ref .., .named ..
  | .empty, .unit | .empty, .bool | .empty, .int | .empty, .sum ..
  | .empty, .arrow .. | .empty, .ref .. | .empty, .value | .empty, .tuple ..
  | .empty, .tvar .. | .empty, .named ..
  | .value, .unit | .value, .bool | .value, .int | .value, .sum ..
  | .value, .arrow .. | .value, .ref .. | .value, .empty | .value, .tuple ..
  | .value, .tvar .. | .value, .named ..
  | .tuple .., .unit | .tuple .., .bool | .tuple .., .int
  | .tuple .., .sum .. | .tuple .., .arrow .. | .tuple .., .ref .. | .tuple .., .empty
  | .tuple .., .value | .tuple .., .tvar .. | .tuple .., .named ..
  | .tvar .., .unit | .tvar .., .bool | .tvar .., .int | .tvar .., .sum ..
  | .tvar .., .arrow .. | .tvar .., .ref .. | .tvar .., .empty | .tvar .., .value | .tvar .., .tuple ..
  | .tvar .., .named ..
  | .named .., .unit | .named .., .bool | .named .., .int | .named .., .sum ..
  | .named .., .arrow .. | .named .., .ref .. | .named .., .empty | .named .., .value | .named .., .tuple ..
  | .named .., .tvar .. => isFalse (by intro h; cases h)
where
  typesDecEq : (as bs : List Typ) → Decidable (as = bs)
    | [], [] => isTrue rfl
    | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
    | a :: as, b :: bs => match a.decEq b, typesDecEq as bs with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)

instance : DecidableEq Typ := Typ.decEq

instance : BEq Typ := ⟨fun a b => decide (a = b)⟩
instance : LawfulBEq Typ where
  eq_of_beq h := of_decide_eq_true h
  rfl := by simp [BEq.beq]

/--
Substitution over `Typ`.

This is currently structural-only scaffolding. It becomes meaningfully
variable-sensitive once `Typ` grows `tvar`/`named`.
-/
def Typ.subst (_σ : TyVar → Typ) : Typ → Typ
  | .unit => .unit
  | .bool => .bool
  | .int => .int
  | .sum ts => .sum (ts.map (Typ.subst _σ))
  | .arrow t1 t2 => .arrow (Typ.subst _σ t1) (Typ.subst _σ t2)
  | .ref t => .ref (Typ.subst _σ t)
  | .empty => .empty
  | .value => .value
  | .tuple ts => .tuple (ts.map (Typ.subst _σ))
  | .tvar v => _σ v
  | .named T args => .named T (args.map (Typ.subst _σ))

structure DataDecl where
  tparams : List TyVar
  payloads : List Typ
  deriving Repr, Inhabited, DecidableEq

abbrev TypeEnv := TypeName → Option DataDecl

def TypeEnv.empty : TypeEnv := fun _ => none

/--
Instantiation is also scaffolding for now: until `Typ` can contain type
variables, substitution has no observable effect.
-/
def DataDecl.instantiate (d : DataDecl) (args : List Typ) : Typ :=
  let σ := fun v =>
    match (d.tparams.zip args).find? (fun p => p.1 == v) with
    | some (_, ty) => ty
    | none => .tvar v
  .sum (d.payloads.map (Typ.subst σ))

def TypeName.unfold (Θ : TypeEnv) (T : TypeName) (args : List Typ) : Option Typ :=
  (Θ T).map (·.instantiate args)

/-! ## Weight and depth measures -/

mutual
  @[reducible]
  def Typ.weight : Typ → Nat
    | .unit | .bool | .int | .empty | .value | .tvar _ => 1
    | .sum ts => 1 + Typ.weights ts
    | .arrow t1 t2 => 1 + Typ.weight t1 + Typ.weight t2
    | .ref t => 1 + Typ.weight t
    | .tuple ts => 1 + Typ.weights ts
    | .named _ args => 1 + Typ.weights args

  @[reducible]
  def Typ.weights : List Typ → Nat
    | [] => 0
    | t :: ts => Typ.weight t + Typ.weights ts
end

mutual
  @[reducible]
  def Typ.depth : Typ → Nat
    | .unit | .bool | .int | .empty | .value | .tvar _ => 1
    | .sum ts => 1 + Typ.depths ts
    | .arrow t1 t2 => 1 + max (Typ.depth t1) (Typ.depth t2)
    | .ref t => 1 + Typ.depth t
    | .tuple ts => 1 + Typ.depths ts
    | .named _ args => 1 + Typ.depths args

  @[reducible]
  def Typ.depths : List Typ → Nat
    | [] => 0
    | t :: ts => max (Typ.depth t) (Typ.depths ts)
end

theorem Typ.weight_pos (t : Typ) : 0 < Typ.weight t := by
  cases t <;> simp [Typ.weight] <;> omega

theorem Typ.weight_pair_lt_sum (ss ts : List Typ) :
    1 + Typ.weights ss + Typ.weights ts < Typ.weight (.sum ss) + Typ.weight (.sum ts) := by
  simp [Typ.weight]

theorem Typ.weight_pair_lt_arrow_dom (s1 s2 t1 t2 : Typ) :
    Typ.weight t1 + Typ.weight s1 <
      Typ.weight (.arrow s1 s2) + Typ.weight (.arrow t1 t2) := by
  simp [Typ.weight]
  omega

theorem Typ.weight_pair_lt_arrow_codom (s1 s2 t1 t2 : Typ) :
    Typ.weight s2 + Typ.weight t2 <
      Typ.weight (.arrow s1 s2) + Typ.weight (.arrow t1 t2) := by
  simp [Typ.weight]
  omega

theorem Typ.weight_pair_lt_list_head (s : Typ) (ss : List Typ) (t : Typ) (ts : List Typ) :
    Typ.weight s + Typ.weight t < 1 + Typ.weights (s :: ss) + Typ.weights (t :: ts) := by
  simp [Typ.weights]
  omega

theorem Typ.weight_pair_lt_list_tail (s : Typ) (ss : List Typ) (t : Typ) (ts : List Typ) :
    1 + Typ.weights ss + Typ.weights ts < 1 + Typ.weights (s :: ss) + Typ.weights (t :: ts) := by
  have hs : 0 < Typ.weight s := Typ.weight_pos s
  have ht : 0 < Typ.weight t := Typ.weight_pos t
  simp [Typ.weights]
  omega

/-! ## Subtyping decision procedure -/

mutual

  def Typ.subBody (Θ : TypeEnv) (recur : Typ → Typ → Bool) : Typ → Typ → Bool :=
      fun s t =>
        match s, t with
        | .empty, _ => true
        | _, .value => true
        | .sum ss, .sum ts => Typ.subListBody Θ recur ss ts
        | .arrow s1 s2, .arrow t1 t2 =>
            Typ.subBody Θ recur t1 s1 && Typ.subBody Θ recur s2 t2
        | .tuple ss, .tuple ts => Typ.subListBody Θ recur ss ts
        | _, _ =>
            if s == t then true
            else match s, t with
              | .named T args, _ => match TypeName.unfold Θ T args with
                  | some s' => recur s' t
                  | none => false
              | _, .named T args => match TypeName.unfold Θ T args with
                  | some t' => recur s t'
                  | none => false
              | _, _ => false
  termination_by s t => Typ.weight s + Typ.weight t
  decreasing_by
    all_goals
      simp [Typ.weight]; try omega

  def Typ.subListBody (Θ : TypeEnv) (recur : Typ → Typ → Bool) : List Typ → List Typ → Bool
    | [], [] => true
    | s :: ss, t :: ts => Typ.subBody Θ recur s t && Typ.subListBody Θ recur ss ts
    | _, _ => false
  termination_by ss ts => 1 + Typ.weights ss + Typ.weights ts
  decreasing_by
    all_goals
      first
        | exact Typ.weight_pair_lt_list_head _ _ _ _
        | exact Typ.weight_pair_lt_list_tail _ _ _ _
end

def Typ.subi (Θ : TypeEnv) (steps : Nat) : Typ → Typ → Bool :=
  match steps with
  | 0 => fun _ _ => false
  | n + 1 => Typ.subBody Θ (Typ.subi Θ n)

def Typ.subListi (Θ : TypeEnv) (steps : Nat) : List Typ → List Typ → Bool :=
  match steps with
  | 0 => fun _ _ => false
  | n + 1 => Typ.subListBody Θ (Typ.subi Θ n)

def Typ.sub (Θ : TypeEnv) : Typ → Typ → Bool :=
  fun s t => Typ.subi Θ (max (Typ.depth s) (Typ.depth t)) s t

def Typ.subList (Θ : TypeEnv) : List Typ → List Typ → Bool :=
  fun ss ts => Typ.subListi Θ (max (Typ.depths ss) (Typ.depths ts)) ss ts

/-! ## Subtyping relation -/

mutual
  inductive Typ.Sub (Θ : TypeEnv) : Typ → Typ → Prop where
    | refl  : Typ.Sub Θ t t
    | bot   : Typ.Sub Θ .empty t
    | top   : Typ.Sub Θ t .value
    | trans : Typ.Sub Θ s t → Typ.Sub Θ t u → Typ.Sub Θ s u
    | sum   : Typ.SubList Θ ss ts
            → Typ.Sub Θ (.sum ss) (.sum ts)
    | arrow : Typ.Sub Θ t1 s1
            → Typ.Sub Θ s2 t2
            → Typ.Sub Θ (.arrow s1 s2) (.arrow t1 t2)
    | tuple : Typ.SubList Θ ss ts
            → Typ.Sub Θ (.tuple ss) (.tuple ts)
    | named_left : TypeName.unfold Θ T args = some ty
                 → Typ.Sub Θ ty t
                 → Typ.Sub Θ (.named T args) t
    | named_right : TypeName.unfold Θ T args = some ty
                  → Typ.Sub Θ s ty
                  → Typ.Sub Θ s (.named T args)

  inductive Typ.SubList (Θ : TypeEnv) : List Typ → List Typ → Prop where
    | nil  : Typ.SubList Θ [] []
    | cons : Typ.Sub Θ s t → Typ.SubList Θ ss ts → Typ.SubList Θ (s :: ss) (t :: ts)
end

theorem Typ.SubList.length_eq : Typ.SubList Θ ss ts → ss.length = ts.length
  | .nil => rfl
  | .cons _ h => by simp [List.length_cons, h.length_eq]

-- Forward direction: decision procedure is sound.
mutual
  private theorem Typ.subBody_sound {Θ : TypeEnv} {recur : Typ → Typ → Bool}
      (hrecur : ∀ {s t}, recur s t = true → Typ.Sub Θ s t)
      {s t : Typ} (h : Typ.subBody Θ recur s t = true) : Typ.Sub Θ s t := by
    unfold Typ.subBody at h
    split at h
    · exact .bot
    · exact .top
    · exact .sum (subListBody_sound hrecur h)
    · simp [Bool.and_eq_true] at h
      exact .arrow (subBody_sound hrecur h.1) (subBody_sound hrecur h.2)
    · exact .tuple (subListBody_sound hrecur h)
    · -- catchall: if s == t then true else match (s, t) for named
      split at h
      · -- s == t
        rename_i hbeq
        have heq : s = t := by simpa using hbeq
        subst heq; exact .refl
      · -- s ≠ t, check if either side is named
        split at h
        · -- s = .named T args
          rename_i T args hneq
          split at h
          · rename_i s' hunfold
            exact .named_left hunfold (hrecur h)
          · cases h
        · -- t = .named T args (s is not named)
          rename_i T args hneq
          split at h
          · rename_i t' hunfold
            exact .named_right hunfold (hrecur h)
          · cases h
        · -- neither named
          cases h
  termination_by Typ.weight s + Typ.weight t
  decreasing_by
    all_goals
      subst_vars
      try simp [Typ.weight]
      try omega

  private theorem Typ.subListBody_sound {Θ : TypeEnv} {recur : Typ → Typ → Bool}
      (hrecur : ∀ {s t}, recur s t = true → Typ.Sub Θ s t)
      {ss ts : List Typ}
      (h : Typ.subListBody Θ recur ss ts = true) : Typ.SubList Θ ss ts := by
    match ss, ts with
    | [], [] =>
        exact .nil
    | s :: ss, t :: ts =>
        simp [Typ.subListBody, Bool.and_eq_true] at h
        exact .cons (subBody_sound hrecur h.1) (subListBody_sound hrecur h.2)
    | [], _ :: _ | _ :: _, [] =>
        simp [Typ.subListBody] at h
  termination_by 1 + Typ.weights ss + Typ.weights ts
  decreasing_by
    all_goals
      first
        | exact Typ.weight_pair_lt_list_head _ _ _ _
        | exact Typ.weight_pair_lt_list_tail _ _ _ _

  private theorem Typ.subi_sound {Θ : TypeEnv} {steps : Nat} {s t : Typ}
      (h : Typ.subi Θ steps s t = true) : Typ.Sub Θ s t := by
    induction steps generalizing s t with
    | zero =>
      simp [Typ.subi] at h
    | succ n ih =>
      simpa [Typ.subi] using
        (Typ.subBody_sound (Θ := Θ) (recur := Typ.subi Θ n) (hrecur := fun {s t} h => ih h) h)

  private theorem Typ.subListi_sound {Θ : TypeEnv} {steps : Nat}
      {ss ts : List Typ} (h : Typ.subListi Θ steps ss ts = true) : Typ.SubList Θ ss ts := by
    induction steps generalizing ss ts with
    | zero =>
      simp [Typ.subListi] at h
    | succ n ih =>
      simpa [Typ.subListi] using
        (Typ.subListBody_sound (Θ := Θ) (recur := Typ.subi Θ n) (hrecur := fun {s t} h => Typ.subi_sound h) h)
end

theorem Typ.sub_sound {Θ : TypeEnv} {s t : Typ}
    (h : Typ.sub Θ s t = true) : Typ.Sub Θ s t := by
  exact Typ.subi_sound (Θ := Θ) (steps := max (Typ.depth s) (Typ.depth t)) h

theorem Typ.subList_sound {Θ : TypeEnv} {ss ts : List Typ}
    (h : Typ.subList Θ ss ts = true) : Typ.SubList Θ ss ts := by
  exact Typ.subListi_sound (Θ := Θ) (steps := max (Typ.depths ss) (Typ.depths ts)) h

/-! ## Join and meet -/

mutual
  def Typ.join (Θ : TypeEnv) : Typ → Typ → Typ
    | .empty, t | t, .empty => t
    | .value, _ | _, .value => .value
    | .sum  ss,     .sum  ts     => if ss.length == ts.length
                                    then .sum (Typ.joinList Θ ss ts)
                                    else .value
    | .arrow s1 s2, .arrow t1 t2 => .arrow (Typ.meet Θ s1 t1) (Typ.join Θ s2 t2)
    | .ref s,       .ref t       => if s == t then .ref s else .value
    | .tuple ss,    .tuple ts    => if ss.length == ts.length
                                    then .tuple (Typ.joinList Θ ss ts)
                                    else .value
    | s, t =>
        if Typ.sub Θ s t then t
        else if Typ.sub Θ t s then s
        else .value

  def Typ.meet (Θ : TypeEnv) : Typ → Typ → Typ
    | .value, t | t, .value => t
    | .empty, _ | _, .empty => .empty
    | .sum  ss,     .sum  ts     => if ss.length == ts.length
                                    then .sum (Typ.meetList Θ ss ts)
                                    else .empty
    | .arrow s1 s2, .arrow t1 t2 => .arrow (Typ.join Θ s1 t1) (Typ.meet Θ s2 t2)
    | .ref s,       .ref t       => if s == t then .ref s else .empty
    | .tuple ss,    .tuple ts    => if ss.length == ts.length
                                    then .tuple (Typ.meetList Θ ss ts)
                                    else .empty
    | s, t =>
        if Typ.sub Θ s t then s
        else if Typ.sub Θ t s then t
        else .empty

  def Typ.joinList (Θ : TypeEnv) : List Typ → List Typ → List Typ
    | s :: ss, t :: ts => Typ.join Θ s t :: Typ.joinList Θ ss ts
    | _, _             => []

  def Typ.meetList (Θ : TypeEnv) : List Typ → List Typ → List Typ
    | s :: ss, t :: ts => Typ.meet Θ s t :: Typ.meetList Θ ss ts
    | _, _             => []
end

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

end TinyML
