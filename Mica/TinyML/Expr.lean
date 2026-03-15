namespace TinyML

abbrev Var := String
abbrev Location := Nat

inductive Binder where
  | none
  | named (name : Var)
  deriving Repr, BEq, Inhabited, DecidableEq

instance : LawfulBEq Binder where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> simp_all [BEq.beq, instBEqBinder.beq]
  rfl {a} := by
    cases a <;> simp [BEq.beq, instBEqBinder.beq]

inductive Type_ where
  | unit
  | bool
  | int
  | prod (t1 t2 : Type_)
  | sum (t1 t2 : Type_)
  | arrow (t1 t2 : Type_)
  | ref (t: Type_)
  | empty   -- bottom type (uninhabited)
  | value   -- top type (all runtime values)
  | tuple (ts : List Type_)
  deriving Repr

def Type_.decEq : (a b : Type_) → Decidable (a = b)
  | .unit, .unit | .bool, .bool | .int, .int | .empty, .empty | .value, .value => isTrue rfl
  | .prod s1 s2, .prod t1 t2 | .sum s1 s2, .sum t1 t2 | .arrow s1 s2, .arrow t1 t2 =>
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
  | .unit, .bool | .unit, .int | .unit, .prod .. | .unit, .sum .. | .unit, .arrow ..
  | .unit, .ref .. | .unit, .empty | .unit, .value | .unit, .tuple ..
  | .bool, .unit | .bool, .int | .bool, .prod .. | .bool, .sum .. | .bool, .arrow ..
  | .bool, .ref .. | .bool, .empty | .bool, .value | .bool, .tuple ..
  | .int, .unit | .int, .bool | .int, .prod .. | .int, .sum .. | .int, .arrow ..
  | .int, .ref .. | .int, .empty | .int, .value | .int, .tuple ..
  | .prod .., .unit | .prod .., .bool | .prod .., .int | .prod .., .sum ..
  | .prod .., .arrow .. | .prod .., .ref .. | .prod .., .empty | .prod .., .value | .prod .., .tuple ..
  | .sum .., .unit | .sum .., .bool | .sum .., .int | .sum .., .prod ..
  | .sum .., .arrow .. | .sum .., .ref .. | .sum .., .empty | .sum .., .value | .sum .., .tuple ..
  | .arrow .., .unit | .arrow .., .bool | .arrow .., .int | .arrow .., .prod ..
  | .arrow .., .sum .. | .arrow .., .ref .. | .arrow .., .empty | .arrow .., .value | .arrow .., .tuple ..
  | .ref .., .unit | .ref .., .bool | .ref .., .int | .ref .., .prod ..
  | .ref .., .sum .. | .ref .., .arrow .. | .ref .., .empty | .ref .., .value | .ref .., .tuple ..
  | .empty, .unit | .empty, .bool | .empty, .int | .empty, .prod .. | .empty, .sum ..
  | .empty, .arrow .. | .empty, .ref .. | .empty, .value | .empty, .tuple ..
  | .value, .unit | .value, .bool | .value, .int | .value, .prod .. | .value, .sum ..
  | .value, .arrow .. | .value, .ref .. | .value, .empty | .value, .tuple ..
  | .tuple .., .unit | .tuple .., .bool | .tuple .., .int | .tuple .., .prod ..
  | .tuple .., .sum .. | .tuple .., .arrow .. | .tuple .., .ref .. | .tuple .., .empty
  | .tuple .., .value => isFalse (by intro h; cases h)
where
  typesDecEq : (as bs : List Type_) → Decidable (as = bs)
    | [], [] => isTrue rfl
    | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
    | a :: as, b :: bs => match a.decEq b, typesDecEq as bs with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)

instance : DecidableEq Type_ := Type_.decEq
instance : BEq Type_ := ⟨fun a b => decide (a = b)⟩
instance : LawfulBEq Type_ where
  eq_of_beq h := of_decide_eq_true h
  rfl := by simp [BEq.beq]

inductive BinOp where
  | add | sub | mul | div
  | eq | lt | le | gt | ge
  | and | or
  | pair
  deriving Repr, BEq, Inhabited, DecidableEq

inductive UnOp where
  | neg | not
  | fst | snd
  | inl | inr
  deriving Repr, BEq, Inhabited, DecidableEq

mutual
  inductive Val where
    | int (n : Int)
    | bool (b : Bool)
    | unit
    | pair (fst snd : Val)
    | inl (v : Val)
    | inr (v : Val)
    | loc (l : Location)
    | fix (self : Binder) (arg : Binder) (argTy retTy : Option Type_) (body : Expr)
    | tuple (vs : List Val)

  inductive Expr where
    | val (v : Val)
    | var (name : Var)
    | unop (op : UnOp) (e : Expr)
    | binop (op : BinOp) (lhs rhs : Expr)
    | fix (self : Binder) (arg : Binder) (argTy retTy : Option Type_) (body : Expr)
    | app (fn arg : Expr)
    | ifThenElse (cond thn els : Expr)
    | letIn (name : Binder) (bound body : Expr)
    | ref    (e : Expr)
    | deref  (e : Expr)
    | store  (loc val : Expr)
    | assert (e : Expr)
    | tuple (es : List Expr)
end

instance : Inhabited Val := ⟨.unit⟩
instance : Inhabited Expr := ⟨.val .unit⟩

mutual
  def Val.decEq (a b : Val) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | exact isFalse (by omega) | skip
    all_goals first | exact isFalse Val.noConfusion | skip
    case int.int a b => exact match decEq a b with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case bool.bool a b => exact match decEq a b with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case unit.unit => exact isTrue rfl
    case pair.pair a1 a2 b1 b2 => exact match a1.decEq b1, a2.decEq b2 with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case inl.inl a b => exact match a.decEq b with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case inr.inr a b => exact match a.decEq b with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case loc.loc a b => exact match decEq a b with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case fix.fix s1 a1 at1 rt1 b1 s2 a2 at2 rt2 b2 =>
      exact match decEq s1 s2, decEq a1 a2, decEq at1 at2, decEq rt1 rt2, b1.decEq b2 with
      | isTrue h1, isTrue h2, isTrue h3, isTrue h4, isTrue h5 =>
        isTrue (by subst h1; subst h2; subst h3; subst h4; subst h5; rfl)
      | isFalse h, _, _, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h, _, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case tuple.tuple vs1 vs2 =>
      exact match valsDecEq vs1 vs2 with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)

  def Expr.decEq (a b : Expr) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | exact isFalse (by omega) | skip
    all_goals first | exact isFalse Expr.noConfusion | skip
    case val.val v1 v2 => exact match v1.decEq v2 with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case var.var n1 n2 => exact match decEq n1 n2 with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case unop.unop o1 e1 o2 e2 => exact match decEq o1 o2, e1.decEq e2 with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case binop.binop o1 l1 r1 o2 l2 r2 => exact match decEq o1 o2, l1.decEq l2, r1.decEq r2 with
      | isTrue h1, isTrue h2, isTrue h3 => isTrue (by subst h1; subst h2; subst h3; rfl)
      | isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case fix.fix s1 a1 at1 rt1 b1 s2 a2 at2 rt2 b2 =>
      exact match decEq s1 s2, decEq a1 a2, decEq at1 at2, decEq rt1 rt2, b1.decEq b2 with
      | isTrue h1, isTrue h2, isTrue h3, isTrue h4, isTrue h5 =>
        isTrue (by subst h1; subst h2; subst h3; subst h4; subst h5; rfl)
      | isFalse h, _, _, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h, _, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case app.app f1 a1 f2 a2 => exact match f1.decEq f2, a1.decEq a2 with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case ifThenElse.ifThenElse c1 t1 e1 c2 t2 e2 =>
      exact match c1.decEq c2, t1.decEq t2, e1.decEq e2 with
      | isTrue h1, isTrue h2, isTrue h3 => isTrue (by subst h1; subst h2; subst h3; rfl)
      | isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case letIn.letIn b1 d1 y1 b2 d2 y2 => exact match decEq b1 b2, d1.decEq d2, y1.decEq y2 with
      | isTrue h1, isTrue h2, isTrue h3 => isTrue (by subst h1; subst h2; subst h3; rfl)
      | isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case ref.ref e1 e2 => exact match e1.decEq e2 with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case deref.deref e1 e2 => exact match e1.decEq e2 with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case store.store l1 v1 l2 v2 => exact match l1.decEq l2, v1.decEq v2 with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case assert.assert e1 e2 => exact match e1.decEq e2 with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case tuple.tuple es1 es2 =>
      exact match exprsDecEq es1 es2 with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)

  def valsDecEq : (as bs : List Val) → Decidable (as = bs)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
    | a :: as, b :: bs => match a.decEq b, valsDecEq as bs with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)

  def exprsDecEq : (as bs : List Expr) → Decidable (as = bs)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
    | a :: as, b :: bs => match a.decEq b, exprsDecEq as bs with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
end

instance : DecidableEq Val := Val.decEq
instance : DecidableEq Expr := Expr.decEq

deriving instance Repr for Val
deriving instance Repr for Expr
deriving instance BEq for Val
deriving instance BEq for Expr

abbrev Vars := List Var
abbrev Vals := List Val
abbrev Exprs := List Expr
abbrev Binders := List Binder

def Subst := TinyML.Var → Option TinyML.Val

def Subst.update (γ : Subst) (x : Var) (v : Val) : Subst :=
  fun z => if z == x then some v else γ z

@[simp] theorem Subst.update_eq (γ : Subst) (x : Var) (v : Val) (z : Var) :
    γ.update x v z = if z == x then some v else γ z := rfl

def Subst.id : Subst := fun _ => none

def Subst.remove (γ : Subst) (x : Var) : Subst :=
  fun z => if z == x then none else γ z

@[simp] theorem Subst.remove_eq (γ : Subst) (x z : Var) :
    γ.remove x z = if z == x then none else γ z := rfl

def Subst.remove' (γ : Subst) (b : Binder) : Subst :=
  match b with
  | .none    => γ
  | .named x => γ.remove x

@[simp] theorem Subst.remove'_none (γ : Subst) : γ.remove' .none = γ := rfl
@[simp] theorem Subst.remove'_named (γ : Subst) (x : Var) :
    γ.remove' (.named x) = γ.remove x := rfl

def Subst.update' (b : Binder) (v : Val) (σ : Subst) : Subst :=
  match b with
  | .none    => σ
  | .named x => σ.update x v

def Subst.removeAll (γ : Subst) (xs : List Var) : Subst :=
  xs.foldl Subst.remove γ

@[simp] theorem Subst.removeAll_nil (γ : Subst) : γ.removeAll [] = γ := rfl
@[simp] theorem Subst.removeAll_cons (γ : Subst) (x : Var) (xs : List Var) :
    γ.removeAll (x :: xs) = (γ.remove x).removeAll xs := rfl

def Subst.removeAll' (γ : Subst) (bs : Binders) : Subst :=
  bs.foldl Subst.remove' γ

@[simp] theorem Subst.removeAll'_nil (γ : Subst) : γ.removeAll' [] = γ := rfl
@[simp] theorem Subst.removeAll'_cons (γ : Subst) (b : Binder) (bs : Binders) :
    γ.removeAll' (b :: bs) = (γ.remove' b).removeAll' bs := rfl

def Subst.updateAll (γ : Subst) : List Var → List Val → Subst
  | [], _ => γ
  | _, [] => γ
  | x :: xs, v :: vs => (γ.update x v).updateAll xs vs

@[simp] theorem Subst.updateAll_nil_left (γ : Subst) (vs : List Val) : γ.updateAll [] vs = γ := rfl
@[simp] theorem Subst.updateAll_nil_right (γ : Subst) (xs : List Var) : γ.updateAll xs [] = γ := by
  cases xs <;> rfl
@[simp] theorem Subst.updateAll_cons (γ : Subst) (x : Var) (xs : List Var) (v : Val) (vs : List Val) :
    γ.updateAll (x :: xs) (v :: vs) = (γ.update x v).updateAll xs vs := rfl

def Subst.updateAll' (γ : Subst) : List Binder → List Val → Subst
  | [], _ => γ
  | _, [] => γ
  | b :: bs, v :: vs => (γ.update' b v).updateAll' bs vs

@[simp] theorem Subst.updateAll'_nil_left (γ : Subst) (vs : List Val) : γ.updateAll' [] vs = γ := rfl
@[simp] theorem Subst.updateAll'_nil_right (γ : Subst) (bs : List Binder) : γ.updateAll' bs [] = γ := by
  cases bs <;> rfl
@[simp] theorem Subst.updateAll'_cons (γ : Subst) (b : Binder) (bs : List Binder) (v : Val) (vs : List Val) :
    γ.updateAll' (b :: bs) (v :: vs) = (γ.update' b v).updateAll' bs vs := rfl

def Expr.subst (σ : Subst) : Expr → Expr
  | .val w => .val w
  | .var y => match σ y with | some v => .val v | none => .var y
  | .unop op e => .unop op (e.subst σ)
  | .binop op l r => .binop op (l.subst σ) (r.subst σ)
  | .fix f y at_ rt body =>
    .fix f y at_ rt (body.subst (σ.remove' f |>.remove' y))
  | .app fn arg => .app (fn.subst σ) (arg.subst σ)
  | .ifThenElse c t e => .ifThenElse (c.subst σ) (t.subst σ) (e.subst σ)
  | .letIn b bound body =>
    .letIn b (bound.subst σ) (body.subst (σ.remove' b))
  | .ref e => .ref (e.subst σ)
  | .deref e => .deref (e.subst σ)
  | .store loc v => .store (loc.subst σ) (v.subst σ)
  | .assert e => .assert (e.subst σ)
  | .tuple es => .tuple (es.map (Expr.subst σ))

@[simp] private theorem Subst.remove_none (x : Var) :
    Subst.remove (fun _ => none) x = fun _ => none := by
  funext z; simp [Subst.remove]

@[simp] private theorem Subst.remove'_none_subst (b : Binder) :
    Subst.remove' (fun _ => none) b = fun _ => none := by
  cases b <;> simp [Subst.remove', Subst.remove_none]

theorem Expr.subst_none (e : Expr) : e.subst (fun _ => none) = e := by
  induction e using Expr.rec
    (motive_1 := fun _ => True)
    (motive_3 := fun _ => True)
    (motive_4 := fun es => es.map (Expr.subst (fun _ => none)) = es)
  all_goals try trivial
  all_goals simp_all [Expr.subst]

theorem Expr.subst_comp (e : Expr) (σ ρ : Subst) :
    (e.subst σ).subst ρ = e.subst (fun z => match σ z with | some v => v | none => ρ z) := by
  induction e using Expr.rec
    (motive_1 := fun _ => True)
    (motive_3 := fun _ => True)
    (motive_4 := fun es => ∀ σ ρ,
      (es.map (Expr.subst σ)).map (Expr.subst ρ) =
      es.map (Expr.subst (fun z => match σ z with | some v => some v | none => ρ z)))
    generalizing σ ρ
  all_goals try trivial
  all_goals simp_all [Expr.subst]
  case var y =>
    split <;> simp_all [Expr.subst]
  case fix f y at_ rt body ih =>
    congr 1; funext z
    cases f <;> cases y <;> simp [Subst.remove', Subst.remove] <;> split <;> simp_all
  case letIn b bound body ihbound ihbd =>
    congr 1; funext z
    cases b <;> simp [Subst.remove', Subst.remove] <;> split <;> simp_all

/-- Removing a binder from γ and then substituting it back yields the same as just updating γ.
    Used to prove Program.subst_remove_update. -/
theorem Expr.subst_remove'_update' (e : Expr) (γ : Subst) (b : Binder) (v : Val) :
    (e.subst (γ.remove' b)).subst (Subst.id.update' b v) =
    e.subst (γ.update' b v) := by
  rw [Expr.subst_comp]
  congr 1; funext z
  cases b <;> simp [Subst.remove', Subst.remove, Subst.update', Subst.update, Subst.id]
  all_goals (split <;> simp_all)


def Expr.freeVars : Expr → List Var
  | .val _ => []
  | .var y => [y]
  | .unop _ e => e.freeVars
  | .binop _ l r => l.freeVars ++ r.freeVars
  | .fix f y _ _ body =>
    body.freeVars.filter (fun v => f != .named v && y != .named v)
  | .app fn arg => fn.freeVars ++ arg.freeVars
  | .ifThenElse c t e => c.freeVars ++ t.freeVars ++ e.freeVars
  | .letIn b bound body =>
    bound.freeVars ++
    body.freeVars.filter (fun v => match b with | .named y => y != v | .none => true)
  | .ref e => e.freeVars
  | .deref e => e.freeVars
  | .store loc v => loc.freeVars ++ v.freeVars
  | .assert e => e.freeVars
  | .tuple es => es.flatMap Expr.freeVars

theorem Expr.freeVars_subst (γ1 γ2 : Var → Option Val) (e : Expr) :
    (∀ x ∈ e.freeVars, γ1 x = γ2 x) → e.subst γ1 = e.subst γ2 := by
  induction e using Expr.rec
    (motive_1 := fun _ => True)
    (motive_3 := fun _ => True)
    (motive_4 := fun es => ∀ γ1 γ2 : Var → Option Val,
      (∀ x ∈ es.flatMap Expr.freeVars, γ1 x = γ2 x) →
      es.map (Expr.subst γ1) = es.map (Expr.subst γ2))
    generalizing γ1 γ2
  all_goals try trivial  -- closes all Val cases
  case val => intro; simp [Expr.subst]
  case var x =>
    intro h
    simp only [Expr.freeVars, List.mem_singleton, forall_eq] at h
    simp [Expr.subst, h]
  case unop op e ih =>
    intro h; simp only [Expr.freeVars] at h
    simp [Expr.subst, ih γ1 γ2 h]
  case binop op l r ihl ihr =>
    intro h; simp only [Expr.freeVars, List.mem_append] at h
    simp [Expr.subst, ihl γ1 γ2 (fun x hx => h x (Or.inl hx)),
                       ihr γ1 γ2 (fun x hx => h x (Or.inr hx))]
  case fix f y at_ rt body ih =>
    intro h; simp only [Expr.freeVars, List.mem_filter] at h
    simp only [Expr.subst]; congr 1; apply ih
    intro x hx
    cases f <;> cases y <;> simp only [Subst.remove', Subst.remove] <;>
      (try exact h x ⟨hx, by simp⟩) <;>
      (split <;> (try rfl) <;> (try (split <;> (try rfl)))) <;>
      (refine h x ⟨hx, ?_⟩; simp only [bne, Bool.and_eq_true, Bool.not_eq_true',
        beq_eq_false_iff_ne, ne_eq, Binder.named.injEq] at *; constructor <;> intro <;> simp_all)
  case app fn arg ihf iha =>
    intro h; simp only [Expr.freeVars, List.mem_append] at h
    simp [Expr.subst, ihf γ1 γ2 (fun x hx => h x (Or.inl hx)),
                       iha γ1 γ2 (fun x hx => h x (Or.inr hx))]
  case ifThenElse c t e ihc iht ihe =>
    intro h; simp only [Expr.freeVars, List.mem_append] at h
    simp [Expr.subst, ihc γ1 γ2 (fun x hx => h x (by simp [hx])),
                       iht γ1 γ2 (fun x hx => h x (by simp [hx])),
                       ihe γ1 γ2 (fun x hx => h x (by simp [hx]))]
  case letIn b bound body ihbound ihbd =>
    intro h; simp only [Expr.freeVars, List.mem_append, List.mem_filter] at h
    simp only [Expr.subst]; congr 1
    · exact ihbound γ1 γ2 (fun x hx => h x (Or.inl hx))
    · apply ihbd
      intro x hx
      simp only [Subst.remove']
      cases b with
      | none => exact h x (Or.inr (by simp [hx]))
      | named y =>
        by_cases hxy : (x == y) = true
        · simp [hxy]
        · simp only [Bool.not_eq_true] at hxy; simp [hxy]
          exact h x (Or.inr (And.intro hx (by simp [bne, (beq_eq_false_iff_ne.mp hxy).symm])))
  case ref e ih =>
    intro h; simp only [Expr.freeVars] at h
    simp [Expr.subst, ih γ1 γ2 h]
  case deref e ih =>
    intro h; simp only [Expr.freeVars] at h
    simp [Expr.subst, ih γ1 γ2 h]
  case store loc v ihloc ihv =>
    intro h; simp only [Expr.freeVars, List.mem_append] at h
    simp [Expr.subst, ihloc γ1 γ2 (fun x hx => h x (Or.inl hx)),
                       ihv γ1 γ2 (fun x hx => h x (Or.inr hx))]
  case assert e ih =>
    intro h; simp only [Expr.freeVars] at h
    simp [Expr.subst, ih γ1 γ2 h]
  case tuple es ih =>
    intro h; simp only [Expr.subst]; congr 1
    apply ih
    intro x hx
    exact h x (by simp [Expr.freeVars]; exact List.mem_flatMap.mp hx)
  case nil => intros; rfl
  case cons e es ihe ihes =>
    intro γ1 γ2 h
    simp only [List.flatMap_cons, List.mem_append] at h
    simp [ihe γ1 γ2 (fun x hx => h x (Or.inl hx)),
          ihes γ1 γ2 (fun x hx => h x (Or.inr hx))]

-- Substitution composition lemma for the fix body.
-- (body.subst γ').subst (id.update' fb fval |>.update' (.named arg) v_arg)
-- = body.subst (γ.update' fb fval |>.update' (.named arg) v_arg)
-- where γ' masks fb and arg from γ.
theorem Expr.subst_fix_comp (body : TinyML.Expr)
    (fb : TinyML.Binder) (arg : TinyML.Var) (γ : TinyML.Subst)
    (fval v_arg : TinyML.Val) :
    let γ' := (γ.remove' fb).remove' (.named arg)
    (body.subst γ').subst (TinyML.Subst.id.update' fb fval |>.update' (.named arg) v_arg) =
    body.subst (γ.update' fb fval |>.update' (.named arg) v_arg) := by
  simp only []
  rw [TinyML.Expr.subst_comp]
  congr 1; funext z
  cases fb <;>
    simp [TinyML.Subst.remove', TinyML.Subst.remove, TinyML.Subst.update',
          TinyML.Subst.update, TinyML.Subst.id] <;>
    (split <;> split <;> simp_all)


structure Decl (S : Type) where
  name : Binder
  body : Expr
  spec : Option S
  deriving Repr, BEq, Inhabited

def Decl.mapSpec {S T : Type} (f : S → Option T) (d : Decl S) : Decl T :=
  { name := d.name, body := d.body, spec := d.spec.bind f }

abbrev Program := List (Decl Expr)


/-- Substitute values into a declaration body (not the spec). -/
def Decl.subst (d : Decl Expr) (σ : Subst) : Decl Expr :=
  { d with body := d.body.subst σ }

/-- Substitute values into a program, respecting shadowing by binders. -/
def Program.subst : Program → Subst → Program
  | [], _ => []
  | d :: rest, σ => d.subst σ :: Program.subst rest (Subst.remove' σ d.name)

@[simp] theorem Program.subst_length (prog : TinyML.Program) (σ : TinyML.Subst) :
    (Program.subst prog σ).length = prog.length := by
  induction prog generalizing σ with
  | nil => simp [Program.subst]
  | cons d rest ih => simp [Program.subst, ih]

theorem Program.subst_comp (ds : Program) (σ τ : Subst) :
    Program.subst (Program.subst ds σ) τ =
    Program.subst ds (fun z => match σ z with | some v => some v | none => τ z) := by
  induction ds generalizing σ τ with
  | nil => simp [Program.subst]
  | cons d rest ih =>
    simp only [Program.subst, Decl.subst, Expr.subst_comp]
    congr 1
    rw [ih]; congr 1; funext z
    cases d.name <;> simp [Subst.remove', Subst.remove] <;> split <;> simp_all

-- Composition lemma: removing a binder then substituting it is the same as updating.
theorem Program.subst_remove_update (ds : Program) (b : Binder) (v : Val)
    (γ : Subst) :
    Program.subst (Program.subst ds (Subst.remove' γ b))
      (Subst.update' b v .id) =
    Program.subst ds (Subst.update' b v γ) := by
  rw [Program.subst_comp]
  congr 1; funext z
  cases b <;>
    simp [Subst.remove', Subst.remove, Subst.update',
          Subst.update, Subst.id] <;>
    all_goals (split <;> simp_all)

theorem Program.subst_id (prog : TinyML.Program) :
    prog.subst TinyML.Subst.id = prog := by
  have hid : TinyML.Subst.id = (fun _ => none) := rfl
  rw [hid]
  induction prog with
  | nil => simp [TinyML.Program.subst]
  | cons d rest ih =>
    simp [TinyML.Program.subst, TinyML.Decl.subst, TinyML.Expr.subst_none, ih]

def Exprs.subst (σ : Subst) (es : Exprs) : Exprs := es.map (Expr.subst σ)

@[simp] theorem Exprs.subst_nil (σ : Subst) : Exprs.subst σ [] = [] := rfl
@[simp] theorem Exprs.subst_cons (σ : Subst) (e : Expr) (es : Exprs) :
    Exprs.subst σ (e :: es) = e.subst σ :: Exprs.subst σ es := rfl

def Exprs.freeVars : Exprs → List Var
  | [] => []
  | e :: es => e.freeVars ++ Exprs.freeVars es

@[simp] theorem Exprs.freeVars_nil : Exprs.freeVars [] = [] := rfl
@[simp] theorem Exprs.freeVars_cons (e : Expr) (es : Exprs) :
    Exprs.freeVars (e :: es) = e.freeVars ++ Exprs.freeVars es := rfl

theorem Exprs.subst_none (es : Exprs) : Exprs.subst (fun _ => none) es = es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [Exprs.subst_cons, Expr.subst_none, ih]

theorem Exprs.subst_comp (es : Exprs) (σ ρ : Subst) :
    Exprs.subst ρ (Exprs.subst σ es) =
    Exprs.subst (fun z => match σ z with | some v => some v | none => ρ z) es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [Exprs.subst_cons, Expr.subst_comp, ih]

theorem Exprs.freeVars_subst (γ1 γ2 : Var → Option Val) (es : Exprs) :
    (∀ x ∈ Exprs.freeVars es, γ1 x = γ2 x) → Exprs.subst γ1 es = Exprs.subst γ2 es := by
  induction es with
  | nil => intros; rfl
  | cons e es ih =>
    intro h
    simp only [Exprs.freeVars_cons, List.mem_append] at h
    simp only [Exprs.subst_cons]
    congr 1
    · exact Expr.freeVars_subst γ1 γ2 e (fun x hx => h x (Or.inl hx))
    · exact ih (fun x hx => h x (Or.inr hx))

@[simp] theorem Binder.named_beq (x z : Var) : (Binder.named x == Binder.named z) = (x == z) := by
  simp [BEq.beq, instBEqBinder.beq]

theorem Subst.removeAll'_eq (γ : Subst) (bs : Binders) (z : Var) :
    γ.removeAll' bs z = if bs.any (· == .named z) then none else γ z := by
  induction bs generalizing γ with
  | nil => simp
  | cons b bs ih =>
    simp only [Subst.removeAll'_cons, List.any_cons]
    cases b with
    | none => simp [Subst.remove', ih]
    | named x =>
      simp only [Subst.remove'_named, Binder.named_beq]
      rw [ih]; simp only [BEq.comm (a := x) (b := z)]
      split <;> simp_all

/-- Look up the value bound to variable `z` in a binder/value list.
    Last matching binder wins (matching left-fold semantics of `updateAll'`).
    Equivalent to `(bs.zip vs).reverse.findSome? fun (b, v) => if b == .named z then some v else none`. -/
def Binders.findVal : Binders → Vals → Var → Option Val
  | [], _, _ | _, [], _ => none
  | b :: bs, v :: vs, z =>
    match findVal bs vs z with
    | some w => some w
    | none => if b == .named z then some v else none

@[simp] theorem Binders.findVal_nil_left (vs : Vals) (z : Var) : Binders.findVal [] vs z = none := rfl
@[simp] theorem Binders.findVal_nil_right (bs : Binders) (z : Var) : Binders.findVal bs [] z = none := by
  cases bs <;> rfl
@[simp] theorem Binders.findVal_cons (b : Binder) (bs : Binders) (v : Val) (vs : Vals) (z : Var) :
    Binders.findVal (b :: bs) (v :: vs) z =
    match Binders.findVal bs vs z with
    | some w => some w
    | none => if b == .named z then some v else none := rfl

theorem Subst.updateAll'_eq (γ : Subst) (bs : Binders) (vs : Vals) (z : Var)
    (hlen : bs.length = vs.length) :
    γ.updateAll' bs vs z =
    match Binders.findVal bs vs z with
    | some v => some v
    | none => γ z := by
  induction bs generalizing γ vs with
  | nil => simp
  | cons b bs ih =>
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp only [Subst.updateAll'_cons, Binders.findVal_cons]
      rw [ih _ _ hlen]
      rcases h : Binders.findVal bs vs z with _ | w
      · cases b with
        | none => simp [Subst.update']
        | named x =>
          simp only [Subst.update', Subst.update_eq, Binder.named_beq]
          by_cases hzx : z = x
          · simp_all
          · simp [beq_iff_eq, hzx, Ne.symm hzx]
      · simp

/-- The composition of `removeAll'` followed by `updateAll'` is just `updateAll'`.
    Generalized: the "base" substitution `σ` is arbitrary (instantiate with `σ = id` for the main use). -/
private theorem Subst.removeAll'_updateAll'_gen (bs : Binders) (vs : Vals)
    (hlen : bs.length = vs.length) (γ σ : Subst) (z : Var) :
    let merged : Subst := fun w => match γ w with | some v => some v | none => σ w
    (match (γ.removeAll' bs) z with | some v => some v | none => (σ.updateAll' bs vs) z)
    = (merged.updateAll' bs vs) z := by
  simp only []
  induction bs generalizing γ σ vs with
  | nil => simp only [Subst.removeAll'_nil, Subst.updateAll'_nil_left]
  | cons b bs ih =>
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp only [Subst.removeAll'_cons, Subst.updateAll'_cons]
      rw [ih vs hlen (γ.remove' b) (Subst.update' b v σ)]
      congr 1; funext w
      cases b with
      | none => simp [Subst.remove', Subst.update']
      | named x =>
        simp only [Subst.remove', Subst.remove_eq, Subst.update', Subst.update_eq]
        by_cases hwx : w = x <;> simp_all

private theorem Subst.removeAll'_updateAll'_comp (γ : Subst) (bs : Binders) (vs : Vals)
    (hlen : bs.length = vs.length) (z : Var) :
    (match (γ.removeAll' bs) z with | some v => some v | none => (Subst.id.updateAll' bs vs) z)
    = (γ.updateAll' bs vs) z := by
  rw [removeAll'_updateAll'_gen _ _ hlen]
  congr 1; funext w; simp [Subst.id]; split <;> simp_all

theorem Exprs.subst_removeAll'_updateAll' (es : Exprs) (γ : Subst) (bs : Binders) (vs : Vals)
    (hlen : bs.length = vs.length) :
    Exprs.subst (Subst.id.updateAll' bs vs) (Exprs.subst (γ.removeAll' bs) es) =
    Exprs.subst (γ.updateAll' bs vs) es := by
  rw [Exprs.subst_comp]
  congr 1
  funext z
  exact Subst.removeAll'_updateAll'_comp γ bs vs hlen z

end TinyML
