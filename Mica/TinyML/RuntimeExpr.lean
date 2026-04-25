-- SUMMARY: Runtime TinyML IR, values, and substitution machinery.
import Mica.TinyML.Common

namespace Runtime

abbrev Location := Nat

open TinyML (Var BinOp UnOp)

inductive Binder where
  | none
  | named (name : Var)
  deriving Repr, BEq, Inhabited, DecidableEq

instance : LawfulBEq Binder where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> simp_all [BEq.beq, instBEqBinder.beq]
  rfl {a} := by
    cases a <;> simp [BEq.beq, instBEqBinder.beq]

mutual
  inductive Val where
    | int (n : Int)
    | bool (b : Bool)
    | unit
    | inj (tag : Nat) (arity : Nat) (payload : Val)
    | loc (l : Location)
    | fix (self : Binder) (args : List Binder) (body : Expr)
    | tuple (vs : List Val)

  inductive Expr where
    | val (v : Val)
    | var (name : Var)
    | unop (op : UnOp) (e : Expr)
    | binop (op : BinOp) (lhs rhs : Expr)
    | fix (self : Binder) (args : List Binder) (body : Expr)
    | app (fn : Expr) (args : List Expr)
    | ifThenElse (cond thn els : Expr)
    | ref    (e : Expr)
    | deref  (e : Expr)
    | store  (loc val : Expr)
    | assert (e : Expr)
    | tuple (es : List Expr)
    | inj (tag : Nat) (arity : Nat) (payload : Expr)
    | match_ (scrutinee : Expr) (branches : List Expr)
end

instance : Inhabited Val := ⟨.unit⟩
instance : Inhabited Expr := ⟨.val .unit⟩

/-- `let x = e1 in e2` is desugared to `(fix _ [x] e2) e1`. -/
def Expr.letIn (name : Binder) (bound body : Expr) : Expr :=
  .app (.fix .none [name] body) [bound]

/-- Is the expression a function (fix) node? -/
def Expr.isFunc : Expr → Bool
  | .fix .. => true
  | _ => false

@[simp] theorem Expr.isFunc_fix : (Expr.fix self args body).isFunc = true := rfl

theorem Expr.isFunc_elim {e : Expr} (h : e.isFunc = true) :
    ∃ self args body, e = .fix self args body := by
  cases e <;> simp [isFunc] at h
  exact ⟨_, _, _, rfl⟩


-- `deriving DecidableEq` does not support mutual inductives with `List`-nested
-- recursion, so we define the instances by hand.
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
    case inj.inj t1 a1 p1 t2 a2 p2 => exact match decEq t1 t2, decEq a1 a2, p1.decEq p2 with
      | isTrue h1, isTrue h2, isTrue h3 => isTrue (by subst h1; subst h2; subst h3; rfl)
      | isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case loc.loc a b => exact match decEq a b with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case fix.fix s1 args1 b1 s2 args2 b2 =>
      exact match decEq s1 s2, decEq args1 args2, b1.decEq b2 with
      | isTrue h1, isTrue h2, isTrue h3 =>
        isTrue (by subst h1; subst h2; subst h3; rfl)
      | isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
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
    case fix.fix s1 args1 b1 s2 args2 b2 =>
      exact match decEq s1 s2, decEq args1 args2, b1.decEq b2 with
      | isTrue h1, isTrue h2, isTrue h3 =>
        isTrue (by subst h1; subst h2; subst h3; rfl)
      | isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case app.app f1 args1 f2 args2 => exact match f1.decEq f2, exprsDecEq args1 args2 with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case ifThenElse.ifThenElse c1 t1 e1 c2 t2 e2 =>
      exact match c1.decEq c2, t1.decEq t2, e1.decEq e2 with
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
    case inj.inj t1 a1 p1 t2 a2 p2 => exact match decEq t1 t2, decEq a1 a2, p1.decEq p2 with
      | isTrue h1, isTrue h2, isTrue h3 => isTrue (by subst h1; subst h2; subst h3; rfl)
      | isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case match_.match_ s1 bs1 s2 bs2 => exact match s1.decEq s2, exprsDecEq bs1 bs2 with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)

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

def Subst := Var → Option Val

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

def Subst.updateBinder (b : Binder) (v : Val) (σ : Subst) : Subst :=
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

def Subst.updateAllBinder (γ : Subst) : List Binder → List Val → Subst
  | [], _ => γ
  | _, [] => γ
  | b :: bs, v :: vs => (γ.updateBinder b v).updateAllBinder bs vs

@[simp] theorem Subst.updateAllBinder_nil_left (γ : Subst) (vs : List Val) : γ.updateAllBinder [] vs = γ := rfl
@[simp] theorem Subst.updateAllBinder_nil_right (γ : Subst) (bs : List Binder) : γ.updateAllBinder bs [] = γ := by
  cases bs <;> rfl
@[simp] theorem Subst.updateAllBinder_cons (γ : Subst) (b : Binder) (bs : List Binder) (v : Val) (vs : List Val) :
    γ.updateAllBinder (b :: bs) (v :: vs) = (γ.updateBinder b v).updateAllBinder bs vs := rfl

def Expr.subst (σ : Subst) : Expr → Expr
  | .val w => .val w
  | .var y => match σ y with | some v => .val v | none => .var y
  | .unop op e => .unop op (e.subst σ)
  | .binop op l r => .binop op (l.subst σ) (r.subst σ)
  | .fix f args body =>
    .fix f args (body.subst (σ.remove' f |>.removeAll' args))
  | .app fn args => .app (fn.subst σ) (args.map (Expr.subst σ))
  | .ifThenElse c t e => .ifThenElse (c.subst σ) (t.subst σ) (e.subst σ)
  | .ref e => .ref (e.subst σ)
  | .deref e => .deref (e.subst σ)
  | .store loc v => .store (loc.subst σ) (v.subst σ)
  | .assert e => .assert (e.subst σ)
  | .tuple es => .tuple (es.map (Expr.subst σ))
  | .inj tag arity payload => .inj tag arity (payload.subst σ)
  | .match_ scrut branches => .match_ (scrut.subst σ) (branches.map (Expr.subst σ))

@[simp] theorem Expr.subst_fix (σ : Subst) (self : Binder) (args : List Binder) (body : Expr) :
    (Expr.fix self args body).subst σ = .fix self args (body.subst (σ.remove' self |>.removeAll' args)) := by
  simp [Expr.subst]

@[simp] theorem Expr.letIn_subst (σ : Subst) (name : Binder) (bound body : Expr) :
    (Expr.letIn name bound body).subst σ = Expr.letIn name (bound.subst σ) (body.subst (σ.remove' name)) := by
  simp [Expr.letIn, Expr.subst, Subst.remove'_none, Subst.removeAll'_cons, Subst.removeAll'_nil]

theorem Expr.isFunc_subst {e : Expr} {σ : Subst} (h : e.isFunc = true) :
    (e.subst σ).isFunc = true := by
  obtain ⟨self, args, body, rfl⟩ := isFunc_elim h
  simp [subst_fix]

@[simp] private theorem Subst.remove_none (x : Var) :
    Subst.remove (fun _ => none) x = fun _ => none := by
  funext z; simp [Subst.remove]

@[simp] private theorem Subst.remove'_none_subst (b : Binder) :
    Subst.remove' (fun _ => none) b = fun _ => none := by
  cases b <;> simp [Subst.remove', Subst.remove_none]

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

@[simp] theorem Expr.subst_val (σ : Subst) (v : Val) : (Expr.val v).subst σ = .val v := by
  simp [Expr.subst]

@[simp] private theorem Subst.removeAll'_none_subst_list (bs : Binders) :
    Subst.removeAll' (fun _ => none) bs = fun _ => none := by
  induction bs with
  | nil => simp
  | cons b bs ih => simp only [Subst.removeAll'_cons, Subst.remove'_none_subst, ih]

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
  case fix f args body ih =>
    congr 1; funext z
    simp only [Subst.removeAll'_eq]
    cases f <;> simp [Subst.remove', Subst.remove] <;> split <;> simp_all
    all_goals (split <;> simp_all)
/-- Removing a binder from γ and then substituting it back yields the same as just updating γ.
    Used to prove Program.subst_remove_update. -/
theorem Expr.subst_remove'_updateBinder (e : Expr) (γ : Subst) (b : Binder) (v : Val) :
    (e.subst (γ.remove' b)).subst (Subst.id.updateBinder b v) =
    e.subst (γ.updateBinder b v) := by
  rw [Expr.subst_comp]
  congr 1; funext z
  cases b <;> simp [Subst.remove', Subst.remove, Subst.updateBinder, Subst.update, Subst.id]
  all_goals (split <;> simp_all)


def Expr.freeVars : Expr → List Var
  | .val _ => []
  | .var y => [y]
  | .unop _ e => e.freeVars
  | .binop _ l r => l.freeVars ++ r.freeVars
  | .fix f args body =>
    body.freeVars.filter (fun v => f != .named v && !args.any (· == .named v))
  | .app fn args => fn.freeVars ++ args.flatMap Expr.freeVars
  | .ifThenElse c t e => c.freeVars ++ t.freeVars ++ e.freeVars
  | .ref e => e.freeVars
  | .deref e => e.freeVars
  | .store loc v => loc.freeVars ++ v.freeVars
  | .assert e => e.freeVars
  | .tuple es => es.flatMap Expr.freeVars
  | .inj _ _ payload => payload.freeVars
  | .match_ scrut branches => scrut.freeVars ++ branches.flatMap Expr.freeVars

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
  case val => intro; simp
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
  case fix f args body ih =>
    intro h; simp only [Expr.freeVars, List.mem_filter] at h
    simp only [Expr.subst]; congr 1; apply ih
    intro x hx
    simp only [Subst.removeAll'_eq]
    -- The filter condition in h guarantees x is not bound by f or args
    cases f <;> simp only [Subst.remove', Subst.remove]
    · -- f = .none: only args matter
      split
      · rfl
      · rename_i hany
        refine h x ⟨hx, ?_⟩
        simp only [bne, BEq.beq, instBEqBinder.beq, Bool.not_eq_true', Bool.and_eq_true]
        exact ⟨trivial, by simpa [BEq.beq, instBEqBinder.beq, Bool.not_eq_true'] using hany⟩
    · -- f = .named name
      rename_i name
      split
      · rfl
      · split
        · rfl
        · rename_i hany hne
          refine h x ⟨hx, ?_⟩
          simp only [bne, BEq.beq, instBEqBinder.beq, Bool.not_eq_true', Bool.and_eq_true]
          exact ⟨by simpa [BEq.beq, instBEqBinder.beq, beq_iff_eq, ne_comm] using hne,
                 by simpa [BEq.beq, instBEqBinder.beq, Bool.not_eq_true'] using hany⟩
  case app fn args ihf ihargs =>
    intro h; simp only [Expr.freeVars, List.mem_append] at h
    simp only [Expr.subst]; congr 1
    · exact ihf γ1 γ2 (fun x hx => h x (Or.inl hx))
    · exact ihargs γ1 γ2 (fun x hx => h x (Or.inr hx))
  case ifThenElse c t e ihc iht ihe =>
    intro h; simp only [Expr.freeVars, List.mem_append] at h
    simp [Expr.subst, ihc γ1 γ2 (fun x hx => h x (by simp [hx])),
                       iht γ1 γ2 (fun x hx => h x (by simp [hx])),
                       ihe γ1 γ2 (fun x hx => h x (by simp [hx]))]
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
  case inj tag arity payload ih =>
    intro h; simp only [Expr.freeVars] at h
    simp [Expr.subst, ih γ1 γ2 h]
  case match_ scrut branches ihscrut ihbranches =>
    intro h; simp only [Expr.freeVars, List.mem_append] at h
    simp only [Expr.subst]; congr 1
    · exact ihscrut γ1 γ2 (fun x hx => h x (Or.inl hx))
    · apply ihbranches
      intro x hx
      exact h x (Or.inr hx)
  case nil => intros; rfl
  case cons e es ihe ihes =>
    intro γ1 γ2 h
    simp only [List.flatMap_cons, List.mem_append] at h
    simp [ihe γ1 γ2 (fun x hx => h x (Or.inl hx)),
          ihes γ1 γ2 (fun x hx => h x (Or.inr hx))]

structure Decl where
  name : Binder
  body : Expr
  deriving Repr, BEq, Inhabited

abbrev Program := List Decl


/-- Substitute values into a declaration body. -/
def Decl.subst (d : Decl) (σ : Subst) : Decl :=
  { d with body := d.body.subst σ }

/-- Substitute values into a program, respecting shadowing by binders. -/
def Program.subst : Program → Subst → Program
  | [], _ => []
  | d :: rest, σ => d.subst σ :: Program.subst rest (Subst.remove' σ d.name)

@[simp] theorem Program.subst_length (prog : Program) (σ : Subst) :
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
      (Subst.updateBinder b v .id) =
    Program.subst ds (Subst.updateBinder b v γ) := by
  rw [Program.subst_comp]
  congr 1; funext z
  cases b <;>
    simp [Subst.remove', Subst.remove, Subst.updateBinder,
          Subst.update, Subst.id] <;>
    all_goals (split <;> simp_all)

theorem Program.subst_id (prog : Program) :
    prog.subst Subst.id = prog := by
  have hid : Subst.id = (fun _ => none) := rfl
  rw [hid]
  induction prog with
  | nil => simp [Program.subst]
  | cons d rest ih =>
    simp [Program.subst, Decl.subst, Expr.subst_none, ih]

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

/-- Look up the value bound to variable `z` in a binder/value list.
    Last matching binder wins (matching left-fold semantics of `updateAllBinder`).
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

theorem Subst.updateAllBinder_eq (γ : Subst) (bs : Binders) (vs : Vals) (z : Var)
    (hlen : bs.length = vs.length) :
    γ.updateAllBinder bs vs z =
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
      simp only [Subst.updateAllBinder_cons, Binders.findVal_cons]
      rw [ih _ _ hlen]
      rcases h : Binders.findVal bs vs z with _ | w
      · cases b with
        | none => simp [Subst.updateBinder]
        | named x =>
          simp only [Subst.updateBinder, Subst.update_eq, Binder.named_beq]
          by_cases hzx : z = x
          · simp_all
          · simp [beq_iff_eq, hzx, Ne.symm hzx]
      · simp

/-- The composition of `removeAll'` followed by `updateAllBinder` is just `updateAllBinder`.
    Generalized: the "base" substitution `σ` is arbitrary (instantiate with `σ = id` for the main use). -/
private theorem Subst.removeAll'_updateAllBinder_gen (bs : Binders) (vs : Vals)
    (hlen : bs.length = vs.length) (γ σ : Subst) (z : Var) :
    let merged : Subst := fun w => match γ w with | some v => some v | none => σ w
    (match (γ.removeAll' bs) z with | some v => some v | none => (σ.updateAllBinder bs vs) z)
    = (merged.updateAllBinder bs vs) z := by
  simp only []
  induction bs generalizing γ σ vs with
  | nil => simp only [Subst.removeAll'_nil, Subst.updateAllBinder_nil_left]
  | cons b bs ih =>
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp only [Subst.removeAll'_cons, Subst.updateAllBinder_cons]
      rw [ih vs hlen (γ.remove' b) (Subst.updateBinder b v σ)]
      congr 1; funext w
      cases b with
      | none => simp [Subst.remove', Subst.updateBinder]
      | named x =>
        simp only [Subst.remove', Subst.remove_eq, Subst.updateBinder, Subst.update_eq]
        by_cases hwx : w = x <;> simp_all

private theorem Subst.removeAll'_updateAllBinder_comp (γ : Subst) (bs : Binders) (vs : Vals)
    (hlen : bs.length = vs.length) (z : Var) :
    (match (γ.removeAll' bs) z with | some v => some v | none => (Subst.id.updateAllBinder bs vs) z)
    = (γ.updateAllBinder bs vs) z := by
  rw [removeAll'_updateAllBinder_gen _ _ hlen]
  congr 1; funext w; simp [Subst.id]; split <;> simp_all

-- Substitution composition lemma for the fix body.
theorem Expr.subst_fix_comp (body : Expr)
    (fb : Binder) (bs : Binders) (γ : Subst)
    (fval : Val) (vs : Vals)
    (hlen : bs.length = vs.length) :
    let γ' := (γ.remove' fb).removeAll' bs
    (body.subst γ').subst (Subst.id.updateBinder fb fval |>.updateAllBinder bs vs) =
    body.subst (γ.updateBinder fb fval |>.updateAllBinder bs vs) := by
  simp only []; rw [Expr.subst_comp]; congr 1; funext z
  have hgen := Subst.removeAll'_updateAllBinder_gen bs vs hlen
                 (γ.remove' fb) (Subst.id.updateBinder fb fval) z
  simp only [] at hgen
  rw [hgen]
  congr 1; funext w
  cases fb with
  | none => simp only [Subst.remove', Subst.updateBinder, Subst.id]; cases γ w <;> rfl
  | named f =>
    simp only [Subst.remove'_named, Subst.updateBinder, Subst.update_eq,
               Subst.remove_eq, Subst.id]
    split <;> simp_all

theorem Exprs.subst_removeAll'_updateAllBinder (es : Exprs) (γ : Subst) (bs : Binders) (vs : Vals)
    (hlen : bs.length = vs.length) :
    Exprs.subst (Subst.id.updateAllBinder bs vs) (Exprs.subst (γ.removeAll' bs) es) =
    Exprs.subst (γ.updateAllBinder bs vs) es := by
  rw [Exprs.subst_comp]
  congr 1
  funext z
  exact Subst.removeAll'_updateAllBinder_comp γ bs vs hlen z

end Runtime

namespace TinyML

def Const.runtime : TinyML.Const → Runtime.Val
  | .int n  => .int n
  | .bool b => .bool b
  | .unit   => .unit

end TinyML
