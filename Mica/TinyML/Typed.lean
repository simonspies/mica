import Mica.TinyML.Common
import Mica.TinyML.Untyped

namespace Typed

open TinyML

inductive Binder where
  | none
  | named (name : Var) (ty : Option Typ)
  deriving Repr, Inhabited, DecidableEq

instance : BEq Binder := ⟨fun a b => decide (a = b)⟩

instance : LawfulBEq Binder where
  eq_of_beq h := of_decide_eq_true h
  rfl := by simp [BEq.beq]

inductive Expr where
  | const (c : Const)
  | var (name : Var)
  | unop (op : UnOp) (e : Expr)
  | binop (op : BinOp) (lhs rhs : Expr)
  | fix (self : Binder) (args : List Binder) (retTy : Option Typ) (body : Expr)
  | app (fn : Expr) (args : List Expr)
  | ifThenElse (cond thn els : Expr)
  | letIn (name : Binder) (bound body : Expr)
  | ref    (e : Expr)
  | deref  (e : Expr)
  | store  (loc val : Expr)
  | assert (e : Expr)
  | tuple (es : List Expr)
  | inj (tag : Nat) (arity : Nat) (payload : Expr)
  | match_ (scrutinee : Expr) (branches : List (Binder × Expr))

instance : Inhabited Expr := ⟨.const .unit⟩

/-- Is the expression a function (fix) node? -/
def Expr.isFunc : Expr → Bool
  | .fix .. => true
  | _ => false

@[simp] theorem Expr.isFunc_fix : (Expr.fix self args retTy body).isFunc = true := rfl

theorem Expr.isFunc_elim {e : Expr} (h : e.isFunc = true) :
    ∃ self args retTy body, e = .fix self args retTy body := by
  cases e <;> simp [isFunc] at h
  exact ⟨_, _, _, _, rfl⟩


mutual
  def Expr.decEq (a b : Expr) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | exact isFalse (by omega) | skip
    all_goals first | exact isFalse Expr.noConfusion | skip
    case const.const c1 c2 => exact match decEq c1 c2 with
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
    case fix.fix s1 args1 rt1 b1 s2 args2 rt2 b2 =>
      exact match decEq s1 s2, decEq args1 args2, decEq rt1 rt2, b1.decEq b2 with
      | isTrue h1, isTrue h2, isTrue h3, isTrue h4 =>
        isTrue (by subst h1; subst h2; subst h3; subst h4; rfl)
      | isFalse h, _, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
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
    case inj.inj t1 a1 p1 t2 a2 p2 => exact match decEq t1 t2, decEq a1 a2, p1.decEq p2 with
      | isTrue h1, isTrue h2, isTrue h3 => isTrue (by subst h1; subst h2; subst h3; rfl)
      | isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case match_.match_ s1 bs1 s2 bs2 => exact match s1.decEq s2, branchesDecEq bs1 bs2 with
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

  def branchDecEq : (a b : Binder × Expr) → Decidable (a = b)
    | (b1, e1), (b2, e2) => match decEq b1 b2, e1.decEq e2 with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)

  def branchesDecEq : (as bs : List (Binder × Expr)) → Decidable (as = bs)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
    | a :: as, b :: bs => match branchDecEq a b, branchesDecEq as bs with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
end

instance : DecidableEq Expr := Expr.decEq

deriving instance Repr for Expr
deriving instance BEq for Expr

abbrev Vars := List Var
abbrev Exprs := List Expr
abbrev Binders := List Binder

@[simp] theorem Binder.named_beq (x z : Var) (tx tz : Option Typ) :
    (Binder.named x tx == Binder.named z tz) = (x == z && tx == tz) := by
  apply Bool.eq_iff_iff.mpr
  simp only [BEq.beq, Bool.and_eq_true, Binder.named.injEq, decide_eq_true_iff]
  exact and_congr Iff.rfl beq_iff_eq.symm

structure Decl (S : Type) where
  name : Binder
  body : Expr
  spec : Option S
  deriving Repr, BEq, Inhabited

def Decl.mapSpec {S T : Type} (f : S → Option T) (d : Decl S) : Decl T :=
  { name := d.name, body := d.body, spec := d.spec.bind f }

abbrev Program (S : Type) := List (Decl S)

/-! ### Trivial elaboration from Untyped to Typed -/

def Binder.elaborate : Untyped.Binder → Typed.Binder
  | .none => .none
  | .named x ty => .named x ty

mutual
  def Expr.elaborate : Untyped.Expr → Typed.Expr
    | .const c => .const c
    | .var x => .var x
    | .unop op e => .unop op (Expr.elaborate e)
    | .binop op l r => .binop op (Expr.elaborate l) (Expr.elaborate r)
    | .fix self args retTy body =>
        .fix (Binder.elaborate self) (args.map Binder.elaborate) retTy (Expr.elaborate body)
    | .app fn args => .app (Expr.elaborate fn) (Exprs.elaborate args)
    | .ifThenElse c t e => .ifThenElse (Expr.elaborate c) (Expr.elaborate t) (Expr.elaborate e)
    | .letIn b bound body =>
        .letIn (Binder.elaborate b) (Expr.elaborate bound) (Expr.elaborate body)
    | .ref e => .ref (Expr.elaborate e)
    | .deref e => .deref (Expr.elaborate e)
    | .store loc val => .store (Expr.elaborate loc) (Expr.elaborate val)
    | .assert e => .assert (Expr.elaborate e)
    | .tuple es => .tuple (Exprs.elaborate es)
    | .inj tag arity payload => .inj tag arity (Expr.elaborate payload)
    | .match_ scrut branches =>
        .match_ (Expr.elaborate scrut) (Branches.elaborate branches)

  def Exprs.elaborate : List Untyped.Expr → List Typed.Expr
    | [] => []
    | e :: es => Expr.elaborate e :: Exprs.elaborate es

  def Branches.elaborate : List (Untyped.Binder × Untyped.Expr) → List (Typed.Binder × Typed.Expr)
    | [] => []
    | (b, e) :: rest => (Binder.elaborate b, Expr.elaborate e) :: Branches.elaborate rest
end
def Decl.elaborate {S : Type} (d : Untyped.Decl S) : Typed.Decl S :=
  { name := Binder.elaborate d.name, body := Expr.elaborate d.body, spec := d.spec }

def Program.elaborate {S : Type} (prog : Untyped.Program S) : Typed.Program S :=
  prog.map Decl.elaborate

end Typed
