-- SUMMARY: Typed TinyML IR, with erasure to the runtime IR.
import Mica.TinyML.Common
import Mica.TinyML.Types
import Mica.TinyML.RuntimeExpr

namespace Typed

open TinyML

structure Binder where
  name : Option Var
  ty : Typ
  deriving Repr

instance : Inhabited Binder := ⟨⟨Option.none, .value⟩⟩

instance : DecidableEq Binder := by
  intro a b
  cases a with
  | mk n1 t1 =>
    cases b with
    | mk n2 t2 =>
      exact match decEq n1 n2, decEq t1 t2 with
        | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
        | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
        | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)

def Binder.none (ty : Typ) : Binder := ⟨Option.none, ty⟩

def Binder.named (name : Var) (ty : Typ) : Binder := ⟨some name, ty⟩

instance : BEq Binder := ⟨fun a b => decide (a = b)⟩

instance : LawfulBEq Binder where
  eq_of_beq {a b} h := by
    exact of_decide_eq_true h
  rfl {a} := by
    simp [BEq.beq]

inductive Expr where
  | const (c : Const)
  | var (name : Var) (ty : Typ)
  | unop (op : UnOp) (e : Expr) (ty : Typ)
  | binop (op : BinOp) (lhs rhs : Expr) (ty : Typ)
  | fix (self : Binder) (args : List Binder) (retTy : Typ) (body : Expr)
  | app (fn : Expr) (args : List Expr) (ty : Typ)
  | ifThenElse (cond thn els : Expr) (ty : Typ)
  | letIn (name : Binder) (bound body : Expr)
  | ref    (e : Expr)
  | deref  (e : Expr) (ty : Typ)
  | store  (loc val : Expr)
  | assert (e : Expr)
  | tuple (es : List Expr)
  | inj (tag : Nat) (arity : Nat) (payload : Expr)
  | match_ (scrutinee : Expr) (branches : List (Binder × Expr)) (ty : Typ)
  | cast (e : Expr) (ty : Typ)

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

-- `deriving DecidableEq` does not support mutual inductives with `List`-nested
-- recursion, so we define the instance by hand.
mutual
  def Expr.decEq (a b : Expr) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | exact isFalse (by omega) | skip
    all_goals first | exact isFalse Expr.noConfusion | skip
    case const.const c1 c2 => exact match decEq c1 c2 with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case var.var n1 t1 n2 t2 => exact match decEq n1 n2, decEq t1 t2 with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case unop.unop o1 e1 t1 o2 e2 t2 =>
      exact match decEq o1 o2, e1.decEq e2, decEq t1 t2 with
      | isTrue h1, isTrue h2, isTrue h3 => isTrue (by subst h1; subst h2; subst h3; rfl)
      | isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case binop.binop o1 l1 r1 t1 o2 l2 r2 t2 =>
      exact match decEq o1 o2, l1.decEq l2, r1.decEq r2, decEq t1 t2 with
      | isTrue h1, isTrue h2, isTrue h3, isTrue h4 =>
        isTrue (by subst h1; subst h2; subst h3; subst h4; rfl)
      | isFalse h, _, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case fix.fix s1 args1 rt1 b1 s2 args2 rt2 b2 =>
      exact match decEq s1 s2, decEq args1 args2, decEq rt1 rt2, b1.decEq b2 with
      | isTrue h1, isTrue h2, isTrue h3, isTrue h4 =>
        isTrue (by subst h1; subst h2; subst h3; subst h4; rfl)
      | isFalse h, _, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case app.app f1 args1 t1 f2 args2 t2 =>
      exact match f1.decEq f2, exprsDecEq args1 args2, decEq t1 t2 with
      | isTrue h1, isTrue h2, isTrue h3 => isTrue (by subst h1; subst h2; subst h3; rfl)
      | isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case ifThenElse.ifThenElse c1 t1 e1 ty1 c2 t2 e2 ty2 =>
      exact match c1.decEq c2, t1.decEq t2, e1.decEq e2, decEq ty1 ty2 with
      | isTrue h1, isTrue h2, isTrue h3, isTrue h4 =>
        isTrue (by subst h1; subst h2; subst h3; subst h4; rfl)
      | isFalse h, _, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case letIn.letIn b1 d1 y1 b2 d2 y2 => exact match decEq b1 b2, d1.decEq d2, y1.decEq y2 with
      | isTrue h1, isTrue h2, isTrue h3 => isTrue (by subst h1; subst h2; subst h3; rfl)
      | isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case ref.ref e1 e2 => exact match e1.decEq e2 with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case deref.deref e1 t1 e2 t2 => exact match e1.decEq e2, decEq t1 t2 with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
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
    case match_.match_ s1 bs1 t1 s2 bs2 t2 =>
      exact match s1.decEq s2, branchesDecEq bs1 bs2, decEq t1 t2 with
      | isTrue h1, isTrue h2, isTrue h3 => isTrue (by subst h1; subst h2; subst h3; rfl)
      | isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case cast.cast e1 t1 e2 t2 => exact match e1.decEq e2, decEq t1 t2 with
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

def Const.ty : Const → Typ
  | .int _ => .int
  | .bool _ => .bool
  | .unit => .unit

def arrowOfArgs : List Binder → Typ → Typ
  | [], retTy => retTy
  | arg :: args, retTy => .arrow arg.ty (arrowOfArgs args retTy)

def Expr.ty : Expr → Typ
  | .const c => Const.ty c
  | .var _ ty => ty
  | .unop _ _ ty => ty
  | .binop _ _ _ ty => ty
  | .fix _ args retTy _ => arrowOfArgs args retTy
  | .app _ _ ty => ty
  | .ifThenElse _ _ _ ty => ty
  | .letIn _ _ body => body.ty
  | .ref e => .ref e.ty
  | .deref _ ty => ty
  | .store _ _ => .unit
  | .assert _ => .unit
  | .tuple es => .tuple (es.map Expr.ty)
  | .inj tag arity e => .sum ((List.replicate arity .empty).set tag e.ty)
  | .match_ _ _ ty => ty
  | .cast _ ty => ty

structure ValDecl (S : Type) where
  name : Binder
  body : Expr
  spec : Option S
  deriving Repr, BEq

instance [Inhabited S] : Inhabited (ValDecl S) := ⟨{ name := default, body := default, spec := default }⟩

def ValDecl.mapSpec {S T : Type} (f : S → Option T) (d : ValDecl S) : ValDecl T :=
  { name := d.name, body := d.body, spec := d.spec.bind f }

abbrev Program (S : Type) := List (ValDecl S)

def Binder.runtime : Typed.Binder → Runtime.Binder
  | ⟨Option.none, _⟩ => .none
  | ⟨some x, _⟩ => .named x

@[simp] theorem Binder.runtime_of_name_none {b : Typed.Binder}
    (h : b.name = Option.none) : b.runtime = .none := by
  cases b with
  | mk name ty =>
    cases name with
    | none =>
      simp [Binder.runtime]
    | some x =>
      simp at h

@[simp] theorem Binder.runtime_of_name_some {b : Typed.Binder} {x : TinyML.Var}
    (h : b.name = Option.some x) : b.runtime = .named x := by
  cases b with
  | mk name ty =>
    cases name with
    | none =>
      simp at h
    | some y =>
      simp at h
      subst h
      simp [Binder.runtime]

def Expr.runtime : Typed.Expr → Runtime.Expr
  | .const c => .val (Runtime.Val.ofConst c)
  | .var x _ => .var x
  | .unop op e _ => .unop op e.runtime
  | .binop op l r _ => .binop op l.runtime r.runtime
  | .fix self args _ body => .fix (self.runtime) (args.map (·.runtime)) body.runtime
  | .app fn args _ => .app fn.runtime (args.map Expr.runtime)
  | .ifThenElse c t e _ => .ifThenElse c.runtime t.runtime e.runtime
  | .letIn b bound body => .letIn (b.runtime) bound.runtime body.runtime
  | .ref e => .ref e.runtime
  | .deref e _ => .deref e.runtime
  | .store loc val => .store loc.runtime val.runtime
  | .assert e => .assert e.runtime
  | .tuple es => .tuple (es.map Expr.runtime)
  | .inj tag arity payload => .inj tag arity payload.runtime
  | .match_ scrut branches _ => .match_ scrut.runtime (branchListRuntime branches)
  | .cast e _ => e.runtime
where
  branchListRuntime : List (Typed.Binder × Typed.Expr) → List Runtime.Expr
    | [] => []
    | (b, e) :: rest => Runtime.Expr.fix .none [b.runtime] e.runtime :: branchListRuntime rest

def ValDecl.runtime {S : Type} (d : Typed.ValDecl S) : Runtime.Decl :=
  { name := d.name.runtime, body := d.body.runtime }

def Program.runtime {S : Type} (prog : Typed.Program S) : Runtime.Program :=
  prog.map ValDecl.runtime

theorem Expr.branchListRuntime_eq_map (branches : List (Typed.Binder × Typed.Expr)) :
    Expr.runtime.branchListRuntime branches =
      branches.map fun p => Runtime.Expr.fix .none [p.1.runtime] p.2.runtime := by
  induction branches with
  | nil => unfold Expr.runtime.branchListRuntime; rfl
  | cons hd rest ih =>
    obtain ⟨b, e⟩ := hd
    unfold Expr.runtime.branchListRuntime
    simp only [List.map_cons]
    congr 1

theorem Expr.branchListRuntime_castBodies (ty : TinyML.Typ) (branches : List (Typed.Binder × Typed.Expr)) :
    Expr.runtime.branchListRuntime
      (branches.map fun p => (p.1, if p.2.ty = ty then p.2 else .cast p.2 ty)) =
    Expr.runtime.branchListRuntime branches := by
  induction branches with
  | nil =>
    simp [Expr.runtime.branchListRuntime]
  | cons hd rest ih =>
    obtain ⟨b, e⟩ := hd
    unfold Expr.runtime.branchListRuntime
    simp only [List.map_cons]
    by_cases h : e.ty = ty
    · simp [h, ih]
    · simp [Expr.runtime, h, ih]

end Typed
