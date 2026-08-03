-- SUMMARY: Typed TinyML IR, with erasure to the runtime IR.
import Mica.TinyML.Common
import Mica.SourceTinyML.Types
import Mica.TinyML.RuntimeExpr

namespace Typed

open TinyML

/-- A binder, parameterized by the variables its type annotation admits, in step
with `Typ.WithTypeVars`. -/
structure Binder.WithTypeVars (V : Type) where
  name : Option TinyML.Var
  ty : Typ.WithTypeVars V
  deriving Repr

/-- The binder of the typed IR the verifier consumes. -/
abbrev Binder := Binder.WithTypeVars Empty

instance : Inhabited Binder := ⟨⟨Option.none, .value⟩⟩

instance {V : Type} [DecidableEq V] : DecidableEq (Binder.WithTypeVars V) := by
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

def Binder.named (name : TinyML.Var) (ty : Typ) : Binder := ⟨some name, ty⟩

instance {V : Type} [DecidableEq V] : BEq (Binder.WithTypeVars V) :=
  ⟨fun a b => decide (a = b)⟩

instance {V : Type} [DecidableEq V] : LawfulBEq (Binder.WithTypeVars V) where
  eq_of_beq {a b} h := by
    exact of_decide_eq_true h
  rfl {a} := by
    simp [BEq.beq]

/-- The typed IR, parameterized by the variables its type annotations admit. -/
inductive Expr.WithTypeVars (V : Type) where
  | const (c : Const)
  | var (name : TinyML.Var) (ty : Typ.WithTypeVars V)
  /-- Reference to a built-in primitive, indexed by name. `inst` is the
      type-variable instantiation solved at the use site; `ty` is the
      instantiated arrow type derived from the registry's scheme. -/
  | prim (name : String) (inst : List (TyVar × Typ.WithTypeVars V))
      (ty : Typ.WithTypeVars V)
  | unop (op : UnOp) (e : WithTypeVars V) (ty : Typ.WithTypeVars V)
  | binop (op : BinOp) (lhs rhs : WithTypeVars V) (ty : Typ.WithTypeVars V)
  /-- A function literal. `spec` is the specification the function was checked
      against, which is also what `Expr.ty` puts in the node's arrow type; the
      self binder carries the same arrow. -/
  | fix (self : Binder.WithTypeVars V) (args : List (Binder.WithTypeVars V))
      (retTy : Typ.WithTypeVars V) (spec : Option (Spec (Typ.WithTypeVars V)))
      (body : WithTypeVars V)
  | app (fn : WithTypeVars V) (args : List (WithTypeVars V)) (ty : Typ.WithTypeVars V)
  | ifThenElse (cond thn els : WithTypeVars V) (ty : Typ.WithTypeVars V)
  | letIn (name : Binder.WithTypeVars V) (bound body : WithTypeVars V)
  | letProd (names : List (Binder.WithTypeVars V)) (bound body : WithTypeVars V)
  | ref    (ownership : Ownership) (e : WithTypeVars V)
  | deref  (e : WithTypeVars V) (ty : Typ.WithTypeVars V)
  | store  (loc val : WithTypeVars V)
  | arrayMake (ownership : Ownership) (len init : WithTypeVars V)
  | arrayLen (arr : WithTypeVars V)
  | arrayGet (arr idx : WithTypeVars V) (ty : Typ.WithTypeVars V)
  | arraySet (arr idx val : WithTypeVars V)
  | assert (e : WithTypeVars V)
  | tuple (es : List (WithTypeVars V))
  /-- `ty` is the sum injected into; the verifier checks that its `tag`-th
      component is the payload's type. -/
  | inj (tag : Nat) (arity : Nat) (payload : WithTypeVars V) (ty : Typ.WithTypeVars V)
  | match_ (scrutinee : WithTypeVars V)
      (branches : List (Binder.WithTypeVars V × WithTypeVars V)) (ty : Typ.WithTypeVars V)
  | cast (e : WithTypeVars V) (ty : Typ.WithTypeVars V)

/-- The typed IR the verifier consumes. Its annotations are closed types. -/
abbrev Expr := Expr.WithTypeVars Empty

namespace Expr
-- As for `Typ`: `.fix` resolves in the inductive's namespace, `Expr.fix` in the
-- one named after the syntax it usually builds.
export WithTypeVars (const var prim unop binop fix app ifThenElse letIn letProd
  ref deref store arrayMake arrayLen arrayGet arraySet assert tuple inj match_ cast)
end Expr

instance : Inhabited Expr := ⟨.const .unit⟩

/-- Is the expression a function (fix) node? -/
def Expr.WithTypeVars.isFunc : Expr.WithTypeVars V → Bool
  | .fix .. => true
  | _ => false

@[simp] theorem Expr.isFunc_fix {self : Binder.WithTypeVars V}
    {args : List (Binder.WithTypeVars V)} {retTy : Typ.WithTypeVars V}
    {spec : Option (Spec (Typ.WithTypeVars V))} {body : Expr.WithTypeVars V} :
    (Expr.WithTypeVars.fix self args retTy spec body).isFunc = true := rfl

theorem Expr.isFunc_elim {e : Expr.WithTypeVars V} (h : e.isFunc = true) :
    ∃ self args retTy spec body, e = .fix self args retTy spec body := by
  cases e <;> simp [Expr.WithTypeVars.isFunc] at h
  exact ⟨_, _, _, _, _, rfl⟩

-- `deriving DecidableEq` does not support mutual inductives with `List`-nested
-- recursion, so we define the instance by hand.
mutual
  private def Expr.WithTypeVars.decEq {V : Type} [DecidableEq V]
      (a b : Expr.WithTypeVars V) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | exact isFalse (by omega) | skip
    -- Once the inductive has a parameter, `noConfusion` takes a type equality
    -- and an `HEq` rather than the plain disequality this used, so the
    -- mismatched-constructor cases are discharged by elimination instead.
    all_goals first | (refine isFalse ?_; intro h; cases h; done) | skip
    case const.const c1 c2 => exact match decEq c1 c2 with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case var.var n1 t1 n2 t2 => exact match decEq n1 n2, decEq t1 t2 with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case prim.prim n1 i1 t1 n2 i2 t2 =>
      exact match decEq n1 n2, decEq i1 i2, decEq t1 t2 with
      | isTrue h1, isTrue h2, isTrue h3 =>
          isTrue (by subst h1; subst h2; subst h3; rfl)
      | isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
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
    case fix.fix s1 args1 rt1 sp1 b1 s2 args2 rt2 sp2 b2 =>
      exact match decEq s1 s2, decEq args1 args2, decEq rt1 rt2, decEq sp1 sp2, b1.decEq b2 with
      | isTrue h1, isTrue h2, isTrue h3, isTrue h4, isTrue h5 =>
        isTrue (by subst h1; subst h2; subst h3; subst h4; subst h5; rfl)
      | isFalse h, _, _, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h, _, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
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
    case letProd.letProd bs1 d1 y1 bs2 d2 y2 => exact match decEq bs1 bs2, d1.decEq d2, y1.decEq y2 with
      | isTrue h1, isTrue h2, isTrue h3 => isTrue (by subst h1; subst h2; subst h3; rfl)
      | isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case ref.ref o1 e1 o2 e2 => exact match decEq o1 o2, e1.decEq e2 with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case deref.deref e1 t1 e2 t2 => exact match e1.decEq e2, decEq t1 t2 with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case store.store l1 v1 l2 v2 => exact match l1.decEq l2, v1.decEq v2 with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case arrayMake.arrayMake o1 n1 v1 o2 n2 v2 => exact match decEq o1 o2, n1.decEq n2, v1.decEq v2 with
      | isTrue h0, isTrue h1, isTrue h2 => isTrue (by subst h0; subst h1; subst h2; rfl)
      | isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case arrayLen.arrayLen a1 a2 => exact match a1.decEq a2 with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case arrayGet.arrayGet a1 i1 t1 a2 i2 t2 => exact match a1.decEq a2, i1.decEq i2, decEq t1 t2 with
      | isTrue h1, isTrue h2, isTrue h3 => isTrue (by subst h1; subst h2; subst h3; rfl)
      | isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case arraySet.arraySet a1 i1 v1 a2 i2 v2 => exact match a1.decEq a2, i1.decEq i2, v1.decEq v2 with
      | isTrue h1, isTrue h2, isTrue h3 => isTrue (by subst h1; subst h2; subst h3; rfl)
      | isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case assert.assert e1 e2 => exact match e1.decEq e2 with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case tuple.tuple es1 es2 =>
      exact match exprsDecEq es1 es2 with
      | isTrue h => isTrue (by subst h; rfl)
      | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    case inj.inj t1 a1 p1 ty1 t2 a2 p2 ty2 =>
      exact match decEq t1 t2, decEq a1 a2, Expr.WithTypeVars.decEq p1 p2, decEq ty1 ty2 with
      | isTrue h1, isTrue h2, isTrue h3, isTrue h4 =>
        isTrue (by subst h1; subst h2; subst h3; subst h4; rfl)
      | isFalse h, _, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
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

  private def exprsDecEq {V : Type} [DecidableEq V] :
      (as bs : List (Expr.WithTypeVars V)) → Decidable (as = bs)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
    | a :: as, b :: bs => match a.decEq b, exprsDecEq as bs with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)

  private def branchDecEq {V : Type} [DecidableEq V] :
      (a b : Binder.WithTypeVars V × Expr.WithTypeVars V) → Decidable (a = b)
    | (b1, e1), (b2, e2) => match decEq b1 b2, e1.decEq e2 with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)

  private def branchesDecEq {V : Type} [DecidableEq V] :
      (as bs : List (Binder.WithTypeVars V × Expr.WithTypeVars V)) → Decidable (as = bs)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
    | a :: as, b :: bs => match branchDecEq a b, branchesDecEq as bs with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
end

instance {V : Type} [DecidableEq V] : DecidableEq (Expr.WithTypeVars V) :=
  Expr.WithTypeVars.decEq

deriving instance Repr for Expr.WithTypeVars

instance {V : Type} [DecidableEq V] : BEq (Expr.WithTypeVars V) :=
  ⟨fun a b => decide (a = b)⟩

instance {V : Type} [DecidableEq V] : LawfulBEq (Expr.WithTypeVars V) where
  eq_of_beq h := of_decide_eq_true h
  rfl := by simp [BEq.beq]

abbrev Vars := List TinyML.Var
abbrev Exprs := List Expr
abbrev Binders := List Binder

def Const.ty : Const → Typ.WithTypeVars V
  | .int _ => .int
  | .bool _ => .bool
  | .char _ => .char
  | .string _ => .string
  | .float _ => .float
  | .unit => .unit

def Expr.WithTypeVars.ty : Expr.WithTypeVars V → Typ.WithTypeVars V
  | .const c => Const.ty c
  | .var _ ty => ty
  | .prim _ _ ty => ty
  | .unop _ _ ty => ty
  | .binop _ _ _ ty => ty
  | .fix _ args retTy spec _ => .arrow (args.map (·.ty)) retTy spec
  | .app _ _ ty => ty
  | .ifThenElse _ _ _ ty => ty
  | .letIn _ _ body => body.ty
  | .letProd _ _ body => body.ty
  | .ref .owned e => .owned e.ty
  | .ref .shared e => .ref e.ty
  | .deref _ ty => ty
  | .store _ _ => .unit
  | .arrayMake .owned _ init => .ownedArray init.ty
  | .arrayMake .shared _ init => .array init.ty
  | .arrayLen _ => .int
  | .arrayGet _ _ ty => ty
  | .arraySet _ _ _ => .unit
  | .assert _ => .unit
  | .tuple es => .tuple (es.map Expr.WithTypeVars.ty)
  | .inj _ _ _ ty => ty
  | .match_ _ _ ty => ty
  | .cast _ ty => ty

/-- The specification a function literal was elaborated against, if any. This
is where a declaration's specification lives, together with its arrow type. -/
def Expr.WithTypeVars.spec? : Expr.WithTypeVars V → Option (Spec (Typ.WithTypeVars V))
  | .fix _ _ _ spec _ => spec
  | _ => none

@[simp] theorem Expr.spec?_fix (self : Binder.WithTypeVars V)
    (args : List (Binder.WithTypeVars V)) (retTy : Typ.WithTypeVars V)
    (spec : Option (Spec (Typ.WithTypeVars V))) (body : Expr.WithTypeVars V) :
    (Expr.WithTypeVars.fix self args retTy spec body).spec? = spec := rfl

/-- A checked declaration. It carries no specification of its own: the literal
it binds records the specification it was elaborated against, and so does the
declaration's arrow type. -/
structure ValDecl where
  name : Binder
  body : Expr
  /-- The spec-level relation this declaration is registered as, if `[@@fn]`. -/
  relation : Option String := none
  deriving Repr, BEq, Inhabited

abbrev Program := List ValDecl

def Binder.WithTypeVars.runtime : Typed.Binder.WithTypeVars V → Runtime.Binder
  | ⟨Option.none, _⟩ => .none
  | ⟨some x, _⟩ => .named x

@[simp] theorem Binder.runtime_of_name_none {b : Typed.Binder.WithTypeVars V}
    (h : b.name = Option.none) : b.runtime = .none := by
  cases b with
  | mk name ty =>
    cases name with
    | none =>
      simp [Binder.WithTypeVars.runtime]
    | some x =>
      simp at h

@[simp] theorem Binder.runtime_of_name_some {b : Typed.Binder.WithTypeVars V}
    {x : TinyML.Var} (h : b.name = Option.some x) : b.runtime = .named x := by
  cases b with
  | mk name ty =>
    cases name with
    | none =>
      simp at h
    | some y =>
      simp at h
      subst h
      simp [Binder.WithTypeVars.runtime]

mutual
  def Expr.WithTypeVars.runtime : Typed.Expr.WithTypeVars V → Runtime.Expr
    | .const c => .val (Runtime.Val.ofConst c)
    | .var x _ => .var x
    | .prim n _ _ => .val (.prim n)
    | .unop op e _ => .unop op e.runtime
    | .binop op l r _ => .binop op l.runtime r.runtime
    | .fix self args _ _ body => .fix (self.runtime) (args.map (·.runtime)) body.runtime
    | .app fn args _ => .app fn.runtime (args.map Expr.WithTypeVars.runtime)
    | .ifThenElse c t e _ => .ifThenElse c.runtime t.runtime e.runtime
    | .letIn b bound body => .letIn (b.runtime) bound.runtime body.runtime
    | .letProd bs bound body => .letProd (bs.map (·.runtime)) bound.runtime body.runtime
    | .ref _ e => .ref e.runtime
    | .deref e _ => .deref e.runtime
    | .store loc val => .store loc.runtime val.runtime
    | .arrayMake _ len init => .arrayMake len.runtime init.runtime
    | .arrayLen arr => .arrayLen arr.runtime
    | .arrayGet arr idx _ => .arrayGet arr.runtime idx.runtime
    | .arraySet arr idx val => .arraySet arr.runtime idx.runtime val.runtime
    | .assert e => .assert e.runtime
    | .tuple es => .tuple (es.map Expr.WithTypeVars.runtime)
    | .inj tag arity payload _ => .inj tag arity payload.runtime
    | .match_ scrut branches _ =>
        .match_ scrut.runtime (Expr.WithTypeVars.branchListRuntime branches)
    | .cast e _ => e.runtime

  /-- Erase `match_` branches to their runtime closures used by `Expr.runtime`. -/
  def Expr.WithTypeVars.branchListRuntime :
      List (Typed.Binder.WithTypeVars V × Typed.Expr.WithTypeVars V) → List Runtime.Expr
    | [] => []
    | (b, e) :: rest =>
        Runtime.Expr.fix .none [b.runtime] e.runtime
          :: Expr.WithTypeVars.branchListRuntime rest
end

def ValDecl.runtime (d : Typed.ValDecl) : Runtime.Decl :=
  { name := d.name.runtime, body := d.body.runtime }

def Program.runtime (prog : Typed.Program) : Runtime.Program :=
  prog.map ValDecl.runtime

theorem Expr.branchListRuntime_eq_map
    (branches : List (Typed.Binder.WithTypeVars V × Typed.Expr.WithTypeVars V)) :
    Expr.WithTypeVars.branchListRuntime branches =
      branches.map fun p => Runtime.Expr.fix .none [p.1.runtime] p.2.runtime := by
  induction branches with
  | nil => unfold Expr.WithTypeVars.branchListRuntime; rfl
  | cons hd rest ih =>
    obtain ⟨b, e⟩ := hd
    unfold Expr.WithTypeVars.branchListRuntime
    simp only [List.map_cons]
    congr 1

theorem Expr.branchListRuntime_castBodies [DecidableEq V] (ty : Typ.WithTypeVars V)
    (branches : List (Typed.Binder.WithTypeVars V × Typed.Expr.WithTypeVars V)) :
    Expr.WithTypeVars.branchListRuntime
      (branches.map fun p => (p.1, if p.2.ty = ty then p.2 else .cast p.2 ty)) =
    Expr.WithTypeVars.branchListRuntime branches := by
  induction branches with
  | nil =>
    simp [Expr.WithTypeVars.branchListRuntime]
  | cons hd rest ih =>
    obtain ⟨b, e⟩ := hd
    unfold Expr.WithTypeVars.branchListRuntime
    simp only [List.map_cons]
    by_cases h : e.ty = ty
    · simp [h, ih]
    · simp [Expr.WithTypeVars.runtime, h, ih]

end Typed
