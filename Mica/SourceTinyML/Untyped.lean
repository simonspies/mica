-- SUMMARY: Untyped TinyML IR and specification syntax, with annotations carried where available.
import Mica.TinyML.Common
import Mica.SourceTinyML.Types
import Mica.TinyML.RuntimeExpr

/-!
# Untyped IR

The IR the frontend elaborates into, together with the syntax of the
specifications written in it. `SpecParser` recognises a specification's control
structure (`assert`, `let`, predicate `bind`, `ite`, `ret`) and keeps the
embedded leaf expressions as ordinary untyped terms; typing turns the whole
thing into a completed `Spec Typ` (`Assertions.lean`).
-/

namespace Spec

/-- Specification predicates. Each names a spec-level variable already in
scope, whose encoded value the translator looks up directly. -/
inductive Pred where
  | isinj (tag arity : Nat) (scrut : String)
  | own (loc : String)
  /-- Ownership of a mutable array `loc`, binding its vector snapshot. -/
  | arr (loc : String)
  deriving Inhabited

/-- The assertion language, parametric in the embedded leaf expression type `ε`
(used by `assert`, `let_`, and `ite`). Only `ε := Untyped.Expr` occurs in
practice. -/
inductive Assert (ε : Type) : Type → Type where
  | ret (val : α) : Assert ε α
  | assert (cond : ε) (rest : Assert ε α) : Assert ε α
  | let_ (name : String) (val : ε) (rest : Assert ε α) : Assert ε α
  /-- Bind the value a predicate exposes. An ownership snapshot is data, never
  a function, so its annotation is a core type. -/
  | bind (p : Pred) (name : String) (ty : TinyML.Typ) (rest : Assert ε α) : Assert ε α
  | ite (cond : ε) (thn els : Assert ε α) : Assert ε α

instance [Inhabited α] : Inhabited (Assert ε α) := ⟨.ret default⟩

/-- The postcondition of a specification: the name bound to the result value,
together with the assertion that must hold of it. A structure, because a nested
inductive may not occur inside its own type parameter. -/
structure Post (ε : Type) where
  name : String
  body : Assert ε Unit

abbrev Pre (ε : Type) := Assert ε (Post ε)

/-- A spec body as written: the argument names it binds, together with the
precondition. Typing turns it into a completed `Spec` (`Assertions.lean`). -/
structure Body (ε : Type) where
  args : List String
  pre : Assert ε (Post ε)

end Spec

namespace Untyped

open TinyML

inductive Binder where
  | none
  | named (name : TinyML.Var) (ty : Option Typ)
  deriving Repr, Inhabited

inductive Expr where
  | const (c : Const)
  | var (name : TinyML.Var)
  /-- Reference to a built-in primitive, indexed by name. Resolved from a
      qualified path by the frontend; the registry (threaded through typing)
      is the source of its type scheme. -/
  | prim (name : String)
  | unop (op : UnOp) (e : Expr)
  | binop (op : BinOp) (lhs rhs : Expr)
  | fix (self : Binder) (args : List Binder) (retTy : Option Typ) (body : Expr)
  | app (fn : Expr) (args : List Expr)
  | ifThenElse (cond thn els : Expr)
  | letIn (name : Binder) (bound body : Expr)
  | letProd (names : List Binder) (bound body : Expr)
  | ref    (ownership : Ownership) (e : Expr)
  | deref  (e : Expr)
  | store  (loc val : Expr)
  | arrayMake (ownership : Ownership) (len init : Expr)
  | arrayLen (arr : Expr)
  | arrayGet (arr idx : Expr)
  | arraySet (arr idx val : Expr)
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


deriving instance Repr for Expr

abbrev Vars := List TinyML.Var
abbrev Exprs := List Expr
abbrev Binders := List Binder

structure ValDecl (S : Type) where
  name : Binder
  body : Expr
  declMeta : DeclMeta S
  deriving Repr, Inhabited

def ValDecl.mapSpec {S T : Type} (f : S → Option T) (d : ValDecl S) : ValDecl T :=
  { name := d.name, body := d.body, declMeta := d.declMeta.mapSpec f }

structure TypeDecl where
  name : TypeName
  body : DataDecl
  deriving Repr, Inhabited

inductive Decl (S : Type) where
  | val_ (d : ValDecl S)
  | type_ (d : TypeDecl)
  deriving Repr, Inhabited

def Decl.mapSpec {S T : Type} (f : S → Option T) : Decl S → Decl T
  | .val_ d => .val_ (d.mapSpec f)
  | .type_ d => .type_ d

abbrev Program (S : Type) := List (Decl S)

def Binder.runtime : Untyped.Binder → Runtime.Binder
  | .none => .none
  | .named x _ty => .named x

/-- The primitive name of a bare primitive reference, `none` otherwise. Lets
    callers dispatch on "is this a primitive" without matching on `Expr`. -/
def Expr.primName? : Expr → Option String
  | .prim n => some n
  | _ => none


def Expr.runtime : Untyped.Expr → Runtime.Expr
  | .const c => .val (Runtime.Val.ofConst c)
  | .var x => .var x
  | .prim n => .val (.prim n)
  | .unop op e => .unop op e.runtime
  | .binop op l r => .binop op l.runtime r.runtime
  | .fix self args _ body => .fix (self.runtime) (args.map (·.runtime)) body.runtime
  | .app fn args => .app fn.runtime (args.map Expr.runtime)
  | .ifThenElse c t e => .ifThenElse c.runtime t.runtime e.runtime
  | .letIn b bound body => .letIn (b.runtime) bound.runtime body.runtime
  | .letProd bs bound body => .letProd (bs.map (·.runtime)) bound.runtime body.runtime
  | .ref _ e => .ref e.runtime
  | .deref e => .deref e.runtime
  | .store loc val => .store loc.runtime val.runtime
  | .arrayMake _ len init => .arrayMake len.runtime init.runtime
  | .arrayLen arr => .arrayLen arr.runtime
  | .arrayGet arr idx => .arrayGet arr.runtime idx.runtime
  | .arraySet arr idx val => .arraySet arr.runtime idx.runtime val.runtime
  | .assert e => .assert e.runtime
  | .tuple es => .tuple (es.map Expr.runtime)
  | .inj tag arity payload => .inj tag arity payload.runtime
  | .match_ scrut branches => .match_ scrut.runtime (branchListRuntime branches)
where
  branchListRuntime : List (Untyped.Binder × Untyped.Expr) → List Runtime.Expr
    | [] => []
    | (b, e) :: rest => Runtime.Expr.fix .none [b.runtime] e.runtime :: branchListRuntime rest

theorem Expr.primName?_runtime {e : Expr} {n : String}
    (h : e.primName? = some n) : e.runtime = .val (.prim n) := by
  cases e <;> simp_all [Expr.primName?, Expr.runtime]

def ValDecl.runtime {S : Type} (d : Untyped.ValDecl S) : Runtime.Decl :=
  { name := d.name.runtime, body := d.body.runtime }

def Decl.runtime {S : Type} : Untyped.Decl S → Option Runtime.Decl
  | .val_ d => some d.runtime
  | .type_ _ => none

def Program.runtime {S : Type} (prog : Untyped.Program S) : Runtime.Program :=
  prog.filterMap Decl.runtime

end Untyped
