import Mica.TinyML.RuntimeExpr
import Mica.TinyML.Typed
import Mica.TinyML.Untyped

namespace TinyML

def Const.runtime : TinyML.Const → Runtime.Val
  | .int n  => .int n
  | .bool b => .bool b
  | .unit   => .unit

end TinyML

namespace Typed

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
  | .const c => .val c.runtime
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

def Decl.runtime {S : Type} : Typed.Decl S → Option Runtime.Decl
  | .val_ d => some d.runtime
  | .type_ _ => none

def Program.runtime {S : Type} (prog : Typed.Program S) : Runtime.Program :=
  prog.filterMap Decl.runtime

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

namespace Untyped

def Binder.runtime : Untyped.Binder → Runtime.Binder
  | .none => .none
  | .named x _ty => .named x

def Expr.runtime : Untyped.Expr → Runtime.Expr
  | .const c => .val c.runtime
  | .var x => .var x
  | .unop op e => .unop op e.runtime
  | .binop op l r => .binop op l.runtime r.runtime
  | .fix self args _ body => .fix (self.runtime) (args.map (·.runtime)) body.runtime
  | .app fn args => .app fn.runtime (args.map Expr.runtime)
  | .ifThenElse c t e => .ifThenElse c.runtime t.runtime e.runtime
  | .letIn b bound body => .letIn (b.runtime) bound.runtime body.runtime
  | .ref e => .ref e.runtime
  | .deref e => .deref e.runtime
  | .store loc val => .store loc.runtime val.runtime
  | .assert e => .assert e.runtime
  | .tuple es => .tuple (es.map Expr.runtime)
  | .inj tag arity payload => .inj tag arity payload.runtime
  | .match_ scrut branches => .match_ scrut.runtime (branchListRuntime branches)
where
  branchListRuntime : List (Untyped.Binder × Untyped.Expr) → List Runtime.Expr
    | [] => []
    | (b, e) :: rest => Runtime.Expr.fix .none [b.runtime] e.runtime :: branchListRuntime rest

def ValDecl.runtime {S : Type} (d : Untyped.ValDecl S) : Runtime.Decl :=
  { name := d.name.runtime, body := d.body.runtime }

def Decl.runtime {S : Type} : Untyped.Decl S → Option Runtime.Decl
  | .val_ d => some d.runtime
  | .type_ _ => none

def Program.runtime {S : Type} (prog : Untyped.Program S) : Runtime.Program :=
  prog.filterMap Decl.runtime

end Untyped
