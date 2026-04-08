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
  | .none => .none
  | .named x _ty => .named x

def Expr.runtime : Typed.Expr → Runtime.Expr
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
  branchListRuntime : List (Typed.Binder × Typed.Expr) → List Runtime.Expr
    | [] => []
    | (b, e) :: rest => Runtime.Expr.fix .none [b.runtime] e.runtime :: branchListRuntime rest

def Decl.runtime {S : Type} (d : Typed.Decl S) : Runtime.Decl :=
  { name := d.name.runtime, body := d.body.runtime }

def Program.runtime {S : Type} (prog : Typed.Program S) : Runtime.Program :=
  prog.map Decl.runtime

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

def Decl.runtime {S : Type} (d : Untyped.Decl S) : Runtime.Decl :=
  { name := d.name.runtime, body := d.body.runtime }

def Program.runtime {S : Type} (prog : Untyped.Program S) : Runtime.Program :=
  prog.map Decl.runtime

end Untyped

/-! ### elaborate_runtime: elaboration commutes with erasure to runtime -/

theorem Typed.Binder.elaborate_runtime (b : Untyped.Binder) :
    (Typed.Binder.elaborate b).runtime = b.runtime := by
  cases b <;> simp [Typed.Binder.elaborate, Typed.Binder.runtime, Untyped.Binder.runtime]

private theorem Typed.Exprs.elaborate_map (es : List Untyped.Expr) :
    Typed.Exprs.elaborate es = es.map Typed.Expr.elaborate := by
  induction es with
  | nil => simp [Typed.Exprs.elaborate]
  | cons e rest ih => simp [Typed.Exprs.elaborate, ih]

private theorem Typed.Branches.elaborate_map
    (bs : List (Untyped.Binder × Untyped.Expr)) :
    Typed.Branches.elaborate bs =
    bs.map (fun p => (Typed.Binder.elaborate p.1, Typed.Expr.elaborate p.2)) := by
  induction bs with
  | nil => simp [Typed.Branches.elaborate]
  | cons hd rest ih =>
    obtain ⟨b, e⟩ := hd
    simp [Typed.Branches.elaborate, ih]

mutual
  private theorem elaborate_runtime_expr (e : Untyped.Expr) :
      (Typed.Expr.elaborate e).runtime = e.runtime := by
    cases e with
    | const c => simp [Typed.Expr.elaborate, Typed.Expr.runtime, Untyped.Expr.runtime]
    | var x => simp [Typed.Expr.elaborate, Typed.Expr.runtime, Untyped.Expr.runtime]
    | unop op e =>
      simp [Typed.Expr.elaborate, Typed.Expr.runtime, Untyped.Expr.runtime,
            elaborate_runtime_expr e]
    | binop op l r =>
      simp [Typed.Expr.elaborate, Typed.Expr.runtime, Untyped.Expr.runtime,
            elaborate_runtime_expr l, elaborate_runtime_expr r]
    | fix self args retTy body =>
      simp only [Typed.Expr.elaborate, Typed.Expr.runtime, Untyped.Expr.runtime,
                 elaborate_runtime_expr body, List.map_map]
      congr 1
      · exact Typed.Binder.elaborate_runtime self
      · apply List.map_congr_left; intro b _; exact Typed.Binder.elaborate_runtime b
    | app fn args =>
      simp only [Typed.Expr.elaborate, Typed.Exprs.elaborate_map,
                 Typed.Expr.runtime, Untyped.Expr.runtime, elaborate_runtime_expr fn]
      congr 1
      rw [List.map_map]
      exact elaborate_runtime_list args
    | ifThenElse c t e =>
      simp [Typed.Expr.elaborate, Typed.Expr.runtime, Untyped.Expr.runtime,
            elaborate_runtime_expr c, elaborate_runtime_expr t, elaborate_runtime_expr e]
    | letIn b bound body =>
      simp [Typed.Expr.elaborate, Typed.Expr.runtime, Untyped.Expr.runtime,
            Typed.Binder.elaborate_runtime, elaborate_runtime_expr bound,
            elaborate_runtime_expr body]
    | ref e =>
      simp [Typed.Expr.elaborate, Typed.Expr.runtime, Untyped.Expr.runtime,
            elaborate_runtime_expr e]
    | deref e =>
      simp [Typed.Expr.elaborate, Typed.Expr.runtime, Untyped.Expr.runtime,
            elaborate_runtime_expr e]
    | store loc val =>
      simp [Typed.Expr.elaborate, Typed.Expr.runtime, Untyped.Expr.runtime,
            elaborate_runtime_expr loc, elaborate_runtime_expr val]
    | assert e =>
      simp [Typed.Expr.elaborate, Typed.Expr.runtime, Untyped.Expr.runtime,
            elaborate_runtime_expr e]
    | tuple es =>
      simp only [Typed.Expr.elaborate, Typed.Exprs.elaborate_map,
                 Typed.Expr.runtime, Untyped.Expr.runtime]
      congr 1
      rw [List.map_map]
      exact elaborate_runtime_list es
    | inj tag arity payload =>
      simp [Typed.Expr.elaborate, Typed.Expr.runtime, Untyped.Expr.runtime,
            elaborate_runtime_expr payload]
    | match_ scrut branches =>
      simp only [Typed.Expr.elaborate, Typed.Branches.elaborate_map,
                 Typed.Expr.runtime, Untyped.Expr.runtime, elaborate_runtime_expr scrut]
      congr 1
      exact elaborate_runtime_branches branches

  private theorem elaborate_runtime_list : (es : List Untyped.Expr) →
      es.map (Typed.Expr.runtime ∘ Typed.Expr.elaborate) = es.map Untyped.Expr.runtime
    | [] => rfl
    | e :: rest => by
        simp only [List.map_cons, Function.comp,
                   elaborate_runtime_expr e, elaborate_runtime_list rest]

  private theorem elaborate_runtime_branches : (bs : List (Untyped.Binder × Untyped.Expr)) →
      Typed.Expr.runtime.branchListRuntime
        (bs.map (fun p => (Typed.Binder.elaborate p.1, Typed.Expr.elaborate p.2))) =
      Untyped.Expr.runtime.branchListRuntime bs
    | [] => by simp [Typed.Expr.runtime.branchListRuntime, Untyped.Expr.runtime.branchListRuntime]
    | (b, e) :: rest => by
        simp only [List.map_cons, Typed.Expr.runtime.branchListRuntime,
                   Untyped.Expr.runtime.branchListRuntime,
                   Typed.Binder.elaborate_runtime, elaborate_runtime_expr e,
                   elaborate_runtime_branches rest]
end

theorem Typed.Expr.elaborate_runtime (e : Untyped.Expr) :
    (Typed.Expr.elaborate e).runtime = e.runtime :=
  elaborate_runtime_expr e

theorem Typed.Program.elaborate_runtime {S : Type} (prog : Untyped.Program S) :
    (Typed.Program.elaborate prog).runtime = prog.runtime := by
  simp only [Typed.Program.elaborate, Typed.Program.runtime, Untyped.Program.runtime,
             List.map_map]
  apply List.map_congr_left
  intro d _
  cases d.spec <;>
    simp [Function.comp, Typed.Decl.elaborate, Typed.Decl.runtime, Untyped.Decl.runtime,
      Typed.Binder.elaborate_runtime, Typed.Expr.elaborate_runtime]
