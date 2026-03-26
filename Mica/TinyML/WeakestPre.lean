import Mica.TinyML.Expr
import Mica.TinyML.RuntimeExpr
import Mica.TinyML.OpSem

/-! ## WP Calculus

Weakest precondition axioms for the TinyML expression language.
These axioms encode the semantics of various expression forms.
-/

axiom wp : Runtime.Expr → (Runtime.Val → Prop) → Prop

/-- Weakest precondition for a list of expressions, evaluated right-to-left.
    `wps [e1, e2, e3] Q` first evaluates `e3`, then `e2`, then `e1`,
    and passes `[v1, v2, v3]` (in original order) to `Q`. -/
def wps : Runtime.Exprs → (Runtime.Vals → Prop) → Prop
  | [], Q => Q []
  | e :: es, Q => wps es (fun vs => wp e (fun v => Q (v :: vs)))

axiom wp.val {v : Runtime.Val} {Q : Runtime.Val → Prop} : Q v → wp (.val v) Q
axiom wp.binop {op : TinyML.BinOp} {l r : Runtime.Expr} {Q : Runtime.Val → Prop} :
    wp l (fun vl => wp r (fun vr => ∃ r, TinyML.evalBinOp op vl vr = some r ∧ Q r)) →
    wp (.binop op l r) Q
axiom wp.letIn {b : Runtime.Binder} {e body : Runtime.Expr} {Q : Runtime.Val → Prop} :
    wp e (fun v => wp (body.subst (fun z => match b with
      | .named x => if z == x then some v else none
      | .none => none)) Q) →
    wp (.letIn b e body) Q
axiom wp.mono {e : Runtime.Expr} {P Q : Runtime.Val → Prop} :
    (∀ v, P v → Q v) → wp e P → wp e Q

axiom wp.ifThenElse {cond thn els : Runtime.Expr} {Q : Runtime.Val → Prop} :
    wp cond (fun vc =>
      (vc ≠ Runtime.Val.bool false → wp thn Q) ∧
      (vc = Runtime.Val.bool false → wp els Q)) →
    wp (.ifThenElse cond thn els) Q

axiom wp.fix {f : Runtime.Binder} {args : List (Runtime.Binder × Option TinyML.Type_)}
    {rt : Option TinyML.Type_} P e (Φ: List Runtime.Val → Prop):
  (
    (∀ vs, Φ vs → wp (.app (.val (.fix f args rt e)) (vs.map Runtime.Expr.val)) P) →
    ∀ vs, Φ vs → wp (e.subst ((Runtime.Subst.id.update' f (.fix f args rt e)).updateAll' (args.map Prod.fst) vs)) P
  ) → ∀ vs, Φ vs → wp (.app (.val (.fix f args rt e)) (vs.map Runtime.Expr.val)) P

axiom wp.app fn args P:
  wps args (fun vs => wp fn (fun fv => wp (.app (.val fv) (vs.map Runtime.Expr.val)) P)) →
  wp (.app fn args) P

axiom wp.func (P: Runtime.Val → Prop):
  P (.fix f args rt e) → wp (.fix f args rt e) P

axiom wp.fix' {f : Runtime.Binder} {args : List (Runtime.Binder × Option TinyML.Type_)}
    {rt : Option TinyML.Type_} e (Φ: (Runtime.Val → Prop) → List Runtime.Val → Prop) :
  (
    (∀ vs P, Φ P vs → wp (.app (.val (.fix f args rt e)) (vs.map Runtime.Expr.val)) P) →
    ∀ vs P, Φ P vs → wp (e.subst ((Runtime.Subst.id.update' f (.fix f args rt e)).updateAll' (args.map Prod.fst) vs)) P
  ) → ∀ vs P, Φ P vs → wp (.app (.val (.fix f args rt e)) (vs.map Runtime.Expr.val)) P


axiom wp.unop {op : TinyML.UnOp} {e : Runtime.Expr} {Q : Runtime.Val → Prop} :
    wp e (fun v => ∃ r, TinyML.evalUnOp op v = some r ∧ Q r) →
    wp (.unop op e) Q

/-- `assert e` evaluates `e`; if the result is not `false` it returns unit, otherwise traps. -/
axiom wp.assert {e : Runtime.Expr} {P : Runtime.Val → Prop} :
  wp e (fun v => v ≠ Runtime.Val.bool false → P .unit) → wp (.assert e) P

/-- A tuple expression evaluates each component (right-to-left) and wraps the results. -/
axiom wp.tuple {es : Runtime.Exprs} {Q : Runtime.Val → Prop} :
  wps es (fun vs => Q (.tuple vs)) → wp (.tuple es) Q

/-- An injection expression evaluates its payload and wraps it with the given tag and arity. -/
axiom wp.inj {tag arity : Nat} {payload : Runtime.Expr} {Q : Runtime.Val → Prop} :
  wp payload (fun v => Q (.inj tag arity v)) → wp (.inj tag arity payload) Q

/-- A match expression evaluates the scrutinee, then dispatches to the appropriate branch. -/
axiom wp.match_ {scrut : Runtime.Expr} {branches : Runtime.Exprs} {Q : Runtime.Val → Prop} :
  wp scrut (fun v =>
    ∃ (tag : Nat) (arity : Nat) (payload : Runtime.Val) (branch : Runtime.Expr),
      v = .inj tag arity payload ∧ branches[tag]? = some branch ∧
      wp (.app branch [.val payload]) Q) →
  wp (.match_ scrut branches) Q


@[simp] theorem wps_nil {Q : Runtime.Vals → Prop} : wps [] Q = Q [] := rfl
@[simp] theorem wps_cons {e : Runtime.Expr} {es : Runtime.Exprs} {Q : Runtime.Vals → Prop} :
    wps (e :: es) Q = wps es (fun vs => wp e (fun v => Q (v :: vs))) := rfl

theorem wps.mono {es : Runtime.Exprs} {P Q : Runtime.Vals → Prop}
    (h : ∀ vs, P vs → Q vs) : wps es P → wps es Q := by
  induction es generalizing P Q with
  | nil => exact h []
  | cons e es ih =>
    simp only [wps_cons]
    exact ih (fun vs hv => wp.mono (fun v hp => h (v :: vs) (hp)) hv)

/-- Program-level weakest precondition: every declaration evaluates safely,
    and each result is substituted into the remaining program. -/
def pwp : Runtime.Program → Prop
  | [] => True
  | ⟨b, e⟩ :: rest => wp e (fun v => pwp (Runtime.Program.subst rest (Runtime.Subst.update' b v .id)))
termination_by prog => prog.length
