import Iris.Examples.IProp
import Mica.TinyML.RuntimeExpr
import Mica.TinyML.OpSem

open Iris Iris.BI

-- Top-level elaboration for Iris connectives (the Iris library only provides
-- these inside `iprop(...)` blocks).
macro_rules
  | `($P ∗ $Q)  => ``(BIBase.sep $P $Q)
  | `($P -∗ $Q) => ``(BIBase.wand $P $Q)
  | `(⌜$φ⌝)     => ``(BIBase.pure $φ)

-- Signature axiomatized for now; eventually we will say there is a heap
-- resource algebra that is part of it.
axiom Sig : BundledGFunctors
abbrev iProp := IProp Sig

-- Points-to axiomatized for now.
axiom pointsTo : Runtime.Location → Runtime.Val → iProp
notation:50 l " ↦ " v:51 => pointsTo l v

axiom wp : Runtime.Expr → (Runtime.Val → iProp) → iProp

/-- Weakest precondition for a list of expressions, evaluated right-to-left.
    `wps [e1, e2, e3] Q` first evaluates `e3`, then `e2`, then `e1`,
    and passes `[v1, v2, v3]` (in original order) to `Q`. -/
noncomputable def wps : Runtime.Exprs → (Runtime.Vals → iProp) → iProp
  | [], Q => Q []
  | e :: es, Q => wps es (fun vs => wp e (fun v => Q (v :: vs)))

/-! ## Core axioms -/

axiom pointsTo.exclusive (l : Runtime.Location) (v1 v2 : Runtime.Val) :
    l ↦ v1 ∗ l ↦ v2 ⊢ (False : iProp)

axiom wp.val {v : Runtime.Val} {Q : Runtime.Val → iProp} :
    Q v ⊢ wp (.val v) Q

axiom wp.binop {op : TinyML.BinOp} {l r : Runtime.Expr} {Q : Runtime.Val → iProp} :
    wp l (fun vl => wp r (fun vr =>
      ∃ (res : Runtime.Val), ⌜TinyML.evalBinOp op vl vr = some res⌝ ∗ Q res)) ⊢
    wp (.binop op l r) Q

axiom wp.mono {e : Runtime.Expr} {P Q : Runtime.Val → iProp} :
    (∀ v, P v -∗ Q v) ∗ wp e P ⊢ wp e Q

axiom wp.ifThenElse {cond thn els : Runtime.Expr} {Q : Runtime.Val → iProp} :
    wp cond (fun vc =>
      BIBase.and
        (⌜vc ≠ Runtime.Val.bool false⌝ -∗ wp thn Q)
        (⌜vc = Runtime.Val.bool false⌝ -∗ wp els Q)) ⊢
    wp (.ifThenElse cond thn els) Q

axiom wp.fix {f : Runtime.Binder} {args : List Runtime.Binder} {e : Runtime.Expr}
    {P : Runtime.Val → iProp} {Φ : List Runtime.Val → iProp} :
    ((∀ vs, Φ vs -∗ wp (.app (.val (.fix f args e)) (vs.map Runtime.Expr.val)) P) -∗
      ∀ vs, Φ vs -∗ wp (e.subst ((Runtime.Subst.id.update' f (.fix f args e)).updateAll' args vs)) P)
    ⊢ (∀ (vs : List Runtime.Val), Φ vs -∗ wp (.app (.val (.fix f args e)) (vs.map Runtime.Expr.val)) P)

axiom wp.app {fn : Runtime.Expr} {args : Runtime.Exprs} {P : Runtime.Val → iProp} :
    wps args (fun vs => wp fn (fun fv =>
      wp (.app (.val fv) (vs.map Runtime.Expr.val)) P)) ⊢
    wp (.app fn args) P

axiom wp.func {f : Runtime.Binder} {args : List Runtime.Binder} {e : Runtime.Expr}
    (P : Runtime.Val → iProp) :
    P (.fix f args e) ⊢ wp (.fix f args e) P

axiom wp.fix' {f : Runtime.Binder} {args : List Runtime.Binder} {e : Runtime.Expr}
    {Φ : (Runtime.Val → iProp) → List Runtime.Val → iProp} :
    ((∀ (vs : List Runtime.Val) (P : Runtime.Val → iProp),
        Φ P vs -∗ wp (.app (.val (.fix f args e)) (vs.map Runtime.Expr.val)) P) -∗
      ∀ (vs : List Runtime.Val) (P : Runtime.Val → iProp),
        Φ P vs -∗ wp (e.subst ((Runtime.Subst.id.update' f (.fix f args e)).updateAll' args vs)) P)
    ⊢ (∀ (vs : List Runtime.Val) (P : Runtime.Val → iProp),
        Φ P vs -∗ wp (.app (.val (.fix f args e)) (vs.map Runtime.Expr.val)) P)

axiom wp.unop {op : TinyML.UnOp} {e : Runtime.Expr} {Q : Runtime.Val → iProp} :
    wp e (fun v =>
      ∃ (res : Runtime.Val), ⌜TinyML.evalUnOp op v = some res⌝ ∗ Q res) ⊢
    wp (.unop op e) Q

/-- `assert e` evaluates `e`; if the result is not `false` it returns unit, otherwise traps. -/
axiom wp.assert {e : Runtime.Expr} {P : Runtime.Val → iProp} :
    wp e (fun v => ⌜v ≠ Runtime.Val.bool false⌝ -∗ P .unit) ⊢
    wp (.assert e) P

/-- A tuple expression evaluates each component (right-to-left) and wraps the results. -/
axiom wp.tuple {es : Runtime.Exprs} {Q : Runtime.Val → iProp} :
    wps es (fun vs => Q (.tuple vs)) ⊢ wp (.tuple es) Q

/-- An injection expression evaluates its payload and wraps it with the given tag and arity. -/
axiom wp.inj {tag arity : Nat} {payload : Runtime.Expr} {Q : Runtime.Val → iProp} :
    wp payload (fun v => Q (.inj tag arity v)) ⊢ wp (.inj tag arity payload) Q

/-- A match expression evaluates the scrutinee, then dispatches to the appropriate branch. -/
axiom wp.match_ {scrut : Runtime.Expr} {branches : Runtime.Exprs} {Q : Runtime.Val → iProp} :
    wp scrut (fun v =>
      ∃ (tag : Nat) (arity : Nat) (payload : Runtime.Val) (branch : Runtime.Expr),
        ⌜v = .inj tag arity payload⌝ ∗ ⌜branches[tag]? = some branch⌝ ∗
        wp (.app branch [.val payload]) Q) ⊢
    wp (.match_ scrut branches) Q

/-! ## Heap operations -/

/-- `ref e` allocates a fresh location, stores the value, and returns the location. -/
axiom wp.ref {e : Runtime.Expr} {Q : Runtime.Val → iProp} :
    wp e (fun v => BIBase.forall fun (l : Runtime.Location) => l ↦ v -∗ Q (.loc l)) ⊢
    wp (.ref e) Q

/-- `deref e` reads the value stored at the location. Reading preserves ownership. -/
axiom wp.deref {e : Runtime.Expr} {Q : Runtime.Val → iProp} :
    wp e (fun vloc =>
      ∃ (l : Runtime.Location) (v : Runtime.Val),
        ⌜vloc = .loc l⌝ ∗ l ↦ v ∗ (l ↦ v -∗ Q v)) ⊢
    wp (.deref e) Q

/-- `store loc val` updates the value at the location. -/
axiom wp.store {loc val : Runtime.Expr} {Q : Runtime.Val → iProp} :
    wp loc (fun vloc => wp val (fun vval =>
      ∃ (l : Runtime.Location) (old : Runtime.Val),
        ⌜vloc = .loc l⌝ ∗ l ↦ old ∗ (l ↦ vval -∗ Q .unit))) ⊢
    wp (.store loc val) Q

/-! ## Derived lemmas -/

@[simp] theorem wps_nil {Q : Runtime.Vals → iProp} : wps [] Q = Q [] := rfl
@[simp] theorem wps_cons {e : Runtime.Expr} {es : Runtime.Exprs} {Q : Runtime.Vals → iProp} :
    wps (e :: es) Q = wps es (fun vs => wp e (fun v => Q (v :: vs))) := rfl

-- Derived monotonicity as an entailment
theorem wp.mono' {e : Runtime.Expr} {P Q : Runtime.Val → iProp}
    (h : ∀ v, P v ⊢ Q v) : wp e P ⊢ wp e Q :=
  emp_sep.2.trans (sep_mono_l (forall_intro fun v => wand_intro (emp_sep.1.trans (h v)))) |>.trans wp.mono

theorem wps.mono {es : Runtime.Exprs} {P Q : Runtime.Vals → iProp}
    (h : ∀ vs, P vs ⊢ Q vs) : wps es P ⊢ wps es Q := by
  induction es generalizing P Q with
  | nil => exact h []
  | cons e es ih =>
    simp only [wps_cons]
    exact ih (fun vs => wp.mono' (fun v => h (v :: vs)))

/-- Program-level weakest precondition: every declaration evaluates safely,
    and each result is substituted into the remaining program. -/
noncomputable def pwp : Runtime.Program → iProp
  | [] => emp
  | ⟨b, e⟩ :: rest =>
    wp e (fun v => pwp (Runtime.Program.subst rest (Runtime.Subst.update' b v .id)))
termination_by prog => prog.length
decreasing_by
  simp [Runtime.Program.subst_length]

/-- Derived wp rule for let-bindings (desugared to immediately-applied fix). -/
theorem wp.letIn {b : Runtime.Binder} {bound body : Runtime.Expr} {Q : Runtime.Val → iProp} :
    wp bound (fun v => wp (body.subst (Runtime.Subst.id.update' b v)) Q) ⊢
    wp (Runtime.Expr.letIn b bound body) Q := by
  simp only [Runtime.Expr.letIn]
  istart
  iintro Hbound
  iapply wp.app
  simp only [wps_cons, wps_nil]
  iapply (wp.mono (P := fun v => wp (body.subst (Runtime.Subst.id.update' b v)) Q))
  isplitl []
  · iintro %v Hv
    iapply wp.func
    iapply (@wp.fix .none [b] body Q
      (fun vs => ∃ v', ⌜vs = [v']⌝ ∗ wp (body.subst (Runtime.Subst.id.update' b v')) Q))
    · iintro _IH %vs ⟨%v', %Heq, Hwp⟩
      subst Heq
      simp only [Runtime.Subst.updateAll'_cons, Runtime.Subst.updateAll'_nil_left,
                  Runtime.Subst.update']
      iexact Hwp
    · iexists v
      isplitr
      · ipure_intro; rfl
      · iexact Hv
  · iexact Hbound
