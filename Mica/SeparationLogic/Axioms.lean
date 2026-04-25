-- SUMMARY: Axiomatized Iris connectives and weakest-precondition rules for TinyML programs and heap operations.
import Iris.Examples.IProp
import Mica.TinyML.RuntimeExpr
import Mica.TinyML.OpSem

open Iris Iris.BI Iris.OFE

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

axiom locinv : Runtime.Location → (Runtime.Val → iProp) → iProp
/- We don't have invariants yet, but the idea is the encoding of locinv is
        locinv l I := inv N (∃ v, l ↦ v * I v)
We don't give out access to the points-to direcly in the rules below and,
instead, the invariant on the value I has to be persistent. -/
axiom locinv_persistent l I : Persistent (locinv l I)

attribute [instance] locinv_persistent

/- In Iris, invariants are contractive in their body. `locinv` is currently
axiomatized in Mica, so this experiment records the corresponding local axiom. -/
axiom locinv_contractive (l : Runtime.Location) :
  Contractive (fun I : Runtime.Val → iProp => locinv l I)

attribute [instance] locinv_contractive

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

axiom wp.bind {k : TinyML.K} {e : Runtime.Expr} {Q : Runtime.Val → iProp} :
    wp e (fun v => wp (k.fill (.val v)) Q) ⊢ wp (k.fill e) Q

axiom wp.mono {e : Runtime.Expr} {P Q : Runtime.Val → iProp} :
    (∀ v, P v -∗ Q v) ∗ wp e P ⊢ wp e Q

axiom wp.app {fn : Runtime.Expr} {args : Runtime.Exprs} {P : Runtime.Val → iProp} :
    wps args (fun vs => wp fn (fun fv =>
      wp (.app (.val fv) (vs.map Runtime.Expr.val)) P)) ⊢
    wp (.app fn args) P

axiom wp.func {f : Runtime.Binder} {args : List Runtime.Binder} {e : Runtime.Expr}
    (P : Runtime.Val → iProp) :
    P (.fix f args e) ⊢ wp (.fix f args e) P

axiom wp.fix {vs : List Runtime.Val} {f : Runtime.Binder} {args : List Runtime.Binder} {e : Runtime.Expr}
    {P : Runtime.Val → iProp} {Φ : List Runtime.Val → iProp} :
      wp (e.subst ((Runtime.Subst.id.updateBinder f (.fix f args e)).updateAllBinder args vs)) P
    ⊢ wp (.app (.val (.fix f args e)) (vs.map Runtime.Expr.val)) P

axiom wp.fix' {f : Runtime.Binder} {args : List Runtime.Binder} {e : Runtime.Expr}
    {Φ : (Runtime.Val → iProp) → List Runtime.Val → iProp} :
    □ (□ (∀ (vs : List Runtime.Val) (P : Runtime.Val → iProp),
        Φ P vs -∗ wp (.app (.val (.fix f args e)) (vs.map Runtime.Expr.val)) P) -∗
      ∀ (vs : List Runtime.Val) (P : Runtime.Val → iProp),
        Φ P vs -∗ wp (e.subst ((Runtime.Subst.id.updateBinder f (.fix f args e)).updateAllBinder args vs)) P)
    ⊢ □ (∀ (vs : List Runtime.Val) (P : Runtime.Val → iProp), Φ P vs -∗ wp (.app (.val (.fix f args e)) (vs.map Runtime.Expr.val)) P)

axiom wp.unop {op : TinyML.UnOp} {v res : Runtime.Val} {Q : Runtime.Val → iProp} :
    TinyML.evalUnOp op v = some res →
    Q res ⊢ wp (.unop op (.val v)) Q

axiom wp.binop {op : TinyML.BinOp} {vl vr res : Runtime.Val} {Q : Runtime.Val → iProp} :
    TinyML.evalBinOp op vl vr = some res →
    Q res ⊢ wp (.binop op (.val vl) (.val vr)) Q

axiom wp.if_true {thn els : Runtime.Expr} {Q : Runtime.Val → iProp} :
    wp thn Q ⊢ wp (.ifThenElse (.val (.bool true)) thn els) Q

axiom wp.if_false {thn els : Runtime.Expr} {Q : Runtime.Val → iProp} :
    wp els Q ⊢ wp (.ifThenElse (.val (.bool false)) thn els) Q

/-- `assert true` returns unit; `assert false` is stuck. -/
axiom wp.assert {P : Runtime.Val → iProp} :
    P .unit ⊢ wp (.assert (.val (.bool true))) P

/-- A tuple expression evaluates each component (right-to-left) and wraps the results. -/
axiom wp.tuple {vs : Runtime.Vals} {Q : Runtime.Val → iProp} :
    Q (.tuple vs) ⊢ wp (.tuple (vs.map Runtime.Expr.val)) Q

/-- An injection expression evaluates its payload and wraps it with the given tag and arity. -/
axiom wp.inj {tag arity : Nat} {payload : Runtime.Val} {Q : Runtime.Val → iProp} :
    Q (.inj tag arity payload) ⊢ wp (.inj tag arity (.val payload)) Q

/-- A match expression evaluates the scrutinee, then dispatches to the appropriate branch. -/
axiom wp.match_ {tag arity : Nat} {payload : Runtime.Val} {branches : Runtime.Exprs}
    {branch : Runtime.Expr} {Q : Runtime.Val → iProp} :
    branches[tag]? = some branch →
    wp (.app branch [.val payload]) Q ⊢
    wp (.match_ (.val (.inj tag arity payload)) branches) Q

/-! ## Heap operations -/

/-- `ref e` allocates a fresh location, stores the value, and returns the location. -/
axiom wp.ref {v : Runtime.Val} {Q : Runtime.Val → iProp} :
    iprop(∀ (l : Runtime.Location), l ↦ v -∗ Q (.loc l)) ⊢
    wp (.ref (.val v)) Q

/-- `deref e` reads the value stored at the location. Reading preserves ownership. -/
axiom wp.deref {l : Runtime.Location} {v : Runtime.Val} {Q : Runtime.Val → iProp} :
    l ↦ v ∗ (l ↦ v -∗ Q v) ⊢ wp (.deref (.val (.loc l))) Q

/-- `store loc val` updates the value at the location. -/
axiom wp.store {l : Runtime.Location} {old v : Runtime.Val} {Q : Runtime.Val → iProp} :
    l ↦ old ∗ (l ↦ v -∗ Q .unit) ⊢ wp (.store (.val (.loc l)) (.val v)) Q


/-- `ref e` allocates a fresh location, stores the value, and returns the location. -/
axiom wp.ref_inv {v : Runtime.Val} {I: Runtime.Val → iProp} {Q : Runtime.Val → iProp} :
    iprop((□ I v) ∗ ∀ (l : Runtime.Location), locinv l I -∗ Q (.loc l)) ⊢
    wp (.ref (.val v)) Q

/-- `deref e` reads the value stored at the location. Reading preserves ownership. -/
axiom wp.deref_inv {l : Runtime.Location} {I: Runtime.Val → iProp} {Q : Runtime.Val → iProp} :
    locinv l I ∗ (∀ v, I v -∗ Q v) ⊢ wp (.deref (.val (.loc l))) Q

/-- `store loc val` updates the value at the location. -/
axiom wp.store_inv {l : Runtime.Location} {v: Runtime.Val} {Q : Runtime.Val → iProp} :
    locinv l I ∗ (□ I v) ∗ Q .unit ⊢ wp (.store (.val (.loc l)) (.val v)) Q


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
    wp e (fun v => pwp (Runtime.Program.subst rest (Runtime.Subst.updateBinder b v .id)))
termination_by prog => prog.length
decreasing_by
  simp [Runtime.Program.subst_length]

@[simp] theorem pwp_nil : pwp [] = (emp : iProp) := by
  simp [pwp]

@[simp] theorem pwp_cons {b : Runtime.Binder} {e : Runtime.Expr} {rest : Runtime.Program} :
    pwp ({ name := b, body := e } :: rest) =
      wp e (fun v => pwp (Runtime.Program.subst rest (Runtime.Subst.updateBinder b v .id))) := by
  simp [pwp]

/-- Derived wp rule for let-bindings (desugared to immediately-applied fix). -/
theorem wp.letIn {b : Runtime.Binder} {bound body : Runtime.Expr} {Q : Runtime.Val → iProp} :
    wp bound (fun v => wp (body.subst (Runtime.Subst.id.updateBinder b v)) Q) ⊢
    wp (Runtime.Expr.letIn b bound body) Q := by
  simp only [Runtime.Expr.letIn]
  istart
  iintro Hbound
  iapply wp.app
  simp only [wps_cons, wps_nil]
  iapply (wp.mono (P := fun v => wp (body.subst (Runtime.Subst.id.updateBinder b v)) Q))
  isplitl []
  · iintro %v Hv
    iapply wp.func
    iapply (wp.fix (Φ := fun _ => emp) (vs := [v]))
    simp only [Runtime.Subst.updateBinder, Runtime.Subst.updateAllBinder_cons,
               Runtime.Subst.updateAllBinder_nil_left]
    iexact Hv
  · iexact Hbound

/-- Applying a single-argument lambda `(fun b -> body)` to a value reduces to substituting. -/
theorem wp.app_lambda_single {b : Runtime.Binder} {body : Runtime.Expr} {v : Runtime.Val}
    {Φ : Runtime.Val → iProp} :
    wp (body.subst (Runtime.Subst.id.updateBinder b v)) Φ ⊢
    wp (.app (.fix .none [b] body) [.val v]) Φ := by
  istart
  iintro Hwp
  iapply wp.app
  simp only [wps_cons, wps_nil]
  iapply wp.val
  iapply wp.func
  iapply (wp.fix (Φ := fun _ => emp) (vs := [v]))
  simp only [Runtime.Subst.updateBinder, Runtime.Subst.updateAllBinder_cons,
             Runtime.Subst.updateAllBinder_nil_left]
  iexact Hwp
