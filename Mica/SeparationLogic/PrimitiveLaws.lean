-- SUMMARY: Spatially lifted weakest-precondition laws for TinyML primitive operations.
import Mica.SeparationLogic.Interpretations

open Iris Iris.BI

/-! # Primitive Laws with Spatial Contexts

Lifted versions of the wp axioms from `Axioms.lean`, stated in terms of
spatial contexts. Each rule has the form `ctx.interp ρ ⊢ wp wctx e Q` given
appropriate premises, where the context may change between premise and
conclusion for stateful operations. -/

namespace SpatialContext

variable {wctx : WpCtx}

private theorem wp_bind_tuple_aux {left : Runtime.Exprs} {es : Runtime.Exprs} {right : Runtime.Vals}
    {Q : Runtime.Val → iProp} :
    wps wctx es (fun vs => wp wctx (.tuple (left ++ vs.map Runtime.Expr.val ++ right.map Runtime.Expr.val)) Q) ⊢
    wp wctx (.tuple (left ++ es ++ right.map Runtime.Expr.val)) Q := by
  induction es generalizing left with
  | nil =>
      simp
  | cons e es ih =>
      simp only [wps_cons]
      have hmono :
          wps wctx es (fun vs =>
            wp wctx e (fun v =>
              wp wctx (.tuple (left ++ (v :: vs).map Runtime.Expr.val ++ right.map Runtime.Expr.val)) Q)) ⊢
          wps wctx es (fun vs =>
            wp wctx (.tuple ((left ++ [e]) ++ vs.map Runtime.Expr.val ++ right.map Runtime.Expr.val)) Q) := by
        apply wps.mono
        intro vs
        have hbind :
            wp wctx e (fun v =>
              wp wctx (.tuple (left ++ (v :: vs).map Runtime.Expr.val ++ right.map Runtime.Expr.val)) Q) ⊢
            wp wctx (.tuple ((left ++ [e]) ++ vs.map Runtime.Expr.val ++ right.map Runtime.Expr.val)) Q := by
          simpa [TinyML.K.fill, List.map_cons, List.append_assoc] using
            (wp.bind (k := TinyML.K.tupleK left .hole (vs ++ right)))
        exact hbind
      exact hmono.trans (by simpa [List.append_assoc] using ih (left := left ++ [e]))

/-- Value: context unchanged. -/
theorem wp_val {v : Runtime.Val} {Q : Runtime.Val → iProp}
    {R : iProp}
    (h : R ⊢ Q v) :
    R ⊢ wp wctx (.val v) Q :=
  h.trans wp.val

/-- Unary operation under evaluation: first evaluate the operand, then take the
    head unary-operation step. -/
theorem wp_bind_unop {op : TinyML.UnOp} {e : Runtime.Expr} {Q : Runtime.Val → iProp}
    {R : iProp}
    (h : R ⊢ wp wctx e (fun v => wp wctx (.unop op (.val v)) Q)) :
    R ⊢ wp wctx (.unop op e) Q :=
  h.trans (wp.bind (k := TinyML.K.unop op .hole))

/-- Unary operation at values: context unchanged. -/
theorem wp_unop {op : TinyML.UnOp} {v res : Runtime.Val} {Q : Runtime.Val → iProp}
    {R : iProp}
    (h : R ⊢ Q res) :
    TinyML.evalUnOp op v = some res →
    R ⊢ wp wctx (.unop op (.val v)) Q := by
  intro heval
  exact h.trans (wp.unop heval)

/-- Binary operation under evaluation: first evaluate the right operand, then the
    left operand, then take the head binary-operation step. -/
theorem wp_bind_binop {op : TinyML.BinOp} {l r : Runtime.Expr} {Q : Runtime.Val → iProp}
    {R : iProp}
    (h : R ⊢ wp wctx r (fun vr => wp wctx l (fun vl =>
      wp wctx (.binop op (.val vl) (.val vr)) Q))) :
    R ⊢ wp wctx (.binop op l r) Q := by
  have hr :
      wp wctx r (fun vr => wp wctx l (fun vl => wp wctx (.binop op (.val vl) (.val vr)) Q)) ⊢
      wp wctx r (fun vr => wp wctx (.binop op l (.val vr)) Q) := by
    apply wp.mono
    intro vr
    exact wp.bind (k := TinyML.K.binopL op .hole vr)
  exact h.trans (hr.trans (wp.bind (k := TinyML.K.binopR op l .hole)))

/-- Binary operation at values: context unchanged. -/
theorem wp_binop {op : TinyML.BinOp} {vl vr res : Runtime.Val} {Q : Runtime.Val → iProp}
    {R : iProp}
    (h : R ⊢ Q res) :
    TinyML.evalBinOp op vl vr = some res →
    R ⊢ wp wctx (.binop op (.val vl) (.val vr)) Q := by
  intro heval
  apply h.trans
  iapply (wp.binop heval)

/-- Conditional under evaluation: first evaluate the condition, then take the
    appropriate branch head step. -/
theorem wp_bind_if {cond thn els : Runtime.Expr} {Q : Runtime.Val → iProp}
    {R : iProp}
    (h : R ⊢ wp wctx cond (fun v => wp wctx (.ifThenElse (.val v) thn els) Q)) :
    R ⊢ wp wctx (.ifThenElse cond thn els) Q :=
  h.trans (wp.bind (k := TinyML.K.ifCond .hole thn els))

/-- Conditional on `true`: context unchanged. -/
theorem wp_if_true {thn els : Runtime.Expr} {Q : Runtime.Val → iProp}
    {R : iProp}
    (h : R ⊢ wp wctx thn Q) :
    R ⊢ wp wctx (.ifThenElse (.val (.bool true)) thn els) Q :=
  h.trans wp.if_true

/-- Conditional on `false`: context unchanged. -/
theorem wp_if_false {thn els : Runtime.Expr} {Q : Runtime.Val → iProp}
    {R : iProp}
    (h : R ⊢ wp wctx els Q) :
    R ⊢ wp wctx (.ifThenElse (.val (.bool false)) thn els) Q :=
  h.trans wp.if_false

/-- Reference allocation under evaluation: first evaluate the payload, then
    allocate. -/
theorem wp_bind_ref {e : Runtime.Expr} {Q : Runtime.Val → iProp}
    {R : iProp}
    (h : R ⊢ wp wctx e (fun v => wp wctx (.ref (.val v)) Q)) :
    R ⊢ wp wctx (.ref e) Q :=
  h.trans (wp.bind (k := TinyML.K.ref .hole))

/-- Reference allocation at values. The continuation receives fresh ownership in
    the updated environment for a caller-chosen fresh value constant. -/
theorem wp_ref (Θ : TinyML.TypeEnv) {v : Runtime.Val} {Q : Runtime.Val → iProp}
    {ctx : SpatialContext} {ρ : Env} {R : iProp} {Δ : Signature}
    {vt : Term .value} {ty : TinyML.Typ} {name : String} {newctx : SpatialContext}
    (hctx : wfIn ctx Δ)
    (hvt : vt.wfIn Δ)
    (hv : Term.eval ρ vt = v)
    (hfresh : name ∉ Δ.allNames)
    (hnewctx : insert (.pointsTo (.const (.uninterpreted name .value)) vt ty) ctx = newctx)
    (h : ∀ loc,
      newctx.interp Θ (ρ.updateConst .value name (.loc loc)) ∗ R ⊢
      Q (.loc loc)) :
    ctx.interp Θ ρ ∗ TinyML.ValHasType Θ v ty ∗ R  ⊢ wp wctx (.ref (.val v)) Q := by
  have hforall : ctx.interp Θ ρ ∗ TinyML.ValHasType Θ v ty ∗ R ⊢
      BIBase.forall fun (loc : Runtime.Location) => loc ↦ v -∗ Q (.loc loc) := by
    apply forall_intro
    intro loc
    apply wand_intro
    -- goal: (ctx.interp ρ ∗ ValHasType Θ v ty ∗ R) ∗ (loc ↦ v) ⊢ Q (.loc loc)
    let ρ' := ρ.updateConst .value name (.loc loc)
    let a : SpatialAtom := .pointsTo (.const (.uninterpreted name .value)) vt ty
    have hagree : Env.agreeOn Δ ρ ρ' := Env.agreeOn_update_fresh_const (c := ⟨name, .value⟩) hfresh
    have hctxeq : ctx.interp Θ ρ ⊢ ctx.interp Θ ρ' := by
      exact (SpatialContext.interp_env_agree Θ hctx hagree).1
    have hveq : Term.eval ρ' vt = v := by
      simpa [ρ'] using (Term.eval_update_fresh (t := vt) hvt hfresh).trans hv
    have hloc : Term.eval ρ' (.const (.uninterpreted name .value)) = .loc loc := by
      simp [ρ', Term.eval, Env.updateConst]
    have hptIntro : loc ↦ v ∗ TinyML.ValHasType Θ v ty ⊢ a.interp Θ ρ' := by
      rw [← hveq]
      exact (SpatialAtom.interp_pointsTo Θ (ρ := ρ')
        (lt := .const (.uninterpreted name .value)) (vt := vt) (ty := ty) (loc := loc) hloc).2
    have hinsert : ctx.interp Θ ρ ∗ (loc ↦ v ∗ TinyML.ValHasType Θ v ty) ⊢
        (insert a ctx).interp Θ ρ' := by
      apply (sep_mono_l hctxeq).trans
      apply sep_comm.1.trans
      apply (sep_mono_l hptIntro).trans
      simp [a, SpatialContext.interp]
    -- rearrange the heap and type resources into the new spatial atom.
    have hrearrange :
        (ctx.interp Θ ρ ∗ TinyML.ValHasType Θ v ty ∗ R) ∗ (loc ↦ v) ⊢
          (ctx.interp Θ ρ ∗ (loc ↦ v ∗ TinyML.ValHasType Θ v ty)) ∗ R := by
      istart
      iintro ⟨⟨Hctx, Hty, HR⟩, Hpt⟩
      isplitl [Hctx Hpt Hty]
      · isplitl [Hctx]
        · iexact Hctx
        · isplitl [Hpt]
          · iexact Hpt
          · iexact Hty
      · iexact HR
    exact hrearrange.trans ((sep_mono_l hinsert).trans (by simpa [ρ', a, hnewctx] using h loc))
  exact hforall.trans wp.ref

/-- Dereference under evaluation: first evaluate the scrutinee, then dereference
    the resulting value. -/
theorem wp_bind_deref {e : Runtime.Expr} {Q : Runtime.Val → iProp}
    {R : iProp}
    (h : R ⊢ wp wctx e (fun v => wp wctx (.deref (.val v)) Q)) :
    R ⊢ wp wctx (.deref e) Q :=
  h.trans (wp.bind (k := TinyML.K.deref .hole))

/-- Dereference at values: the context must contain a matching points-to.
    Reading preserves ownership.

    Given `remove ctx n = some (.pointsTo lt vt ty, rest)`, we extract the
    points-to from the context and use it at the head dereference step.
    The pure premises identify the runtime value `v` with the location named
    by `lt`, and the continuation premise `h` works with the remaining
    context. -/
theorem wp_deref (Θ : TinyML.TypeEnv) {Q : Runtime.Val → iProp}
    {ctx : SpatialContext} {ρ : Env} {R : iProp}
    {n : Nat} {lt vt : Term .value} {ty : TinyML.Typ} {rest : SpatialContext}
    {v : Runtime.Val} {loc : Runtime.Location}
    (h : ctx.interp Θ ρ ∗ R ⊢ Q (Term.eval ρ vt)) :
    remove ctx n = some (.pointsTo lt vt ty, rest) →
    Term.eval ρ lt = v →
    v = .loc loc →
    ctx.interp Θ ρ ∗ R ⊢ wp wctx (.deref (.val v)) Q := by
  intro hrem hlt hv
  subst hv
  -- Split the context and rewrite the selected atom to a raw points-to fact.
  have hsplit : ctx.interp Θ ρ ⊢
      (loc ↦ Term.eval ρ vt ∗ TinyML.ValHasType Θ (Term.eval ρ vt) ty) ∗
        rest.interp Θ ρ :=
    (interp_remove Θ ρ ctx n _ _ hrem).1 |>.trans (sep_mono_l (SpatialAtom.interp_pointsTo Θ hlt).1)
  -- Rebuild the original context inside the wand, since reading preserves it.
  apply (sep_mono_l hsplit).trans
  istart
  iintro ⟨⟨⟨Hpt, Hty⟩, Hrest⟩, HR⟩
  iapply wp.deref
  isplitl [Hpt]
  · iexact Hpt
  · iintro Hpt
    have hctx :
        (loc ↦ Term.eval ρ vt ∗ TinyML.ValHasType Θ (Term.eval ρ vt) ty) ∗
          rest.interp Θ ρ ⊢ ctx.interp Θ ρ :=
      (sep_mono_l (SpatialAtom.interp_pointsTo Θ hlt).2).trans (interp_remove Θ ρ ctx n _ _ hrem).2
    have hq :
        (loc ↦ Term.eval ρ vt ∗ TinyML.ValHasType Θ (Term.eval ρ vt) ty) ∗
          rest.interp Θ ρ ∗ R ⊢ Q (Term.eval ρ vt) :=
      sep_assoc.2.trans ((sep_mono_l hctx).trans h)
    iapply hq
    isplitl [Hpt Hty]
    · isplitl [Hpt]
      · iexact Hpt
      · iexact Hty
    · isplitr [HR]
      · iexact Hrest
      · iexact HR

/-- Store under evaluation: first evaluate the value expression, then the
    location expression, then take the head store step. -/
theorem wp_bind_store {loc val : Runtime.Expr} {Q : Runtime.Val → iProp}
    {R : iProp}
    (h : R ⊢ wp wctx val (fun vv => wp wctx loc (fun vl =>
      wp wctx (.store (.val vl) (.val vv)) Q))) :
    R ⊢ wp wctx (.store loc val) Q := by
  have hloc :
      wp wctx val (fun vv => wp wctx loc (fun vl => wp wctx (.store (.val vl) (.val vv)) Q)) ⊢
      wp wctx val (fun vv => wp wctx (.store loc (.val vv)) Q) := by
    apply wp.mono
    intro vv
    exact wp.bind (k := TinyML.K.storeL .hole vv)
  exact h.trans (hloc.trans (wp.bind (k := TinyML.K.storeR loc .hole)))

/-- Store at values: replace the selected points-to atom with the updated one. -/
theorem wp_store (Θ : TinyML.TypeEnv) {Q : Runtime.Val → iProp}
    {ctx : SpatialContext} {ρ : Env} {R : iProp}
    {n : Nat} {lt vt_old vt_new : Term .value} {ty : TinyML.Typ} {rest : SpatialContext}
    {vloc vnew : Runtime.Val} {loc : Runtime.Location}
    (h : (insert (.pointsTo lt vt_new ty) rest).interp Θ ρ ∗ R ⊢ Q .unit) :
    remove ctx n = some (.pointsTo lt vt_old ty, rest) →
    Term.eval ρ lt = vloc →
    vloc = .loc loc →
    Term.eval ρ vt_new = vnew →
    ctx.interp Θ ρ ∗ TinyML.ValHasType Θ vnew ty ∗ R ⊢
      wp wctx (.store (.val vloc) (.val vnew)) Q := by
  intro hrem hlt hvloc hvnew
  subst hvloc
  have hsplit : ctx.interp Θ ρ ⊢
      (loc ↦ Term.eval ρ vt_old ∗ TinyML.ValHasType Θ (Term.eval ρ vt_old) ty) ∗
        rest.interp Θ ρ :=
    (interp_remove Θ ρ ctx n _ _ hrem).1 |>.trans (sep_mono_l (SpatialAtom.interp_pointsTo Θ hlt).1)
  apply (sep_mono_l hsplit).trans
  istart
  iintro ⟨⟨⟨Hold, _HoldTy⟩, Hrest⟩, HnewTy, HR⟩
  iapply wp.store
  isplitl [Hold]
  · iexact Hold
  · iintro Hnew
    have hnew : loc ↦ vnew ∗ TinyML.ValHasType Θ vnew ty ⊢
        SpatialAtom.interp Θ ρ (.pointsTo lt vt_new ty) := by
      rw [← hvnew]
      exact (SpatialAtom.interp_pointsTo Θ hlt).2
    have hctx : (loc ↦ vnew ∗ TinyML.ValHasType Θ vnew ty) ∗ rest.interp Θ ρ ⊢
        (insert (.pointsTo lt vt_new ty) rest).interp Θ ρ := by
      simpa [insert, interp] using (sep_mono_l hnew)
    have hq : (loc ↦ vnew ∗ TinyML.ValHasType Θ vnew ty) ∗ rest.interp Θ ρ ∗ R ⊢ Q .unit :=
      sep_assoc.2.trans ((sep_mono_l hctx).trans h)
    iapply hq
    isplitl [Hnew HnewTy]
    · isplitl [Hnew]
      · iexact Hnew
      · iexact HnewTy
    · isplitr [HR]
      · iexact Hrest
      · iexact HR

/-- Assert under evaluation: first evaluate the tested expression, then take
    the head assert step. -/
theorem wp_bind_assert {e : Runtime.Expr} {Q : Runtime.Val → iProp}
    {R : iProp}
    (h : R ⊢ wp wctx e (fun v => wp wctx (.assert (.val v)) Q)) :
    R ⊢ wp wctx (.assert e) Q :=
  h.trans (wp.bind (k := TinyML.K.assert .hole))

/-- Assert on `true`: context unchanged. -/
theorem wp_assert {Q : Runtime.Val → iProp}
    {R : iProp}
    (h : R ⊢ Q .unit) :
    R ⊢ wp wctx (.assert (.val (.bool true))) Q :=
  h.trans wp.assert

/-- Injection under evaluation: first evaluate the payload, then take the head
    injection step. -/
theorem wp_bind_inj {tag arity : Nat} {payload : Runtime.Expr} {Q : Runtime.Val → iProp}
    {R : iProp}
    (h : R ⊢ wp wctx payload (fun v => wp wctx (.inj tag arity (.val v)) Q)) :
    R ⊢ wp wctx (.inj tag arity payload) Q :=
  h.trans (wp.bind (k := TinyML.K.injK tag arity .hole))

/-- Injection at values: context unchanged. -/
theorem wp_inj {tag arity : Nat} {payload : Runtime.Val} {Q : Runtime.Val → iProp}
    {R : iProp}
    (h : R ⊢ Q (.inj tag arity payload)) :
    R ⊢ wp wctx (.inj tag arity (.val payload)) Q :=
  h.trans wp.inj

/-- Tuple under evaluation: evaluate the components right-to-left, then take
    the head tuple step on the resulting values. -/
theorem wp_bind_tuple {es : Runtime.Exprs} {Q : Runtime.Val → iProp}
    {R : iProp}
    (h : R ⊢ wps wctx es (fun vs => wp wctx (.tuple (vs.map Runtime.Expr.val)) Q)) :
    R ⊢ wp wctx (.tuple es) Q := by
  apply h.trans
  simpa using (wp_bind_tuple_aux (left := []) (es := es) (right := []) (Q := Q))

/-- Tuple at values: context unchanged. -/
theorem wp_tuple {vs : Runtime.Vals} {Q : Runtime.Val → iProp}
    {R : iProp}
    (h : R ⊢ Q (.tuple vs)) :
    R ⊢ wp wctx (.tuple (vs.map Runtime.Expr.val)) Q :=
  h.trans wp.tuple

/-- Match under evaluation: first evaluate the scrutinee, then dispatch on the
    resulting injected value. -/
theorem wp_bind_match {scrut : Runtime.Expr} {branches : Runtime.Exprs} {Q : Runtime.Val → iProp}
    {R : iProp}
    (h : R ⊢ wp wctx scrut (fun v => wp wctx (.match_ (.val v) branches) Q)) :
    R ⊢ wp wctx (.match_ scrut branches) Q :=
  h.trans (wp.bind (k := TinyML.K.matchK branches .hole))

/-- Match on an injected value: context unchanged. -/
theorem wp_match {tag arity : Nat} {payload : Runtime.Val} {branches : Runtime.Exprs}
    {branch : Runtime.Expr} {Q : Runtime.Val → iProp}
    {R : iProp}
    (h : R ⊢ wp wctx (.app branch [.val payload]) Q) :
    branches[tag]? = some branch →
    R ⊢ wp wctx (.match_ (.val (.inj tag arity payload)) branches) Q := by
  intro hbranch
  exact h.trans (wp.match_ hbranch)

/-- Function values: context unchanged. -/
theorem wp_func {f : Runtime.Binder} {args : List Runtime.Binder} {e : Runtime.Expr}
    {Q : Runtime.Val → iProp} {R : iProp}
    (h : R ⊢ Q (.fix f args e)) :
    R ⊢ wp wctx (.fix f args e) Q :=
  h.trans (wp.func Q)

/-- Application under evaluation: first evaluate the arguments right-to-left,
    then the function, then take the head application step. -/
theorem wp_bind_app {fn : Runtime.Expr} {args : Runtime.Exprs} {Q : Runtime.Val → iProp}
    {R : iProp}
    (h : R ⊢ wps wctx args (fun vs => wp wctx fn (fun fv =>
      wp wctx (.app (.val fv) (vs.map Runtime.Expr.val)) Q))) :
    R ⊢ wp wctx (.app fn args) Q :=
  h.trans wp.app

/-- Fixpoint unfolding: spatially lifted version of `wp.fix`. -/
theorem wp_fix {f : Runtime.Binder} {args : List Runtime.Binder} {e : Runtime.Expr}
    {P : Runtime.Val → iProp} {Φ : List Runtime.Val → iProp}
    R
    (h : R ⊢
      (wp wctx (e.subst ((Runtime.Subst.id.updateBinder f (.fix f args e)).updateAllBinder args vs)) P)) :
    R ⊢
      (wp wctx (.app (.val (.fix f args e)) (vs.map Runtime.Expr.val)) P) :=
  h.trans (wp.fix (Φ := Φ))

/-- Fixpoint unfolding with a continuation-indexed invariant. -/
theorem wp_fix' {f : Runtime.Binder} {args : List Runtime.Binder} {e : Runtime.Expr}
    {Φ : (Runtime.Val → iProp) → List Runtime.Val → iProp}
    {R : iProp}
    (h : R ⊢
      □ (□ (∀ (vs : List Runtime.Val) (P : Runtime.Val → iProp),
          Φ P vs -∗ wp wctx (.app (.val (.fix f args e)) (vs.map Runtime.Expr.val)) P) -∗
        ∀ (vs : List Runtime.Val) (P : Runtime.Val → iProp),
          Φ P vs -∗ wp wctx (e.subst ((Runtime.Subst.id.updateBinder f (.fix f args e)).updateAllBinder args vs)) P)) :
    R ⊢ □ (∀ (vs : List Runtime.Val) (P : Runtime.Val → iProp),
          Φ P vs -∗ wp wctx (.app (.val (.fix f args e)) (vs.map Runtime.Expr.val)) P) :=
  h.trans (wp.fix' (Φ := Φ))

/-- Let-bindings: evaluate the bound expression, then continue in the body with
    the resulting value substituted. -/
theorem wp_letIn {b : Runtime.Binder} {bound body : Runtime.Expr} {Q : Runtime.Val → iProp}
    {R : iProp}
    (h : R ⊢ wp wctx bound (fun v => wp wctx (body.subst (Runtime.Subst.id.updateBinder b v)) Q)) :
    R ⊢ wp wctx (Runtime.Expr.letIn b bound body) Q :=
  h.trans wp.letIn

theorem wp_prim {n : String} {vs : List Runtime.Val} {Q : Runtime.Val → iProp}
    {R : iProp}
    (h : R ⊢ wctx n vs Q) :
    R ⊢ wp wctx (.app (.val (.prim n)) (vs.map Runtime.Expr.val)) Q :=
  h.trans wp.prim

theorem wp_app_lambda_single {b : Runtime.Binder} {body : Runtime.Expr} {v : Runtime.Val}
    {Φ : Runtime.Val → iProp} {R : iProp}
    (h : R ⊢ wp wctx (body.subst (Runtime.Subst.id.updateBinder b v)) Φ) :
    R ⊢ wp wctx (.app (.fix .none [b] body) [.val v]) Φ :=
  h.trans wp.app_lambda_single


/-- Strengthen the postcondition of a `wp` using a persistent resource:
    if `R` (persistent) entails `wp wctx e P`, and `R` together with `P v` entails `Q v`,
    then `R` entails `wp wctx e Q`. -/
theorem wp_strengthen_persistent
    {R : iProp} [Iris.BI.Persistent R] {e : Runtime.Expr}
    {P Q : Runtime.Val → iProp}
    (hwp : R ⊢ wp wctx e P) (hpost : ∀ v, R ⊢ P v -∗ Q v) :
    R ⊢ wp wctx e Q := by
  iintro □HR
  iapply wp.wand
  isplitr
  · iintro %v
    iapply (hpost v)
    iexact HR
  · iapply hwp; iexact HR

end SpatialContext
