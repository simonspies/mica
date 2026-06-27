-- SUMMARY: The Iris weakest precondition for TinyML and its derived proof rules, including invariant-based heap rules and primitive-call lifting.
import Mathlib.Data.List.Induction
import Iris.ProgramLogic.Lifting
import Iris.Instances.Lib.Invariants
import Mica.SeparationLogic.GhostState
import Mica.TinyML.RuntimeExpr
import Mica.TinyML.OpSem

open Iris Iris.BI Iris.OFE Iris.ProgramLogic Iris.ProgramLogic.EctxLanguage

/-!
This module defines Mica's weakest precondition as the Iris weakest
precondition of the TinyML language instance (`Mica.TinyML.Language`,
`Mica.SeparationLogic.GhostState`) and derives the proof rules used by the
verifier. Heap predicates come from iris-lean's generic heap (`l ↦ v` is
`Iris.pointsTo`); location invariants (`locinv`) are Iris invariants
(`Iris.inv`); primitive calls are lifted from the primitive operational
semantics (`wp.prim`, consumed at the registry level by
`Verifier.Registry.wp_prim`).
-/

-- Top-level elaboration for Iris connectives: the Iris library provides these
-- only inside `iprop(...)` blocks, and the candidates in scope at top level
-- do not elaborate at `iProp` (removing these rules yields "overloaded"
-- elaboration errors at every top-level `∗`/`⌜⌝` use).
macro_rules
  | `($P ∗ $Q)  => ``(BIBase.sep $P $Q)
  | `($P -∗ $Q) => ``(BIBase.wand $P $Q)
  | `(⌜$φ⌝)     => ``(BIBase.pure $φ)

-- The concrete signature from `GhostState`: invariants, later credits, and
-- heap resources over TinyML heaps.
abbrev iProp := IProp.{0} Sig

variable [MicaGS HasLC.hasLC Sig]

abbrev WpCtx := String → List Runtime.Val → (Runtime.Val → iProp) → iProp

/-- Weakest precondition for TinyML expressions: the Iris weakest
    precondition of the TinyML language instance at primitive context `ctx`,
    with stuckness `NotStuck` and the full mask. -/
def wp (ctx : TinyML.PrimCtx) (e : Runtime.Expr) (Φ : Runtime.Val → iProp) : iProp :=
  Wp.wp Stuckness.NotStuck ⊤ (show TinyML.LExpr ctx from e) Φ

/-- The namespace housing the location invariants (`locinv`). A single fixed
    namespace suffices: every rule below opens at most one invariant around
    one atomic step. -/
def micaN : Namespace := nroot.@"mica_locinv"

/-- Location invariant: an Iris invariant owning the location and constraining
    its contents by `I`. The rules below never give out the points-to itself;
    where the payload `I` is handed out (`wp.deref_inv`), it must be
    persistent. -/
def locinv (l : Runtime.Location) (I : Runtime.Val → iProp) : iProp :=
  inv micaN iprop(∃ v, l ↦ [v] ∗ I v)

instance locinv_persistent (l : Runtime.Location) (I : Runtime.Val → iProp) :
    Persistent (locinv l I) :=
  inv_persistent micaN _

instance locinv_contractive (l : Runtime.Location) :
    Contractive (fun I : Runtime.Val → iProp => locinv l I) where
  distLater_dist H :=
    Contractive.distLater_dist (f := inv micaN)
      (fun m hm => exists_ne fun v => sep_ne.ne .rfl (H m hm v))

/-- Weakest precondition for a list of expressions, evaluated right-to-left.
    `wps ctx [e1, e2, e3] Q` first evaluates `e3`, then `e2`, then `e1`,
    and passes `[v1, v2, v3]` (in original order) to `Q`. -/
def wps (ctx : TinyML.PrimCtx) : Runtime.Exprs → (Runtime.Vals → iProp) → iProp
  | [], Q => Q []
  | e :: es, Q => wps ctx es (fun vs => wp ctx e (fun v => Q (v :: vs)))

/-! ## Core rules -/

theorem pointsTo.exclusive (l : Runtime.Location) (b1 b2 : TinyML.Block) :
    l ↦ b1 ∗ l ↦ b2 ⊢ (False : iProp) := by
  istart
  iintro ⟨H1, H2⟩
  icases pointsTo_ne $$ H1 H2 with %Hne
  exact absurd rfl Hne

theorem wp.val {ctx : TinyML.PrimCtx} {v : Runtime.Val} {Q : Runtime.Val → iProp} :
    Q v ⊢ wp ctx (.val v) Q :=
  wp_value' (Val := Runtime.Val)

theorem wp.bind {ctx : TinyML.PrimCtx} {k : TinyML.K} {e : Runtime.Expr} {Q : Runtime.Val → iProp} :
    wp ctx e (fun v => wp ctx (k.fill (.val v)) Q) ⊢ wp ctx (k.fill e) Q :=
  wp_bind (fun e : TinyML.LExpr ctx => k.fill e)

theorem wp.wand {ctx : TinyML.PrimCtx} {e : Runtime.Expr} {P Q : Runtime.Val → iProp} :
    (∀ v, P v -∗ Q v) ∗ wp ctx e P ⊢ wp ctx e Q :=
  sep_symm.trans (wand_elim (wp_wand (Val := Runtime.Val)))

-- Derived monotonicity as an entailment
theorem wp.mono {ctx : TinyML.PrimCtx} {e : Runtime.Expr} {P Q : Runtime.Val → iProp}
    (h : ∀ v, P v ⊢ Q v) : wp ctx e P ⊢ wp ctx e Q :=
  emp_sep.2.trans (sep_mono_left (forall_intro fun v => wand_intro (emp_sep.1.trans (h v))))
    |>.trans (wp.wand (ctx := ctx) (e := e))

/-- Lift a deterministic, heap-preserving head step to a `wp` rule that strips
    a later. The `EctxLifting` wrappers are not public in iris-lean, so this
    routes through the public `wp_lift_pure_det_step_no_fork` and the public
    baseStep/primStep conversion lemmas of `EctxLanguage`. -/
private theorem wp.pure_step' {ctx : TinyML.PrimCtx} {e₁ e₂ : Runtime.Expr}
    (hstep : ∀ μ, TinyML.Head ctx e₁ μ e₂ μ)
    (hdet : ∀ μ e' μ', TinyML.Head ctx e₁ μ e' μ' → e' = e₂ ∧ μ' = μ)
    {Q : Runtime.Val → iProp} :
    ▷ wp ctx e₂ Q ⊢ wp ctx e₁ Q := by
  have hred : ∀ μ : TinyML.Heap,
      BaseStep.Reducible (show TinyML.LExpr ctx from e₁, μ) :=
    fun μ => ⟨[], e₂, μ, [], hstep μ, rfl, rfl⟩
  have hsafe : ∀ μ : TinyML.Heap,
      PrimStep.Reducible (show TinyML.LExpr ctx from e₁, μ) :=
    fun μ => primStep_reducible_of_baseStep_reducible (hred μ)
  refine ((later_mono (wand_intro sep_elim_left)).trans
      (step_fupd_intro Std.LawfulSet.subset_refl)).trans
    (wp_lift_pure_det_step_no_fork (e₂ := show TinyML.LExpr ctx from e₂) ⊤ hsafe ?_)
  rintro μ obs e' μ' eₜ hps
  obtain ⟨h, rfl, rfl⟩ := baseStep_of_primStep_of_baseStep_reducible (hred μ) hps
  obtain ⟨he, hμ⟩ := hdet _ _ _ h
  exact ⟨rfl, hμ, he, rfl⟩

/-- Later-free version of `wp.pure_step'`. -/
private theorem wp.pure_step {ctx : TinyML.PrimCtx} {e₁ e₂ : Runtime.Expr}
    (hstep : ∀ μ, TinyML.Head ctx e₁ μ e₂ μ)
    (hdet : ∀ μ e' μ', TinyML.Head ctx e₁ μ e' μ' → e' = e₂ ∧ μ' = μ)
    {Q : Runtime.Val → iProp} :
    wp ctx e₂ Q ⊢ wp ctx e₁ Q :=
  later_intro.trans (wp.pure_step' hstep hdet)

theorem wp.func {ctx : TinyML.PrimCtx} {f : Runtime.Binder} {args : List Runtime.Binder}
    {e : Runtime.Expr} (P : Runtime.Val → iProp) :
    P (.fix f args e) ⊢ wp ctx (.fix f args e) P :=
  wp.val.trans (wp.pure_step (fun _ => .fixIntro)
    (by rintro μ e' μ' h; cases h; exact ⟨rfl, rfl⟩))

theorem wp.fix {ctx : TinyML.PrimCtx} {vs : List Runtime.Val} {f : Runtime.Binder}
    {args : List Runtime.Binder} {e : Runtime.Expr} {P : Runtime.Val → iProp}
    (hlen : args.length = vs.length) :
      wp ctx (e.subst ((Runtime.Subst.id.updateBinder f (.fix f args e)).updateAllBinder args vs)) P
    ⊢ wp ctx (.app (.val (.fix f args e)) (vs.map Runtime.Expr.val)) P :=
  wp.pure_step (fun _ => .beta hlen) (fun _ _ _ h => h.beta_inv)

theorem wp.unop {ctx : TinyML.PrimCtx} {op : TinyML.UnOp} {v res : Runtime.Val}
    {Q : Runtime.Val → iProp} (heval : TinyML.evalUnOp op v = some res) :
    Q res ⊢ wp ctx (.unop op (.val v)) Q :=
  wp.val.trans (wp.pure_step (fun _ => .unop heval)
    (by rintro μ e' μ' h; cases h; simp_all))

theorem wp.binop {ctx : TinyML.PrimCtx} {op : TinyML.BinOp} {vl vr res : Runtime.Val}
    {Q : Runtime.Val → iProp} (heval : TinyML.evalBinOp op vl vr = some res) :
    Q res ⊢ wp ctx (.binop op (.val vl) (.val vr)) Q :=
  wp.val.trans (wp.pure_step (fun _ => .binop heval)
    (by rintro μ e' μ' h; cases h; simp_all))

theorem wp.if_true {ctx : TinyML.PrimCtx} {thn els : Runtime.Expr} {Q : Runtime.Val → iProp} :
    wp ctx thn Q ⊢ wp ctx (.ifThenElse (.val (.bool true)) thn els) Q :=
  wp.pure_step (fun _ => .ifTrue) (by rintro μ e' μ' h; cases h; exact ⟨rfl, rfl⟩)

theorem wp.if_false {ctx : TinyML.PrimCtx} {thn els : Runtime.Expr} {Q : Runtime.Val → iProp} :
    wp ctx els Q ⊢ wp ctx (.ifThenElse (.val (.bool false)) thn els) Q :=
  wp.pure_step (fun _ => .ifFalse) (by rintro μ e' μ' h; cases h; exact ⟨rfl, rfl⟩)

/-- `assert true` returns unit; `assert false` is stuck. -/
theorem wp.assert {ctx : TinyML.PrimCtx} {P : Runtime.Val → iProp} :
    P .unit ⊢ wp ctx (.assert (.val (.bool true))) P :=
  wp.val.trans (wp.pure_step (fun _ => .assertOk)
    (by rintro μ e' μ' h; cases h; exact ⟨rfl, rfl⟩))

/-- A tuple expression evaluates each component (right-to-left) and wraps the results. -/
theorem wp.tuple {ctx : TinyML.PrimCtx} {vs : Runtime.Vals} {Q : Runtime.Val → iProp} :
    Q (.tuple vs) ⊢ wp ctx (.tuple (vs.map Runtime.Expr.val)) Q :=
  wp.val.trans (wp.pure_step (fun _ => .tuple) (fun _ _ _ h => h.tuple_inv))

/-- An injection expression evaluates its payload and wraps it with the given tag and arity. -/
theorem wp.inj {ctx : TinyML.PrimCtx} {tag arity : Nat} {payload : Runtime.Val}
    {Q : Runtime.Val → iProp} :
    Q (.inj tag arity payload) ⊢ wp ctx (.inj tag arity (.val payload)) Q :=
  wp.val.trans (wp.pure_step (fun _ => .injVal)
    (by rintro μ e' μ' h; cases h; exact ⟨rfl, rfl⟩))

/-- A match expression evaluates the scrutinee, then dispatches to the appropriate branch. -/
theorem wp.match_ {ctx : TinyML.PrimCtx} {tag arity : Nat} {payload : Runtime.Val}
    {branches : Runtime.Exprs} {branch : Runtime.Expr} {Q : Runtime.Val → iProp}
    (hbranch : branches[tag]? = some branch) (harity : arity = branches.length) :
    wp ctx (.app branch [.val payload]) Q ⊢
    wp ctx (.match_ (.val (.inj tag arity payload)) branches) Q := by
  have hlt : tag < branches.length := List.getElem?_eq_some_iff.mp hbranch |>.1
  have hget : branches[tag] = branch := by
    simpa [List.getElem?_eq_getElem hlt] using hbranch
  subst hget
  exact wp.pure_step (fun _ => .match_ hlt harity)
    (by
      rintro μ e' μ' h
      cases h
      exact ⟨rfl, rfl⟩)

/-! ## Heap operations -/

/-- `ref e` allocates a fresh location whose block has `e`'s value in field `0`. -/
theorem wp.ref {ctx : TinyML.PrimCtx} {v : Runtime.Val} {Q : Runtime.Val → iProp} :
    iprop(∀ (l : Runtime.Location), l ↦ [v] -∗ Q (.loc l)) ⊢
    wp ctx (.ref (.val v)) Q := by
  istart
  iintro HΦ
  simp only [_root_.wp]
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  obtain ⟨l, hl⟩ := Iris.Std.List.fresh σ₁.keys
  have hfresh : TinyML.Heap.Fresh l σ₁ := fun hmem => hl (Std.ExtTreeMap.mem_keys.mpr hmem)
  have hred : BaseStep.Reducible (show TinyML.LExpr ctx from .ref (.val v), σ₁) :=
    ⟨[], .val (.loc l), σ₁.update l [v], [], .ref hfresh, rfl, rfl⟩
  isplitr
  · ipureintro
    exact primStep_reducible_of_baseStep_reducible hred
  iintro !> %e₂ %σ₂ %eₜ %Hps Hcr
  obtain ⟨hh, rfl, rfl⟩ := baseStep_of_primStep_of_baseStep_reducible hred Hps
  cases hh
  rename_i l' hfresh'
  imod genHeap_alloc' (σ₁.lookup_fresh l' hfresh') $$ Hσ with ⟨Hσ, Hpt, _Hmt⟩
  imodintro
  simp only [stateInterp, Algebra.BigOpL.bigOpL_nil]
  iframe Hσ
  isplit <;> try itrivial
  iexists (Runtime.Val.loc l')
  isplit
  · ipureintro; rfl
  · iapply HΦ $$ %l' Hpt

/-- `deref e` reads field `0` of the block at the location. Reading preserves ownership. -/
theorem wp.deref {ctx : TinyML.PrimCtx} {l : Runtime.Location} {v : Runtime.Val}
    {Q : Runtime.Val → iProp} :
    l ↦ [v] ∗ (l ↦ [v] -∗ Q v) ⊢ wp ctx (.deref (.val (.loc l))) Q := by
  istart
  iintro ⟨Hpt, HΦ⟩
  simp only [_root_.wp]
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  ihave %Hlook : (⌜Iris.Std.get? σ₁ l = some [v]⌝ : iProp) $$ [Hσ Hpt]
  · ihave >%h := genHeap_valid $$ [$Hσ $Hpt]
    itrivial
  have hlk : TinyML.Heap.lookup l σ₁ = some [v] := Hlook
  have hlkf : TinyML.Heap.lookupField l 0 σ₁ = some v := by
    simp [TinyML.Heap.lookupField_of_lookup hlk]
  have hred : BaseStep.Reducible (show TinyML.LExpr ctx from .deref (.val (.loc l)), σ₁) :=
    ⟨[], .val v, σ₁, [], .deref hlkf, rfl, rfl⟩
  isplitr
  · ipureintro
    exact primStep_reducible_of_baseStep_reducible hred
  iintro !> %e₂ %σ₂ %eₜ %Hps Hcr
  obtain ⟨hh, rfl, rfl⟩ := baseStep_of_primStep_of_baseStep_reducible hred Hps
  cases hh
  rename_i v' hlk'
  obtain rfl : v = v' := Option.some.inj (hlkf.symm.trans hlk')
  imodintro
  simp only [List.length_nil, Nat.add_zero, Algebra.BigOpL.bigOpL_nil]
  iframe Hσ
  isplit <;> try itrivial
  iexists v
  isplit
  · ipureintro; rfl
  · iapply HΦ $$ Hpt

/-- `store loc val` updates field `0` of the block at the location. -/
theorem wp.store {ctx : TinyML.PrimCtx} {l : Runtime.Location} {old v : Runtime.Val}
    {Q : Runtime.Val → iProp} :
    l ↦ [old] ∗ (l ↦ [v] -∗ Q .unit) ⊢ wp ctx (.store (.val (.loc l)) (.val v)) Q := by
  istart
  iintro ⟨Hpt, HΦ⟩
  simp only [_root_.wp]
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  ihave %Hlook : (⌜Iris.Std.get? σ₁ l = some [old]⌝ : iProp) $$ [Hσ Hpt]
  · ihave >%h := genHeap_valid $$ [$Hσ $Hpt]
    itrivial
  have hlk : TinyML.Heap.lookup l σ₁ = some [old] := Hlook
  have hlkf : TinyML.Heap.lookupField l 0 σ₁ = some old := by
    simp [TinyML.Heap.lookupField_of_lookup hlk]
  have hpost : TinyML.Heap.updateField l 0 v σ₁ = σ₁.update l [v] :=
    TinyML.Heap.updateField_of_lookup hlk
  have hred : BaseStep.Reducible (show TinyML.LExpr ctx from .store (.val (.loc l)) (.val v), σ₁) :=
    ⟨[], .val .unit, TinyML.Heap.updateField l 0 v σ₁, [], .store hlkf, rfl, rfl⟩
  isplitr
  · ipureintro
    exact primStep_reducible_of_baseStep_reducible hred
  iintro !> %e₂ %σ₂ %eₜ %Hps Hcr
  obtain ⟨hh, rfl, rfl⟩ := baseStep_of_primStep_of_baseStep_reducible hred Hps
  cases hh
  rename_i w hlk'
  rw [hpost]
  imod genHeap_update' (b₂ := [v]) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  simp only [stateInterp, Algebra.BigOpL.bigOpL_nil]
  iframe Hσ
  isplit <;> try itrivial
  iexists Runtime.Val.unit
  isplit
  · ipureintro; rfl
  · iapply HΦ $$ Hpt

/-! ## Invariant-based heap rules -/

/-- `ref e` under a location invariant: allocate the location, then mint
    `locinv l I` from the fresh points-to and the persistent payload. -/
theorem wp.ref_inv {ctx : TinyML.PrimCtx} {v : Runtime.Val}
    {I : Runtime.Val → iProp} {Q : Runtime.Val → iProp} :
    iprop((□ I v) ∗ ∀ (l : Runtime.Location), locinv l I -∗ Q (.loc l)) ⊢
    wp ctx (.ref (.val v)) Q := by
  simp only [locinv]
  refine .trans ?_ ((wp.ref (Q := fun w => iprop(|={⊤}=> Q w))).trans
    (wp_fupd Stuckness.NotStuck ⊤ (show TinyML.LExpr ctx from .ref (.val v)) Q))
  istart
  iintro ⟨#HI, HΦ⟩ %l Hpt
  imod inv_alloc micaN ⊤ iprop(∃ w, l ↦ [w] ∗ I w) $$ [Hpt] with Hinv
  · inext
    iexists v
    isplitl [Hpt]
    · iexact Hpt
    · iexact HI
  imodintro
  iapply HΦ $$ %l Hinv

/-- `deref e` under a location invariant: open the invariant around the read.
    The payload is handed to the continuation *and* restored into the
    invariant, so `I` must be persistent. -/
theorem wp.deref_inv {ctx : TinyML.PrimCtx} {l : Runtime.Location}
    {I : Runtime.Val → iProp} [∀ v, Persistent (I v)] {Q : Runtime.Val → iProp} :
    locinv l I ∗ (∀ v, I v -∗ Q v) ⊢ wp ctx (.deref (.val (.loc l))) Q := by
  simp only [locinv]
  istart
  iintro ⟨#Hinv, HΦ⟩
  simp only [_root_.wp]
  iapply wp_lift_step_fupd rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  imod inv_acc _ _ _ CoPset.subseteq_top $$ Hinv with ⟨HP, Hcl⟩
  icases HP with ⟨%w, Hpt, HI⟩
  imod Hpt with Hpt
  ihave %Hlook : (⌜Iris.Std.get? σ₁ l = some [w]⌝ : iProp) $$ [Hσ Hpt]
  · ihave >%h := genHeap_valid $$ [$Hσ $Hpt]
    itrivial
  have hlk : TinyML.Heap.lookup l σ₁ = some [w] := Hlook
  have hlkf : TinyML.Heap.lookupField l 0 σ₁ = some w := by
    simp [TinyML.Heap.lookupField_of_lookup hlk]
  have hred : BaseStep.Reducible (show TinyML.LExpr ctx from .deref (.val (.loc l)), σ₁) :=
    ⟨[], .val w, σ₁, [], .deref hlkf, rfl, rfl⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact primStep_reducible_of_baseStep_reducible hred
  iintro %e₂ %σ₂ %eₜ %Hps -
  obtain ⟨hh, rfl, rfl⟩ := baseStep_of_primStep_of_baseStep_reducible hred Hps
  cases hh
  rename_i w' hlk'
  obtain rfl : w = w' := Option.some.inj (hlkf.symm.trans hlk')
  imodintro
  inext
  iintuitionistic HI
  imod Hclose with -
  imod Hcl $$ [Hpt] with -
  · inext
    iexists w
    isplitl [Hpt]
    · iexact Hpt
    · iexact HI
  imodintro
  simp only [stateInterp, Algebra.BigOpL.bigOpL_nil]
  iframe Hσ
  isplitl [HΦ]
  · iapply wp_value ⟨rfl⟩
    iapply HΦ $$ HI
  · itrivial

/-- `store loc val` under a location invariant: open the invariant around the
    write and restore it with the new (persistent) payload. -/
theorem wp.store_inv {ctx : TinyML.PrimCtx} {l : Runtime.Location}
    {v : Runtime.Val} {I : Runtime.Val → iProp} {Q : Runtime.Val → iProp} :
    locinv l I ∗ (□ I v) ∗ Q .unit ⊢ wp ctx (.store (.val (.loc l)) (.val v)) Q := by
  simp only [locinv]
  istart
  iintro ⟨#Hinv, #HIv, HΦ⟩
  simp only [_root_.wp]
  iapply wp_lift_step_fupd rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  imod inv_acc _ _ _ CoPset.subseteq_top $$ Hinv with ⟨HP, Hcl⟩
  icases HP with ⟨%w, Hpt, HI⟩
  imod Hpt with Hpt
  iclear HI
  ihave %Hlook : (⌜Iris.Std.get? σ₁ l = some [w]⌝ : iProp) $$ [Hσ Hpt]
  · ihave >%h := genHeap_valid $$ [$Hσ $Hpt]
    itrivial
  have hlk : TinyML.Heap.lookup l σ₁ = some [w] := Hlook
  have hlkf : TinyML.Heap.lookupField l 0 σ₁ = some w := by
    simp [TinyML.Heap.lookupField_of_lookup hlk]
  have hpost : TinyML.Heap.updateField l 0 v σ₁ = σ₁.update l [v] :=
    TinyML.Heap.updateField_of_lookup hlk
  have hred : BaseStep.Reducible
      (show TinyML.LExpr ctx from .store (.val (.loc l)) (.val v), σ₁) :=
    ⟨[], .val .unit, TinyML.Heap.updateField l 0 v σ₁, [], .store hlkf, rfl, rfl⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact primStep_reducible_of_baseStep_reducible hred
  iintro %e₂ %σ₂ %eₜ %Hps -
  obtain ⟨hh, rfl, rfl⟩ := baseStep_of_primStep_of_baseStep_reducible hred Hps
  cases hh
  rw [hpost]
  imodintro
  inext
  imod genHeap_update' (b₂ := [v]) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imod Hclose with -
  imod Hcl $$ [Hpt] with -
  · inext
    iexists v
    isplitl [Hpt]
    · iexact Hpt
    · iexact HIv
  imodintro
  simp only [stateInterp, Algebra.BigOpL.bigOpL_nil]
  iframe Hσ
  isplitl [HΦ]
  · iapply wp_value ⟨rfl⟩
    iexact HΦ
  · itrivial

/-! ## Primitive calls -/

/-- Generic lifting rule for primitive calls — the relationship between the
    primitive operational semantics and the weakest precondition. A primitive
    call takes one atomic step by `Head.primStep`; the premise asks, for the
    current heap, that the call is reducible under `ctx` and that every result
    the context relates re-establishes the heap interpretation and the
    postcondition. -/
theorem wp.prim {ctx : TinyML.PrimCtx} {n : String} {vs : List Runtime.Val}
    {Q : Runtime.Val → iProp} :
    iprop(∀ μ, heapInterp μ ={⊤}=∗
        ⌜∃ v μ', ctx n vs μ v μ'⌝ ∗
        ▷ ∀ v μ', ⌜ctx n vs μ v μ'⌝ ={⊤}=∗ heapInterp μ' ∗ Q v) ⊢
      wp ctx (.app (.val (.prim n)) (vs.map Runtime.Expr.val)) Q := by
  istart
  iintro H
  simp only [_root_.wp]
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  imod H $$ %σ₁ Hσ with ⟨%hex, H⟩
  obtain ⟨v, μ', hstep⟩ := hex
  have hred : BaseStep.Reducible
      (show TinyML.LExpr ctx from .app (.val (.prim n)) (vs.map Runtime.Expr.val), σ₁) :=
    ⟨[], .val v, μ', [], .primStep hstep, rfl, rfl⟩
  imodintro
  isplitr
  · ipureintro
    exact primStep_reducible_of_baseStep_reducible hred
  iintro !> %e₂ %σ₂ %eₜ %Hps Hcr
  obtain ⟨hh, rfl, rfl⟩ := baseStep_of_primStep_of_baseStep_reducible hred Hps
  obtain ⟨w, hw, rfl⟩ := TinyML.Head.prim_inv hh
  imod H $$ %w %σ₂ %hw with ⟨Hσ, HQ⟩
  imodintro
  simp only [stateInterp, Algebra.BigOpL.bigOpL_nil]
  iframe Hσ
  isplit <;> try itrivial
  iexists w
  isplit
  · ipureintro; rfl
  · iexact HQ

/-- Primitive-call rule for pure contexts: at `n`/`vs`, `ctx` is
    heap-independent and heap-preserving, with at least one result. Covers
    every current stdlib intrinsic (`Verifier.Reduce.pure`). -/
theorem wp.prim_pure {ctx : TinyML.PrimCtx} {n : String} {vs : List Runtime.Val}
    {rel : Runtime.Val → Prop} {Q : Runtime.Val → iProp}
    (hctx : ∀ μ v μ', ctx n vs μ v μ' ↔ rel v ∧ μ' = μ) (hne : ∃ v, rel v) :
    iprop(∀ v, ⌜rel v⌝ -∗ Q v) ⊢
      wp ctx (.app (.val (.prim n)) (vs.map Runtime.Expr.val)) Q := by
  refine .trans ?_ wp.prim
  istart
  iintro H %μ Hσ
  imodintro
  isplitr
  · ipureintro
    obtain ⟨v, hv⟩ := hne
    exact ⟨v, μ, (hctx μ v μ).mpr ⟨hv, rfl⟩⟩
  iintro !> %v %μ' %hstep
  obtain ⟨hv, rfl⟩ := (hctx μ v μ').mp hstep
  imodintro
  iframe Hσ
  iapply H $$ %v %hv

/-! ## Recursion -/

theorem wp.fix' {ctx : TinyML.PrimCtx} {f : Runtime.Binder} {args : List Runtime.Binder}
    {e : Runtime.Expr} {Φ : (Runtime.Val → iProp) → List Runtime.Val → iProp}
    (hlen : ∀ (vs : List Runtime.Val) (P : Runtime.Val → iProp),
      Φ P vs ⊢ (⌜args.length = vs.length⌝ : iProp)) :
    □ (□ (∀ (vs : List Runtime.Val) (P : Runtime.Val → iProp),
        Φ P vs -∗ wp ctx (.app (.val (.fix f args e)) (vs.map Runtime.Expr.val)) P) -∗
      ∀ (vs : List Runtime.Val) (P : Runtime.Val → iProp),
        Φ P vs -∗ wp ctx (e.subst ((Runtime.Subst.id.updateBinder f (.fix f args e)).updateAllBinder args vs)) P)
    ⊢ □ (∀ (vs : List Runtime.Val) (P : Runtime.Val → iProp), Φ P vs -∗ wp ctx (.app (.val (.fix f args e)) (vs.map Runtime.Expr.val)) P) := by
  istart
  iintro #H
  iapply loeb_wand_intuitionistically
  imodintro
  iintro #HG
  imodintro
  iintro %vs %P HΦ
  ihave %hl : (⌜args.length = vs.length⌝ : iProp) $$ [HΦ]
  · iapply hlen vs P
    iexact HΦ
  iapply wp.pure_step' (fun _ => .beta hl) (fun _ _ _ h => h.beta_inv)
  inext
  ispecialize H $$ HG
  iapply H $$ %vs %P HΦ

/-- Definitional unfolding of `wp` into the Iris weakest precondition; stated
    here so it remains usable once `wp` is marked irreducible (adequacy needs
    it). -/
theorem wp_def {ctx : TinyML.PrimCtx} {e : Runtime.Expr} {Φ : Runtime.Val → iProp} :
    wp ctx e Φ = Wp.wp Stuckness.NotStuck ⊤ (show TinyML.LExpr ctx from e) Φ := rfl

/- All rules below treat `wp` as opaque; keep unification from unfolding the
   Iris fixpoint. -/
attribute [irreducible] _root_.wp

/-! ## Application -/

@[simp] theorem wps_nil {ctx : TinyML.PrimCtx} {Q : Runtime.Vals → iProp} :
    wps ctx [] Q = Q [] := rfl
@[simp] theorem wps_cons {ctx : TinyML.PrimCtx} {e : Runtime.Expr} {es : Runtime.Exprs}
    {Q : Runtime.Vals → iProp} :
    wps ctx (e :: es) Q = wps ctx es (fun vs => wp ctx e (fun v => Q (v :: vs))) := rfl

theorem wps_snoc {ctx : TinyML.PrimCtx} {es : Runtime.Exprs} {e : Runtime.Expr}
    {Q : Runtime.Vals → iProp} :
    wps ctx (es ++ [e]) Q = wp ctx e (fun v => wps ctx es (fun vs => Q (vs ++ [v]))) := by
  induction es generalizing Q with
  | nil => rfl
  | cons a es ih => simp [wps_cons, ih]

/-- Evaluate the focused argument of an application (frame `appArgs`). -/
private theorem wp.bind_appArgs {ctx : TinyML.PrimCtx} {fn e : Runtime.Expr}
    {left : Runtime.Exprs} {right : Runtime.Vals} {Q : Runtime.Val → iProp} :
    wp ctx e (fun v => wp ctx (.app fn (left ++ [.val v] ++ right.map .val)) Q) ⊢
    wp ctx (.app fn (left ++ [e] ++ right.map .val)) Q :=
  wp.bind (k := .appArgs fn left .hole right)

/-- Evaluate the function position once all arguments are values (frame `appFn`). -/
private theorem wp.bind_appFn {ctx : TinyML.PrimCtx} {fn : Runtime.Expr} {vs : Runtime.Vals}
    {Q : Runtime.Val → iProp} :
    wp ctx fn (fun fv => wp ctx (.app (.val fv) (vs.map .val)) Q) ⊢
    wp ctx (.app fn (vs.map .val)) Q :=
  wp.bind (k := .appFn .hole vs)

theorem wp.app {ctx : TinyML.PrimCtx} {fn : Runtime.Expr} {args : Runtime.Exprs}
    {P : Runtime.Val → iProp} :
    wps ctx args (fun vs => wp ctx fn (fun fv =>
      wp ctx (.app (.val fv) (vs.map Runtime.Expr.val)) P)) ⊢
    wp ctx (.app fn args) P := by
  suffices h : ∀ (es : Runtime.Exprs) (right : Runtime.Vals),
      wps ctx es (fun vs => wp ctx fn (fun fv =>
        wp ctx (.app (.val fv) ((vs ++ right).map Runtime.Expr.val)) P)) ⊢
      wp ctx (.app fn (es ++ right.map Runtime.Expr.val)) P by
    simpa using h args []
  intro es
  induction es using List.reverseRecOn with
  | nil =>
    intro right
    simpa using wp.bind_appFn (vs := right)
  | append_singleton es e ih =>
    intro right
    rw [wps_snoc]
    have eq1 : ∀ v : Runtime.Val,
        wps ctx es (fun vs => wp ctx fn (fun fv =>
          wp ctx (.app (.val fv) ((vs ++ [v] ++ right).map Runtime.Expr.val)) P)) =
        wps ctx es (fun vs => wp ctx fn (fun fv =>
          wp ctx (.app (.val fv) ((vs ++ v :: right).map Runtime.Expr.val)) P)) := by
      intro v; simp [List.append_assoc]
    have eq2 : ∀ v : Runtime.Val,
        wp ctx (.app fn (es ++ (v :: right).map Runtime.Expr.val)) P =
        wp ctx (.app fn (es ++ [.val v] ++ right.map Runtime.Expr.val)) P := by
      intro v; simp [List.append_assoc]
    refine BIBase.Entails.trans
      (wp.mono (Q := fun v => wp ctx (.app fn (es ++ [.val v] ++ right.map .val)) P) ?_)
      wp.bind_appArgs
    intro v
    exact (BIBase.Entails.of_eq (eq1 v)).trans ((ih (v :: right)).trans
      (BIBase.Entails.of_eq (eq2 v)))

/-! ## Derived lemmas -/

theorem wps.mono {ctx : TinyML.PrimCtx} {es : Runtime.Exprs} {P Q : Runtime.Vals → iProp}
    (h : ∀ vs, P vs ⊢ Q vs) : wps ctx es P ⊢ wps ctx es Q := by
  induction es generalizing P Q with
  | nil => exact h []
  | cons e es ih =>
    simp only [wps_cons]
    exact ih (fun vs => wp.mono (fun v => h (v :: vs)))

/-- Derived wp rule for let-bindings (desugared to immediately-applied fix). -/
theorem wp.letIn {ctx : TinyML.PrimCtx} {b : Runtime.Binder} {bound body : Runtime.Expr}
    {Q : Runtime.Val → iProp} :
    wp ctx bound (fun v => wp ctx (body.subst (Runtime.Subst.id.updateBinder b v)) Q) ⊢
    wp ctx (Runtime.Expr.letIn b bound body) Q := by
  simp only [Runtime.Expr.letIn]
  istart
  iintro Hbound
  iapply wp.app
  simp only [wps_cons, wps_nil]
  iapply (wp.wand (P := fun v => wp ctx (body.subst (Runtime.Subst.id.updateBinder b v)) Q))
  isplitl []
  · iintro %v Hv
    iapply wp.func
    iapply (wp.fix (vs := [v]) rfl)
    simp only [Runtime.Subst.updateBinder, Runtime.Subst.updateAllBinder_cons,
               Runtime.Subst.updateAllBinder_nil_left]
    iassumption
  · iassumption

/-- Program-level weakest precondition: the program, desugared to its nested
    `let`-bindings (`Runtime.Program.expr`), runs safely to completion. -/
def pwp (ctx : TinyML.PrimCtx) (prog : Runtime.Program) : iProp :=
  wp ctx prog.expr (fun _ => emp)

/-- The empty program imposes no obligation. -/
theorem pwp_nil {ctx : TinyML.PrimCtx} : (emp : iProp) ⊢ pwp ctx [] := by
  simp only [pwp, Runtime.Program.expr]
  exact wp.val (v := .unit) (Q := fun _ => emp)

/-- A leading declaration: prove its body via `wp`, then the rest under the
    extended substitution. -/
theorem pwp_cons {ctx : TinyML.PrimCtx} {b : Runtime.Binder} {e : Runtime.Expr}
    {rest : Runtime.Program} :
    wp ctx e (fun v => pwp ctx (Runtime.Program.subst rest (Runtime.Subst.updateBinder b v .id))) ⊢
      pwp ctx ({ name := b, body := e } :: rest) := by
  simp only [pwp, Runtime.Program.expr]
  refine .trans (wp.mono fun v => ?_) wp.letIn
  rw [Runtime.Program.expr_subst]
  exact .rfl

/-- Applying a single-argument lambda `(fun b -> body)` to a value reduces to substituting. -/
theorem wp.app_lambda_single {ctx : TinyML.PrimCtx} {b : Runtime.Binder} {body : Runtime.Expr}
    {v : Runtime.Val} {Φ : Runtime.Val → iProp} :
    wp ctx (body.subst (Runtime.Subst.id.updateBinder b v)) Φ ⊢
    wp ctx (.app (.fix .none [b] body) [.val v]) Φ := by
  istart
  iintro Hwp
  iapply wp.app
  simp only [wps_cons, wps_nil]
  iapply wp.val
  iapply wp.func
  iapply (wp.fix (vs := [v]) rfl)
  simp only [Runtime.Subst.updateBinder, Runtime.Subst.updateAllBinder_cons,
             Runtime.Subst.updateAllBinder_nil_left]
  iassumption
