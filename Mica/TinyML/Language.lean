-- SUMMARY: Iris language instance for the TinyML runtime IR, via evaluation-context items.
import Iris.ProgramLogic.EctxiLanguage
import Mica.TinyML.OpSem

namespace TinyML

open Iris.ProgramLogic

/-!
This module instantiates the Iris program-logic interface with TinyML:
expressions step by `Head` reduction (OpSem) inside evaluation contexts.
Iris locates the operational semantics by typeclass search on the expression
type, and TinyML's reduction is parameterized by a `PrimCtx`, so the instance
is keyed on the type synonym `LExpr ctx` carrying the context as a phantom
parameter.

The instance goes through `EctxItemLanguage`: contexts are lists of flat
frames (`KItem`, innermost first), and Iris derives composition, the
decomposition lemmas, and the `Language` instance. The compound contexts `K`
of OpSem convert to frame lists via `K.items`, which transports Iris's
`Language.Context` instances to `K.fill`.
-/

/-- `Runtime.Expr` tagged with the primitive context that fixes the
    operational behavior of `Val.prim` calls. A plain `def` (not an `abbrev`)
    so instance search keys on `ctx`. -/
def LExpr (_ : PrimCtx) := Runtime.Expr

/-- Conversion from expressions to values, underlying `ToVal`. -/
def exprVal : Runtime.Expr → Option Runtime.Val
  | .val v => some v
  | _ => none

@[simp] theorem exprVal_val (v : Runtime.Val) : exprVal (.val v) = some v := rfl

theorem exprVal_eq_some {e : Runtime.Expr} {v : Runtime.Val} (h : exprVal e = some v) :
    e = .val v := by
  cases e <;> simp_all [exprVal]

/-- A single evaluation-context frame: a constructor of `K` (OpSem) with the
    recursive position removed. Iris derives full contexts as `List KItem`,
    innermost frame first. -/
inductive KItem where
  | unop   (op : TinyML.UnOp)
  | binopR (op : TinyML.BinOp) (lhs : Runtime.Expr)
  | binopL (op : TinyML.BinOp) (v : Runtime.Val)
  | appArgs (fn : Runtime.Expr) (left : Runtime.Exprs) (right : Runtime.Vals)
  | appFn   (vs : Runtime.Vals)
  | ifCond (thn els : Runtime.Expr)
  | letProdK (names : List Runtime.Binder) (body : Runtime.Expr)
  | ref
  | deref
  | storeR (loc : Runtime.Expr)
  | storeL (v : Runtime.Val)
  | arrayMakeInit (len : Runtime.Expr)
  | arrayMakeLen (init : Runtime.Val)
  | arrayLen
  | arrayGetIdx (arr : Runtime.Expr)
  | arrayGetArr (idx : Runtime.Val)
  | arraySetVal (arr idx : Runtime.Expr)
  | arraySetIdx (arr : Runtime.Expr) (val : Runtime.Val)
  | arraySetArr (idx val : Runtime.Val)
  | assert
  | tupleK (left : Runtime.Exprs) (right : Runtime.Vals)
  | injK (tag : Nat) (arity : Nat)
  | matchK (branches : Runtime.Exprs)

/-- Place an expression in the hole of a single frame. -/
def KItem.fill : KItem → Runtime.Expr → Runtime.Expr
  | .unop op,             e => .unop op e
  | .binopR op lhs,       e => .binop op lhs e
  | .binopL op v,         e => .binop op e (.val v)
  | .appArgs fn left right, e => .app fn (left ++ [e] ++ right.map .val)
  | .appFn vs,            e => .app e (vs.map .val)
  | .ifCond thn els,      e => .ifThenElse e thn els
  | .letProdK names body, e => .letProd names e body
  | .ref,                 e => .ref e
  | .deref,               e => .deref e
  | .storeR loc,          e => .store loc e
  | .storeL v,            e => .store e (.val v)
  | .arrayMakeInit len,   e => .arrayMake len e
  | .arrayMakeLen init,   e => .arrayMake e (.val init)
  | .arrayLen,            e => .arrayLen e
  | .arrayGetIdx arr,     e => .arrayGet arr e
  | .arrayGetArr idx,     e => .arrayGet e (.val idx)
  | .arraySetVal arr idx, e => .arraySet arr idx e
  | .arraySetIdx arr val, e => .arraySet arr e (.val val)
  | .arraySetArr idx val, e => .arraySet e (.val idx) (.val val)
  | .assert,              e => .assert e
  | .tupleK left right,   e => .tuple (left ++ [e] ++ right.map .val)
  | .injK tag arity,      e => .inj tag arity e
  | .matchK branches,     e => .match_ e branches

/-- Unique decomposition of an expression list around a non-value focus with
    values to its right: the two splits agree. -/
theorem split_eq_of_focus {l₁ l₂ r₁ r₂ : Runtime.Exprs} {e₁ e₂ : Runtime.Expr}
    (h : l₁ ++ e₁ :: r₁ = l₂ ++ e₂ :: r₂)
    (he₁ : exprVal e₁ = none) (he₂ : exprVal e₂ = none)
    (hr₁ : ∀ x ∈ r₁, ∃ v, x = Runtime.Expr.val v)
    (hr₂ : ∀ x ∈ r₂, ∃ v, x = Runtime.Expr.val v) :
    l₁ = l₂ ∧ e₁ = e₂ ∧ r₁ = r₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => simp_all
    | cons a l₂ =>
      exfalso
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨v, rfl⟩ := hr₁ e₂ (by simp)
      simp [exprVal] at he₂
  | cons a l₁ ih =>
    cases l₂ with
    | nil =>
      exfalso
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨v, rfl⟩ := hr₂ e₁ (by simp)
      simp [exprVal] at he₁
    | cons b l₂ =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, rfl, rfl⟩ := ih h
      simp

/-- Members of a value-mapped list are values. -/
theorem mem_map_val {es : Runtime.Exprs} {vs : Runtime.Vals} {e : Runtime.Expr}
    (heq : es = vs.map Runtime.Expr.val) (hmem : e ∈ es) : ∃ v, e = Runtime.Expr.val v := by
  subst heq
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hmem
  exact ⟨v, rfl⟩

/-! ### Instance obligations

Stated as standalone lemmas over `Runtime.Expr` so that `simp` works
at the right transparency. -/

theorem KItem.fill_inj (Ki : KItem) : Function.Injective Ki.fill := by
  cases Ki <;> intro e₁ e₂ h <;> simp_all [KItem.fill]

theorem KItem.fill_val {Ki : KItem} {e : Runtime.Expr}
    (h : (exprVal (Ki.fill e)).isSome) : (exprVal e).isSome := by
  cases Ki <;> simp [KItem.fill, exprVal] at h

theorem Runtime.Expr.val_injective : Function.Injective Runtime.Expr.val := by
  intro a b h
  cases h
  rfl

theorem KItem.fill_no_val_inj {e₁ e₂ : Runtime.Expr} (Ki₁ Ki₂ : KItem)
    (h₁ : exprVal e₁ = none) (h₂ : exprVal e₂ = none)
    (heq : Ki₁.fill e₁ = Ki₂.fill e₂) : Ki₁ = Ki₂ := by
  have hv₁ : ∀ v : Runtime.Val, e₁ ≠ .val v := by
    rintro v rfl; simp [exprVal] at h₁
  have hv₂ : ∀ v : Runtime.Val, e₂ ≠ .val v := by
    rintro v rfl; simp [exprVal] at h₂
  cases Ki₁ <;> cases Ki₂ <;>
    first
    | (simp_all [KItem.fill, exprVal]; done)
    | skip
  case binopL.binopR =>
    simp only [KItem.fill, Runtime.Expr.binop.injEq] at heq
    exact absurd heq.2.2.symm (hv₂ _)
  case storeL.storeR =>
    simp only [KItem.fill, Runtime.Expr.store.injEq] at heq
    exact absurd heq.2.symm (hv₂ _)
  case arrayMakeLen.arrayMakeInit =>
    simp only [KItem.fill, Runtime.Expr.arrayMake.injEq] at heq
    exact False.elim (hv₂ _ heq.2.symm)
  case arrayGetArr.arrayGetIdx =>
    simp only [KItem.fill, Runtime.Expr.arrayGet.injEq] at heq
    exact absurd heq.2.symm (hv₂ _)
  case arraySetIdx.arraySetVal =>
    simp only [KItem.fill, Runtime.Expr.arraySet.injEq] at heq
    exact absurd heq.2.2.symm (hv₂ _)
  case arraySetArr.arraySetVal =>
    simp only [KItem.fill, Runtime.Expr.arraySet.injEq] at heq
    exact absurd heq.2.2.symm (hv₂ _)
  case arraySetArr.arraySetIdx =>
    simp only [KItem.fill, Runtime.Expr.arraySet.injEq] at heq
    exact False.elim (hv₂ _ heq.2.1.symm)
  case appArgs.appArgs =>
    simp only [KItem.fill, Runtime.Expr.app.injEq, List.append_assoc,
      List.singleton_append] at heq
    obtain ⟨rfl, hlist⟩ := heq
    obtain ⟨rfl, -, hr⟩ := split_eq_of_focus hlist h₁ h₂
      (fun x hx => mem_map_val rfl hx) (fun x hx => mem_map_val rfl hx)
    rw [List.map_inj_right (fun _ _ h => Runtime.Expr.val_injective h)] at hr
    rw [hr]
  case appArgs.appFn =>
    exfalso
    simp only [KItem.fill, Runtime.Expr.app.injEq, List.append_assoc,
      List.singleton_append] at heq
    obtain ⟨v, hv⟩ := mem_map_val (e := e₁) heq.2 (by simp)
    exact hv₁ v hv
  case appFn.appArgs =>
    exfalso
    simp only [KItem.fill, Runtime.Expr.app.injEq, List.append_assoc,
      List.singleton_append] at heq
    obtain ⟨v, hv⟩ := mem_map_val (e := e₂) heq.2.symm (by simp)
    exact hv₂ v hv
  case appFn.appFn =>
    simp only [KItem.fill, Runtime.Expr.app.injEq] at heq
    rw [List.map_inj_right (fun _ _ h => Runtime.Expr.val_injective h)] at heq
    rw [heq.2]
  case tupleK.tupleK =>
    simp only [KItem.fill, Runtime.Expr.tuple.injEq, List.append_assoc,
      List.singleton_append] at heq
    obtain ⟨rfl, -, hr⟩ := split_eq_of_focus heq h₁ h₂
      (fun x hx => mem_map_val rfl hx) (fun x hx => mem_map_val rfl hx)
    rw [List.map_inj_right (fun _ _ h => Runtime.Expr.val_injective h)] at hr
    rw [hr]

theorem Head.val_stuck {ctx : PrimCtx} {e : Runtime.Expr} {μ μ' : Heap} {e' : Runtime.Expr}
    (h : Head ctx e μ e' μ') : exprVal e = none := by
  cases h <;> rfl

theorem Head.fill_val {ctx : PrimCtx} {Ki : KItem} {e : Runtime.Expr} {μ μ' : Heap}
    {e' : Runtime.Expr} (h : Head ctx (Ki.fill e) μ e' μ') : (exprVal e).isSome := by
  cases Ki <;>
    first
    | (cases h <;> simp [exprVal])
    | skip
  case appArgs fn left right =>
    simp only [KItem.fill] at h
    generalize hargs : left ++ [e] ++ List.map Runtime.Expr.val right = args at h
    cases h
    all_goals
      obtain ⟨v, rfl⟩ := mem_map_val (e := e) hargs (by simp)
      simp
  case appFn vs =>
    simp only [KItem.fill] at h
    generalize hargs : List.map Runtime.Expr.val vs = args at h
    cases h <;> simp [exprVal]
  case tupleK left right =>
    simp only [KItem.fill] at h
    generalize hargs : left ++ [e] ++ List.map Runtime.Expr.val right = args at h
    cases h
    obtain ⟨v, rfl⟩ := mem_map_val (e := e) hargs (by simp)
    simp

instance instEctxItemLanguage (ctx : PrimCtx) :
    EctxItemLanguage (LExpr ctx) KItem Heap Empty Runtime.Val where
  toVal := exprVal
  ofVal := .val
  coe_of_toVal_eq_some h := (exprVal_eq_some h).symm
  toVal_coe _ := rfl
  baseStep := fun (e, μ) obs (e', μ', eₜ) => Head ctx e μ e' μ' ∧ obs = [] ∧ eₜ = []
  fillItem := KItem.fill
  fillItem_inj {Ki} := Ki.fill_inj
  fillItem_val _ _ := KItem.fill_val
  fillItem_no_val_inj := KItem.fill_no_val_inj
  val_stuck h := h.1.val_stuck
  base_ctx_step_val h := h.1.fill_val

/-! ## Compound contexts

OpSem's compound contexts `K` convert to frame lists, transporting Iris's
context machinery (`Language.Context`, hence `wp_bind`) to `K.fill`. -/

/-- The frame list of a compound context, innermost frame first (the order of
    Iris's `EvContext.fill`). -/
def K.items : K → List KItem
  | .hole => []
  | .unop op k => k.items ++ [.unop op]
  | .binopR op lhs k => k.items ++ [.binopR op lhs]
  | .binopL op k v => k.items ++ [.binopL op v]
  | .appArgs fn left k right => k.items ++ [.appArgs fn left right]
  | .appFn k vs => k.items ++ [.appFn vs]
  | .ifCond k thn els => k.items ++ [.ifCond thn els]
  | .letProdK names k body => k.items ++ [.letProdK names body]
  | .ref k => k.items ++ [.ref]
  | .deref k => k.items ++ [.deref]
  | .storeR loc k => k.items ++ [.storeR loc]
  | .storeL k v => k.items ++ [.storeL v]
  | .arrayMakeInit len k => k.items ++ [.arrayMakeInit len]
  | .arrayMakeLen k init => k.items ++ [.arrayMakeLen init]
  | .arrayLen k => k.items ++ [.arrayLen]
  | .arrayGetIdx arr k => k.items ++ [.arrayGetIdx arr]
  | .arrayGetArr k idx => k.items ++ [.arrayGetArr idx]
  | .arraySetVal arr idx k => k.items ++ [.arraySetVal arr idx]
  | .arraySetIdx arr k val => k.items ++ [.arraySetIdx arr val]
  | .arraySetArr k idx val => k.items ++ [.arraySetArr idx val]
  | .assert k => k.items ++ [.assert]
  | .tupleK left k right => k.items ++ [.tupleK left right]
  | .injK tag arity k => k.items ++ [.injK tag arity]
  | .matchK branches k => k.items ++ [.matchK branches]

/-- Filling a frame list, innermost frame first. Definitionally equal to
    Iris's `EvContext.fill` for the TinyML instance. -/
def fillItems (ks : List KItem) (e : Runtime.Expr) : Runtime.Expr :=
  ks.foldl (fun x Ki => Ki.fill x) e

theorem K.fill_items (k : K) (e : Runtime.Expr) : k.fill e = fillItems k.items e := by
  induction k generalizing e <;>
    simp [K.fill, K.items, fillItems, List.foldl_append, KItem.fill, *]

/-- A frame as a one-frame compound context. -/
def KItem.toK : KItem → K
  | .unop op => .unop op .hole
  | .binopR op lhs => .binopR op lhs .hole
  | .binopL op v => .binopL op .hole v
  | .appArgs fn left right => .appArgs fn left .hole right
  | .appFn vs => .appFn .hole vs
  | .ifCond thn els => .ifCond .hole thn els
  | .letProdK names body => .letProdK names .hole body
  | .ref => .ref .hole
  | .deref => .deref .hole
  | .storeR loc => .storeR loc .hole
  | .storeL v => .storeL .hole v
  | .arrayMakeInit len => .arrayMakeInit len .hole
  | .arrayMakeLen init => .arrayMakeLen .hole init
  | .arrayLen => .arrayLen .hole
  | .arrayGetIdx arr => .arrayGetIdx arr .hole
  | .arrayGetArr idx => .arrayGetArr .hole idx
  | .arraySetVal arr idx => .arraySetVal arr idx .hole
  | .arraySetIdx arr val => .arraySetIdx arr .hole val
  | .arraySetArr idx val => .arraySetArr .hole idx val
  | .assert => .assert .hole
  | .tupleK left right => .tupleK left .hole right
  | .injK tag arity => .injK tag arity .hole
  | .matchK branches => .matchK branches .hole

@[simp] theorem KItem.toK_fill (Ki : KItem) (e : Runtime.Expr) :
    Ki.toK.fill e = Ki.fill e := by
  cases Ki <;> rfl

/-- A frame list as a compound context. -/
def K.ofItems : List KItem → K
  | [] => .hole
  | Ki :: ks => (K.ofItems ks).comp Ki.toK

theorem K.ofItems_fill (ks : List KItem) (e : Runtime.Expr) :
    (K.ofItems ks).fill e = fillItems ks e := by
  induction ks generalizing e with
  | nil => rfl
  | cons Ki ks ih =>
    simp [K.ofItems, fillItems, K.comp_fill, ih, List.foldl_cons]

/-- `wp_bind` works for `K.fill` of any compound context. -/
instance K.context (ctx : PrimCtx) (k : K) :
    Language.Context (State := Heap) (fun e : LExpr ctx => k.fill e) := by
  have h : (fun e : LExpr ctx => k.fill e) = EvContext.fill (Expr := LExpr ctx) k.items := by
    funext e
    exact K.fill_items k e
  rw [h]
  infer_instance

/-! ## Head-step inversion

Inversion lemmas for head steps whose source carries a value-mapped argument
list; plain `cases` fails there with dependent elimination. -/

theorem Head.beta_inv {ctx : PrimCtx} {f : Runtime.Binder} {args : List Runtime.Binder}
    {body e' : Runtime.Expr} {vs : Runtime.Vals} {μ μ' : Heap}
    (h : Head ctx (.app (.val (.fix f args body)) (vs.map .val)) μ e' μ') :
    e' = body.subst ((Runtime.Subst.id.updateBinder f (.fix f args body)).updateAllBinder args vs)
      ∧ μ' = μ := by
  generalize hl : List.map Runtime.Expr.val vs = l at h
  cases h
  obtain rfl := List.map_inj_right (fun _ _ h => Runtime.Expr.val_injective h) |>.mp hl
  exact ⟨rfl, rfl⟩

theorem Head.tuple_inv {ctx : PrimCtx} {vs : Runtime.Vals} {e' : Runtime.Expr} {μ μ' : Heap}
    (h : Head ctx (.tuple (vs.map .val)) μ e' μ') :
    e' = .val (.tuple vs) ∧ μ' = μ := by
  generalize hl : List.map Runtime.Expr.val vs = l at h
  cases h
  obtain rfl := List.map_inj_right (fun _ _ h => Runtime.Expr.val_injective h) |>.mp hl
  exact ⟨rfl, rfl⟩

theorem Head.prim_inv {ctx : PrimCtx} {n : String} {vs : Runtime.Vals} {e' : Runtime.Expr}
    {μ μ' : Heap} (h : Head ctx (.app (.val (.prim n)) (vs.map .val)) μ e' μ') :
    ∃ v, ctx n vs μ v μ' ∧ e' = .val v := by
  generalize hl : List.map Runtime.Expr.val vs = l at h
  cases h
  obtain rfl := List.map_inj_right (fun _ _ h => Runtime.Expr.val_injective h) |>.mp hl
  exact ⟨_, by assumption, rfl⟩

/-- Lists of impossible observations are empty (TinyML has no observations). -/
theorem obs_nil (obs : List Empty) : obs = [] := by
  cases obs with
  | nil => rfl
  | cons x _ => exact x.elim

/-- Any Iris primitive step of the TinyML language instance (with arbitrary
    observations and forked threads) is an OpSem step. -/
theorem Step.of_primStep {ctx : PrimCtx} {e e' : Runtime.Expr} {μ μ' : Heap}
    {obs : List Empty} {eₜ : List (LExpr ctx)}
    (h : PrimStep.primStep (Expr := LExpr ctx) (e, μ) obs (e', μ', eₜ)) :
    Step ctx e μ e' μ' := by
  rcases h with ⟨⟨hh, -, -⟩⟩
  rename_i e₁ e₂ ks
  show Step ctx (fillItems ks e₁) μ (fillItems ks e₂) μ'
  rw [← K.ofItems_fill, ← K.ofItems_fill]
  exact Step.ctx (K.ofItems ks) hh

/-- OpSem's contextual step agrees with the Iris-derived primitive step of the
    TinyML language instance. -/
theorem Step.iff_primStep {ctx : PrimCtx} {e e' : Runtime.Expr} {μ μ' : Heap} :
    Step ctx e μ e' μ' ↔
      PrimStep.primStep (Expr := LExpr ctx) (e, μ) ([] : List Empty) (e', μ', []) := by
  constructor
  · rintro ⟨k, hh⟩
    exact BaseStep.ContextStep.ofBaseStep' k.items
      (K.fill_items k _).symm (K.fill_items k _).symm ⟨hh, rfl, rfl⟩
  · exact Step.of_primStep

end TinyML
