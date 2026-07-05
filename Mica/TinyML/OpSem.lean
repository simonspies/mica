-- SUMMARY: Operational semantics for the TinyML runtime IR.
import Mica.TinyML.Common
import Mica.TinyML.RuntimeExpr
import Mica.TinyML.Heap

namespace TinyML

/-! ## Pure evaluation functions -/

def evalUnOp (op : TinyML.UnOp) (v : Runtime.Val) : Option Runtime.Val :=
  match op, v with
  | .neg, .int n    => some (.int (-n))
  | .not, .bool b   => some (.bool (!b))
  | .proj n, .tuple vs => vs[n]?
  | _, _            => none

def evalBinOp (op : TinyML.BinOp) (v1 v2 : Runtime.Val) : Option Runtime.Val :=
  match op, v1, v2 with
  | .add, .int a, .int b  => some (.int (a + b))
  | .sub, .int a, .int b  => some (.int (a - b))
  | .mul, .int a, .int b  => some (.int (a * b))
  | .div, .int a, .int b  => if b = 0 then none else some (.int (a / b))
  | .mod, .int a, .int b  => if b = 0 then none else some (.int (a % b))
  | .eq,  .int a, .int b  => some (.bool (a == b))
  | .lt,  .int a, .int b  => some (.bool (a < b))
  | .le,  .int a, .int b  => some (.bool (a ≤ b))
  | .gt,  .int a, .int b  => some (.bool (a > b))
  | .ge,  .int a, .int b  => some (.bool (a ≥ b))
  | .and, .bool a, .bool b => some (.bool (a && b))
  | .or,  .bool a, .bool b => some (.bool (a || b))
  | _, _, _                => none

/-! ## Evaluation contexts -/

/-- Evaluation contexts encode TinyML's right-to-left operand order. -/
inductive K where
  | hole
  | unop   (op : TinyML.UnOp)  (k : K)
  | binopR (op : TinyML.BinOp) (lhs : Runtime.Expr) (k : K)   -- rhs in focus (eval first)
  | binopL (op : TinyML.BinOp) (k : K)      (v : Runtime.Val)  -- lhs in focus, rhs done
  | appArgs (fn : Runtime.Expr) (left : Runtime.Exprs) (k : K) (right : Runtime.Vals)  -- evaluating one arg in a list
  | appFn   (k : K)    (vs : Runtime.Vals)                             -- fn in focus, all args are values
  | ifCond (k : K) (thn els : Runtime.Expr)
  | ref    (k : K)
  | deref  (k : K)
  | storeR (loc : Runtime.Expr) (k : K)                 -- val in focus (eval first)
  | storeL (k : K)      (v : Runtime.Val)               -- loc in focus, val done
  | arrayMakeInit (len : Runtime.Expr) (k : K)
  | arrayMakeLen (k : K) (init : Runtime.Val)
  | arrayLen (k : K)
  | arrayGetIdx (arr : Runtime.Expr) (k : K)
  | arrayGetArr (k : K) (idx : Runtime.Val)
  | arraySetVal (arr idx : Runtime.Expr) (k : K)
  | arraySetIdx (arr : Runtime.Expr) (k : K) (val : Runtime.Val)
  | arraySetArr (k : K) (idx val : Runtime.Val)
  | assert (k : K)
  | tupleK (left : Runtime.Exprs) (k : K) (right : Runtime.Vals)
  | injK   (tag : Nat) (arity : Nat) (k : K)
  | matchK (branches : List Runtime.Expr) (k : K)

def K.fill : K → Runtime.Expr → Runtime.Expr
  | .hole,              e => e
  | .unop op k,         e => .unop op (k.fill e)
  | .binopR op lhs k,   e => .binop op lhs (k.fill e)
  | .binopL op k v,     e => .binop op (k.fill e) (.val v)
  | .appArgs fn left k right, e => .app fn (left ++ [k.fill e] ++ right.map Runtime.Expr.val)
  | .appFn k vs,              e => .app (k.fill e) (vs.map Runtime.Expr.val)
  | .ifCond k thn els,  e => .ifThenElse (k.fill e) thn els
  | .ref k,             e => .ref (k.fill e)
  | .deref k,           e => .deref (k.fill e)
  | .storeR loc k,      e => .store loc (k.fill e)
  | .storeL k v,        e => .store (k.fill e) (.val v)
  | .arrayMakeInit len k, e => .arrayMake len (k.fill e)
  | .arrayMakeLen k init, e => .arrayMake (k.fill e) (.val init)
  | .arrayLen k,        e => .arrayLen (k.fill e)
  | .arrayGetIdx arr k, e => .arrayGet arr (k.fill e)
  | .arrayGetArr k idx, e => .arrayGet (k.fill e) (.val idx)
  | .arraySetVal arr idx k, e => .arraySet arr idx (k.fill e)
  | .arraySetIdx arr k val, e => .arraySet arr (k.fill e) (.val val)
  | .arraySetArr k idx val, e => .arraySet (k.fill e) (.val idx) (.val val)
  | .assert k,          e => .assert (k.fill e)
  | .tupleK left k right, e => .tuple (left ++ [k.fill e] ++ right.map Runtime.Expr.val)
  | .injK tag arity k,    e => .inj tag arity (k.fill e)
  | .matchK branches k,   e => .match_ (k.fill e) branches

/-- Compose two contexts: `(k1.comp k2).fill e = k1.fill (k2.fill e)`. -/
def K.comp : K → K → K
  | .hole,              k2 => k2
  | .unop op k1,        k2 => .unop op (k1.comp k2)
  | .binopR op lhs k1,  k2 => .binopR op lhs (k1.comp k2)
  | .binopL op k1 v,    k2 => .binopL op (k1.comp k2) v
  | .appArgs fn left k1 right, k2 => .appArgs fn left (k1.comp k2) right
  | .appFn k1 vs,              k2 => .appFn (k1.comp k2) vs
  | .ifCond k1 thn els, k2 => .ifCond (k1.comp k2) thn els
  | .ref k1,            k2 => .ref (k1.comp k2)
  | .deref k1,          k2 => .deref (k1.comp k2)
  | .storeR loc k1,     k2 => .storeR loc (k1.comp k2)
  | .storeL k1 v,       k2 => .storeL (k1.comp k2) v
  | .arrayMakeInit len k1, k2 => .arrayMakeInit len (k1.comp k2)
  | .arrayMakeLen k1 init, k2 => .arrayMakeLen (k1.comp k2) init
  | .arrayLen k1,       k2 => .arrayLen (k1.comp k2)
  | .arrayGetIdx arr k1, k2 => .arrayGetIdx arr (k1.comp k2)
  | .arrayGetArr k1 idx, k2 => .arrayGetArr (k1.comp k2) idx
  | .arraySetVal arr idx k1, k2 => .arraySetVal arr idx (k1.comp k2)
  | .arraySetIdx arr k1 val, k2 => .arraySetIdx arr (k1.comp k2) val
  | .arraySetArr k1 idx val, k2 => .arraySetArr (k1.comp k2) idx val
  | .assert k1,         k2 => .assert (k1.comp k2)
  | .tupleK left k1 right, k2 => .tupleK left (k1.comp k2) right
  | .injK tag arity k1,    k2 => .injK tag arity (k1.comp k2)
  | .matchK branches k1,   k2 => .matchK branches (k1.comp k2)

theorem K.comp_fill (k1 k2 : K) (e : Runtime.Expr) :
    (k1.comp k2).fill e = k1.fill (k2.fill e) := by
  induction k1 <;> simp_all [K.comp, K.fill]

abbrev PrimCtx := String → List Runtime.Val → Heap → Runtime.Val → Heap → Prop

/-! ## Head reduction -/

inductive Head (ctx : PrimCtx) : Runtime.Expr → Heap → Runtime.Expr → Heap → Prop where
  /-- A `fix` expression wraps itself as a value. -/
  | fixIntro : Head ctx (.fix f args body) μ (.val (.fix f args body)) μ

  /-- Beta reduction: apply a fixpoint to a list of argument values. -/
  | beta : args.length = vs.length →
           Head ctx (.app (.val (.fix f args body)) (vs.map Runtime.Expr.val)) μ
                (body.subst ((Runtime.Subst.id.updateBinder f (.fix f args body)).updateAllBinder args vs)) μ

  /-- Unary operator applied to a value. -/
  | unop : evalUnOp op v = some w →
           Head ctx (.unop op (.val v)) μ (.val w) μ

  /-- Binary operator applied to two values. -/
  | binop : evalBinOp op v1 v2 = some w →
            Head ctx (.binop op (.val v1) (.val v2)) μ (.val w) μ

  /-- Conditional on true. -/
  | ifTrue  : Head ctx (.ifThenElse (.val (.bool true))  thn els) μ thn μ
  /-- Conditional on false. -/
  | ifFalse : Head ctx (.ifThenElse (.val (.bool false)) thn els) μ els μ

  /-- Allocate a fresh location holding a singleton block. -/
  | ref : Heap.Fresh l μ →
          Head ctx (.ref (.val v)) μ (.val (.loc l)) (μ.update l [v])

  /-- Dereference a location: read field `0` of its block. -/
  | deref : Heap.lookupField l 0 μ = some v →
            Head ctx (.deref (.val (.loc l))) μ (.val v) μ

  /-- Write to a location: update field `0` of its block. -/
  | store :
    Heap.lookupField l 0 μ = some w →
    Head ctx (.store (.val (.loc l)) (.val v)) μ (.val .unit) (Heap.updateField l 0 v μ)

  /-- Allocate a fresh array block of length `n`, initialized with `v`. -/
  | arrayMake : 0 ≤ n → Heap.Fresh l μ →
      Head ctx (.arrayMake (.val (.int n)) (.val v)) μ
        (.val (.array n.toNat l)) (μ.update l (List.replicate n.toNat v))

  /-- Array length is stored in the array value. -/
  | arrayLen :
      Head ctx (.arrayLen (.val (.array len l))) μ (.val (.int len)) μ

  /-- Array read at an in-bounds integer index. -/
  | arrayGet : 0 ≤ i → i.toNat < len → Heap.lookupField l i.toNat μ = some v →
      Head ctx (.arrayGet (.val (.array len l)) (.val (.int i))) μ (.val v) μ

  /-- Array write at an in-bounds integer index. -/
  | arraySet : 0 ≤ i → i.toNat < len → Heap.lookupField l i.toNat μ = some old →
      Head ctx (.arraySet (.val (.array len l)) (.val (.int i)) (.val v)) μ
        (.val .unit) (Heap.updateField l i.toNat v μ)

  /-- Assert succeeds on true; false is stuck (no rule). -/
  | assertOk : Head ctx (.assert (.val (.bool true))) μ (.val .unit) μ

  /-- A tuple of values reduces to a tuple value. -/
  | tuple : Head ctx (.tuple (vs.map Runtime.Expr.val)) μ (.val (.tuple vs)) μ

  /-- Injection of a value becomes a value. -/
  | injVal : Head ctx (.inj tag arity (.val v)) μ (.val (.inj tag arity v)) μ

  /-- Match on an injected value: select the branch and apply it to the payload. -/
  | match_ : (h : i < branches.length) → n = branches.length →
             Head ctx (.match_ (.val (.inj i n v)) branches) μ (.app (branches[i]) [.val v]) μ

  /-- Primitive call: the registry-derived context relates the name, argument
      values, and pre-heap to a result value and post-heap. Unbound names are
      not in the relation, making the call stuck. -/
  | primStep {n vs v μ'} :
      ctx n vs μ v μ' →
      Head ctx (.app (.val (.prim n)) (vs.map Runtime.Expr.val)) μ (.val v) μ'

/-! ## Contextual step -/

inductive Step (ctx : PrimCtx) : Runtime.Expr → Heap → Runtime.Expr → Heap → Prop where
  | ctx : ∀ (k : K), Head ctx e μ e' μ' → Step ctx (k.fill e) μ (k.fill e') μ'

/-- A single step can be lifted into any surrounding context. -/
theorem Step.lift_ctx {ctx : PrimCtx} (k : K) (h : Step ctx e μ e' μ') :
    Step ctx (k.fill e) μ (k.fill e') μ' := by
  cases h with
  | ctx k0 hhead =>
    rw [← K.comp_fill, ← K.comp_fill]
    exact Step.ctx (k.comp k0) hhead

/-! ## Multi-step reduction -/

inductive Steps (ctx : PrimCtx) : Runtime.Expr → Heap → Runtime.Expr → Heap → Prop where
  | refl : Steps ctx e μ e μ
  | step : Step ctx e μ e'' μ'' → Steps ctx e'' μ'' e' μ' → Steps ctx e μ e' μ'

theorem Steps.trans {ctx : PrimCtx} (h1 : Steps ctx e μ e'' μ'') (h2 : Steps ctx e'' μ'' e' μ') :
    Steps ctx e μ e' μ' := by
  induction h1 with
  | refl => exact h2
  | step hs _ ih => exact Steps.step hs (ih h2)

/-- Multi-step reduction can be lifted into any surrounding context. -/
theorem Steps.lift_ctx {ctx : PrimCtx} (k : K) (h : Steps ctx e μ e' μ') :
    Steps ctx (k.fill e) μ (k.fill e') μ' := by
  induction h with
  | refl => exact Steps.refl
  | step hs _ ih => exact Steps.step (hs.lift_ctx k) ih

/-! ## List evaluation contexts -/

/-- A position within a list of expressions being evaluated right-to-left.
    `left` contains unevaluated expressions to the left of the focus,
    `right` contains already-evaluated values to the right. -/
structure ListK where
  left : Runtime.Exprs
  right : Runtime.Vals

/-- Reconstruct the full list by placing the focused expression between
    the unevaluated left and the already-evaluated right. -/
def ListK.fill (lk : ListK) (e : Runtime.Expr) : Runtime.Exprs :=
  lk.left ++ [e] ++ lk.right.map Runtime.Expr.val

@[simp] theorem ListK.fill_mk (left : Runtime.Exprs) (right : Runtime.Vals) (e : Runtime.Expr) :
    ListK.fill ⟨left, right⟩ e = left ++ [e] ++ right.map Runtime.Expr.val := rfl

theorem ListK.fill_length (lk : ListK) (e : Runtime.Expr) :
    (lk.fill e).length = lk.left.length + 1 + lk.right.length := by
  simp [ListK.fill, List.length_append, List.length_map]; omega

/-- An empty list context: no expressions evaluated yet, none waiting. -/
def ListK.empty : ListK := ⟨[], []⟩

@[simp] theorem ListK.fill_empty (e : Runtime.Expr) :
    ListK.empty.fill e = [e] := rfl

end TinyML
