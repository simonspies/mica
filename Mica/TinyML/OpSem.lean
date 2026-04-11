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
  | .assert k1,         k2 => .assert (k1.comp k2)
  | .tupleK left k1 right, k2 => .tupleK left (k1.comp k2) right
  | .injK tag arity k1,    k2 => .injK tag arity (k1.comp k2)
  | .matchK branches k1,   k2 => .matchK branches (k1.comp k2)

theorem K.comp_fill (k1 k2 : K) (e : Runtime.Expr) :
    (k1.comp k2).fill e = k1.fill (k2.fill e) := by
  induction k1 <;> simp_all [K.comp, K.fill]

/-! ## Head reduction -/

inductive Head : Runtime.Expr → Heap → Runtime.Expr → Heap → Prop where
  /-- A `fix` expression wraps itself as a value. -/
  | fixIntro : Head (.fix f args body) μ (.val (.fix f args body)) μ

  /-- Beta reduction: apply a fixpoint to a list of argument values. -/
  | beta : args.length = vs.length →
           Head (.app (.val (.fix f args body)) (vs.map Runtime.Expr.val)) μ
                (body.subst ((Runtime.Subst.id.update' f (.fix f args body)).updateAll' args vs)) μ

  /-- Unary operator applied to a value. -/
  | unop : evalUnOp op v = some w →
           Head (.unop op (.val v)) μ (.val w) μ

  /-- Binary operator applied to two values. -/
  | binop : evalBinOp op v1 v2 = some w →
            Head (.binop op (.val v1) (.val v2)) μ (.val w) μ

  /-- Conditional on true. -/
  | ifTrue  : Head (.ifThenElse (.val (.bool true))  thn els) μ thn μ
  /-- Conditional on false. -/
  | ifFalse : Head (.ifThenElse (.val (.bool false)) thn els) μ els μ

  /-- Allocate a fresh location. -/
  | ref : Heap.Fresh l μ →
          Head (.ref (.val v)) μ (.val (.loc l)) (μ.update l v)

  /-- Dereference a location. -/
  | deref : μ.lookup l = some v →
            Head (.deref (.val (.loc l))) μ (.val v) μ

  /-- Write to a location. -/
  | store :
    μ.lookup l = some w →
    Head (.store (.val (.loc l)) (.val v)) μ (.val .unit) (μ.update l v)

  /-- Assert succeeds on true; false is stuck (no rule). -/
  | assertOk : Head (.assert (.val (.bool true))) μ (.val .unit) μ

  /-- A tuple of values reduces to a tuple value. -/
  | tuple : Head (.tuple (vs.map Runtime.Expr.val)) μ (.val (.tuple vs)) μ

  /-- Injection of a value becomes a value. -/
  | injVal : Head (.inj tag arity (.val v)) μ (.val (.inj tag arity v)) μ

  /-- Match on an injected value: select the branch and apply it to the payload. -/
  | match_ : (h : i < branches.length) → n = branches.length →
             Head (.match_ (.val (.inj i n v)) branches) μ (.app (branches[i]) [.val v]) μ

/-! ## Contextual step -/

inductive Step : Runtime.Expr → Heap → Runtime.Expr → Heap → Prop where
  | ctx : ∀ (k : K), Head e μ e' μ' → Step (k.fill e) μ (k.fill e') μ'

/-- A single step can be lifted into any surrounding context. -/
theorem Step.lift_ctx (k : K) (h : Step e μ e' μ') : Step (k.fill e) μ (k.fill e') μ' := by
  cases h with
  | ctx k0 hhead =>
    rw [← K.comp_fill, ← K.comp_fill]
    exact Step.ctx (k.comp k0) hhead

/-! ## Multi-step reduction -/

inductive Steps : Runtime.Expr → Heap → Runtime.Expr → Heap → Prop where
  | refl : Steps e μ e μ
  | step : Step e μ e'' μ'' → Steps e'' μ'' e' μ' → Steps e μ e' μ'

theorem Steps.trans (h1 : Steps e μ e'' μ'') (h2 : Steps e'' μ'' e' μ') :
    Steps e μ e' μ' := by
  induction h1 with
  | refl => exact h2
  | step hs _ ih => exact Steps.step hs (ih h2)

/-- Multi-step reduction can be lifted into any surrounding context. -/
theorem Steps.lift_ctx (k : K) (h : Steps e μ e' μ') :
    Steps (k.fill e) μ (k.fill e') μ' := by
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
