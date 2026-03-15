import Mica.TinyML.Expr
import Mica.TinyML.Heap

namespace TinyML

/-! ## Pure evaluation functions -/

def evalUnOp (op : UnOp) (v : Val) : Option Val :=
  match op, v with
  | .neg, .int n    => some (.int (-n))
  | .not, .bool b   => some (.bool (!b))
  | .fst, .pair a _ => some a
  | .snd, .pair _ b => some b
  | .inl, v         => some (.inl v)
  | .inr, v         => some (.inr v)
  | _, _            => none

def evalBinOp (op : BinOp) (v1 v2 : Val) : Option Val :=
  match op, v1, v2 with
  | .add, .int a, .int b  => some (.int (a + b))
  | .sub, .int a, .int b  => some (.int (a - b))
  | .mul, .int a, .int b  => some (.int (a * b))
  | .div, .int a, .int b  => if b = 0 then none else some (.int (a / b))
  | .eq,  .int a, .int b  => some (.bool (a == b))
  | .lt,  .int a, .int b  => some (.bool (a < b))
  | .le,  .int a, .int b  => some (.bool (a ≤ b))
  | .gt,  .int a, .int b  => some (.bool (a > b))
  | .ge,  .int a, .int b  => some (.bool (a ≥ b))
  | .and, .bool a, .bool b => some (.bool (a && b))
  | .or,  .bool a, .bool b => some (.bool (a || b))
  | .pair, a, b            => some (.pair a b)
  | _, _, _                => none

/-! ## Evaluation contexts -/

inductive K where
  | hole
  | unop   (op : UnOp)  (k : K)
  | binopR (op : BinOp) (lhs : Expr) (k : K)   -- rhs in focus (eval first)
  | binopL (op : BinOp) (k : K)      (v : Val)  -- lhs in focus, rhs done
  | appR   (fn : Expr)  (k : K)                 -- arg in focus (eval first)
  | appL   (k : K)      (v : Val)               -- fn in focus, arg done
  | ifCond (k : K) (thn els : Expr)
  | letIn  (name : Binder) (k : K) (body : Expr)
  | ref    (k : K)
  | deref  (k : K)
  | storeR (loc : Expr) (k : K)                 -- val in focus (eval first)
  | storeL (k : K)      (v : Val)               -- loc in focus, val done
  | assert (k : K)
  | tupleK (left : Exprs) (k : K) (right : Vals)

def K.fill : K → Expr → Expr
  | .hole,              e => e
  | .unop op k,         e => .unop op (k.fill e)
  | .binopR op lhs k,   e => .binop op lhs (k.fill e)
  | .binopL op k v,     e => .binop op (k.fill e) (.val v)
  | .appR fn k,         e => .app fn (k.fill e)
  | .appL k v,          e => .app (k.fill e) (.val v)
  | .ifCond k thn els,  e => .ifThenElse (k.fill e) thn els
  | .letIn b k body,    e => .letIn b (k.fill e) body
  | .ref k,             e => .ref (k.fill e)
  | .deref k,           e => .deref (k.fill e)
  | .storeR loc k,      e => .store loc (k.fill e)
  | .storeL k v,        e => .store (k.fill e) (.val v)
  | .assert k,          e => .assert (k.fill e)
  | .tupleK left k right, e => .tuple (left ++ [k.fill e] ++ right.map Expr.val)

/-- Compose two contexts: `(k1.comp k2).fill e = k1.fill (k2.fill e)`. -/
def K.comp : K → K → K
  | .hole,              k2 => k2
  | .unop op k1,        k2 => .unop op (k1.comp k2)
  | .binopR op lhs k1,  k2 => .binopR op lhs (k1.comp k2)
  | .binopL op k1 v,    k2 => .binopL op (k1.comp k2) v
  | .appR fn k1,        k2 => .appR fn (k1.comp k2)
  | .appL k1 v,         k2 => .appL (k1.comp k2) v
  | .ifCond k1 thn els, k2 => .ifCond (k1.comp k2) thn els
  | .letIn b k1 body,   k2 => .letIn b (k1.comp k2) body
  | .ref k1,            k2 => .ref (k1.comp k2)
  | .deref k1,          k2 => .deref (k1.comp k2)
  | .storeR loc k1,     k2 => .storeR loc (k1.comp k2)
  | .storeL k1 v,       k2 => .storeL (k1.comp k2) v
  | .assert k1,         k2 => .assert (k1.comp k2)
  | .tupleK left k1 right, k2 => .tupleK left (k1.comp k2) right

theorem K.comp_fill (k1 k2 : K) (e : Expr) :
    (k1.comp k2).fill e = k1.fill (k2.fill e) := by
  induction k1 <;> simp_all [K.comp, K.fill]

/-! ## Head reduction -/

inductive Head : Expr → Heap → Expr → Heap → Prop where
  /-- A `fix` expression wraps itself as a value. -/
  | fixIntro : Head (.fix f x at_ rt body) μ (.val (.fix f x at_ rt body)) μ

  /-- Beta reduction: apply a fixpoint to an argument value. -/
  | beta : Head (.app (.val (.fix f x at_ rt body)) (.val v)) μ
                (body.subst ((Subst.id.update' f (.fix f x at_ rt body)).update' x v)) μ

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

  /-- Let-binding with a value: substitute and continue. -/
  | letVal : Head (.letIn b (.val v) body) μ (body.subst (Subst.id.update' b v)) μ

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
  | tuple : Head (.tuple (vs.map Expr.val)) μ (.val (.tuple vs)) μ

/-! ## Contextual step -/

inductive Step : Expr → Heap → Expr → Heap → Prop where
  | ctx : ∀ (k : K), Head e μ e' μ' → Step (k.fill e) μ (k.fill e') μ'

/-- A single step can be lifted into any surrounding context. -/
theorem Step.lift_ctx (k : K) (h : Step e μ e' μ') : Step (k.fill e) μ (k.fill e') μ' := by
  cases h with
  | ctx k0 hhead =>
    rw [← K.comp_fill, ← K.comp_fill]
    exact Step.ctx (k.comp k0) hhead

/-! ## Multi-step reduction -/

inductive Steps : Expr → Heap → Expr → Heap → Prop where
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
  left : Exprs
  right : Vals

/-- Reconstruct the full list by placing the focused expression between
    the unevaluated left and the already-evaluated right. -/
def ListK.fill (lk : ListK) (e : Expr) : Exprs :=
  lk.left ++ [e] ++ lk.right.map Expr.val

@[simp] theorem ListK.fill_mk (left : Exprs) (right : Vals) (e : Expr) :
    ListK.fill ⟨left, right⟩ e = left ++ [e] ++ right.map Expr.val := rfl

theorem ListK.fill_length (lk : ListK) (e : Expr) :
    (lk.fill e).length = lk.left.length + 1 + lk.right.length := by
  simp [ListK.fill, List.length_append, List.length_map]; omega

/-- An empty list context: no expressions evaluated yet, none waiting. -/
def ListK.empty : ListK := ⟨[], []⟩

@[simp] theorem ListK.fill_empty (e : Expr) :
    ListK.empty.fill e = [e] := rfl

end TinyML
