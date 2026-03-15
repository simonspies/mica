import Mica.FOL.Printing
import Mica.TinyML
import Mica.Verifier.Assertions
import Mica.Verifier.PredicateTransformers

/-!
# AssertionLanguage

Defines `SpecParser`, a pipeline that translates `[@@spec ...]` expressions into `Spec`
values.

## Assertion surface syntax

| Constructor              | Surface syntax            |
|--------------------------|---------------------------|
| `Assertion.ret e`        | `ret e`                   |
| `Assertion.assert φ k`   | `assert φ; k`             |
| `Assertion.let_ v t k`   | `let x = t in k`          |
| `Assertion.pred v p k`   | `bind (p e) @@ fun x -> k`|
| `Assertion.ite φ kt ke`  | `if φ then kt else ke`    |

## Sort inference

Parsing uses a bidirectional type system (`infer` / `check`) with a variable
environment `SpecEnv`. The environment is extended at each binding site: `fun`
binders add `.value` variables, `bind` binders add the type determined by the
predicate, and `let` binders use the inferred type of the bound expression.

All parsers have type `Parser α = SpecEnv → TinyML.Expr → Except String α`.
-/


-- ---------------------------------------------------------------------------
-- Bidirectional type inference for terms and formulas
-- ---------------------------------------------------------------------------

abbrev SpecEnv := List (String × Srt)

def SpecEnv.lookup (env : SpecEnv) (x : String) : Option Srt :=
  (env.find? (·.1 == x)).map (·.2)

-- All parsers carry an explicit `SpecEnv`.
def Parser α := SpecEnv → TinyML.Expr → Except String α

namespace SpecParser

mutual  -- infer / check / formula

/-- Infer the type and value of an expression as a `Term`. -/
def infer (env : SpecEnv) : TinyML.Expr → Except String (Σ t, Term t)
  | .var x => match env.lookup x with
    | some sort => .ok ⟨sort, .var sort x⟩
    | none    => .error s!"unbound variable '{x}'"
  | .val (.int n) => .ok ⟨.int, .const (.i n)⟩
  | .binop .add l r => do
    .ok ⟨.int, .binop .add (← check env .int l) (← check env .int r)⟩
  | .binop .sub l r => do
    .ok ⟨.int, .binop .sub (← check env .int l) (← check env .int r)⟩
  | .binop .mul l r => do
    .ok ⟨.int, .binop .mul (← check env .int l) (← check env .int r)⟩
  | .binop .div l r => do
    .ok ⟨.int, .binop .div (← check env .int l) (← check env .int r)⟩
  | .unop .neg e => do
    .ok ⟨.int, .unop .neg (← check env .int e)⟩
  | .ifThenElse c th el => do
    let ⟨t, th'⟩ ← infer env th
    .ok ⟨t, .ite (← check env .bool c) th' (← check env t el)⟩
  | e => .error s!"cannot infer type of {repr e}"

/-- Check that an expression has type `t`, returning `Term t`. -/
def check (env : SpecEnv) (t : Srt) : TinyML.Expr → Except String (Term t)
  | .var x => match env.lookup x with
    | none    => .error s!"unbound variable '{x}'"
    | some sort =>
      if h : sort = t then .ok (h ▸ .var sort x)
      else .error s!"variable '{x}' has type {repr sort}, expected {repr t}"
  | .val (.int n) => match t with
    | .int   => .ok (.const (.i n))
    | .value => .ok (.unop .ofInt (.const (.i n)))
    | .bool  => .error s!"integer literal cannot be a bool term"
  | .val (.bool b) => match t with
    | .bool  => .ok (.const (.b b))
    | .value => .ok (.unop .ofBool (.const (.b b)))
    | .int   => .error s!"boolean literal cannot be an int term"
  | .binop .add l r => match t with
    | .int => do .ok (.binop .add (← check env .int l) (← check env .int r))
    | _    => .error s!"add produces .int, expected {repr t}"
  | .binop .sub l r => match t with
    | .int => do .ok (.binop .sub (← check env .int l) (← check env .int r))
    | _    => .error s!"sub produces .int, expected {repr t}"
  | .binop .mul l r => match t with
    | .int => do .ok (.binop .mul (← check env .int l) (← check env .int r))
    | _    => .error s!"mul produces .int, expected {repr t}"
  | .binop .div l r => match t with
    | .int => do .ok (.binop .div (← check env .int l) (← check env .int r))
    | _    => .error s!"div produces .int, expected {repr t}"
  | .unop .neg e => match t with
    | .int => do .ok (.unop .neg (← check env .int e))
    | _    => .error s!"neg produces .int, expected {repr t}"
  | .ifThenElse c th el => do
    .ok (.ite (← check env .bool c) (← check env t th) (← check env t el))
  | e =>
    -- fall back to infer and check the result type matches
    match infer env e with
    | .ok ⟨sort, tm⟩ =>
      if h : sort = t then .ok (h ▸ tm)
      else .error s!"expression has type {repr sort}, expected {repr t}"
    | .error msg => .error msg

/-- Convert a TinyML expression to a `Formula`. -/
def formula (env : SpecEnv) : TinyML.Expr → Except String Formula
  | .binop .eq l r => do
    let ⟨t, tl⟩ ← infer env l
    .ok (.eq t tl (← check env t r))
  | .binop .lt l r => do
    .ok (.binpred .lt (← check env .int l) (← check env .int r))
  | .binop .le l r => do
    .ok (.binpred .le (← check env .int l) (← check env .int r))
  | .binop .gt l r => do   -- rewrite as .lt with swapped args (no .gt in Formula)
    .ok (.binpred .lt (← check env .int r) (← check env .int l))
  | .binop .ge l r => do   -- rewrite as .le with swapped args (no .ge in Formula)
    .ok (.binpred .le (← check env .int r) (← check env .int l))
  | .binop .and l r => do .ok (.and (← formula env l) (← formula env r))
  | .binop .or  l r => do .ok (.or  (← formula env l) (← formula env r))
  | .unop .not e    => do .ok (.not (← formula env e))
  | e => .error s!"cannot convert {repr e} to a formula"

end  -- mutual


-- Recognises `isint e` and `isbool e`; argument checked at `.value`.
def typePred (env : SpecEnv) : TinyML.Expr → Except String (Σ t, Atom t)
  | .app (.var "isint")  e => do .ok ⟨.int,  .isint  (← check env .value e)⟩
  | .app (.var "isbool") e => do .ok ⟨.bool, .isbool (← check env .value e)⟩
  | e => .error s!"expected isint or isbool application, got {repr e}"

-- Recognises exactly one `fun x -> e` binder; adds `x : .value` to env.
def pred (inner : Parser α) : Parser (Pred α)
  | env, .fix .none (.named x) _ _ body => do
    .ok (x, ← inner ((x, .value) :: env) body)
  | _, e => .error s!"expected λ x -> ..., got {repr e}"

-- Greedily strips `fun x ->` binders, adding each as `x : .value`.
def multiPred (inner : Parser α) : Parser (MultiPred α) := fun env e =>
  let rec go : SpecEnv → TinyML.Expr → Except String (List String × α)
    | env, .fix .none (.named x) _ _ body =>
      let env' := (x, .value) :: env
      match go env' body with
      | .ok (xs, a) => .ok (x :: xs, a)
      | .error _    => do .ok ([], ← inner env (.fix .none (.named x) none none body))
    | env, e => do .ok ([], ← inner env e)
  go env e

-- Recognises `()` only; ignores the env.
def unit : Parser Unit
  | _, .val .unit => .ok ()
  | _, e => .error s!"expected (), got {repr e}"

-- Parses an `Assertion α`.
-- `bind e1 (fun x -> e2)`: type of `x` comes from the typePred in `e1`.
-- `let x = e in body`: type of `x` inferred from `e`.
def assertion (inner : Parser α) : Parser (Assertion α)
  | env, .app (.var "ret") e => do
    .ok (.ret (← inner env e))
  | env, .app (.app (.var "bind") e1) (.fix .none (.named x) _ _ e2) => do
    let ⟨t, p⟩ ← typePred env e1
    .ok (.pred ⟨x, t⟩ p (← assertion inner ((x, t) :: env) e2))
  | env, .letIn (.named x) bound body => do
    let ⟨t, tm⟩ ← infer env bound
    .ok (.let_ ⟨x, t⟩ tm (← assertion inner ((x, t) :: env) body))
  | env, .letIn .none (.assert cond) body => do
    .ok (.assert (← formula env cond) (← assertion inner env body))
  | env, .ifThenElse cond th el => do
    .ok (.ite (← formula env cond)
              (← assertion inner env th)
              (← assertion inner env el))
  | _, e => .error s!"expected assertion expression, got {repr e}"

def predtrans : Parser PredTrans := assertion (pred (assertion unit))

def spec : Parser SpecPredicate := pred predtrans

end SpecParser
