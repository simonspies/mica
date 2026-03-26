import Mica.Frontend.Spec
import Mica.FOL.Printing
import Mica.Verifier.Assertions
import Mica.Verifier.PredicateTransformers

/-!
# Spec Translation

Sort-checks the untyped `Spec` AST and translates it into typed
`Term`/`Formula`/`Assertion` values.
-/

namespace SpecTranslation

abbrev Env := List (String × Srt)

private def Env.lookup (env : Env) (x : String) : Option Srt :=
  (env.find? (·.1 == x)).map (·.2)

private abbrev M := Except String

-- ---------------------------------------------------------------------------
-- Terms
-- ---------------------------------------------------------------------------

/-- Apply `vtail` n times to a vallist term. -/
private def vtailN (t : Term .vallist) : Nat → Term .vallist
  | 0     => t
  | n + 1 => .unop .vtail (vtailN t n)

private def castTerm (τ : Srt) (ctx : String) : (Σ t, Term t) → M (Term τ)
  | ⟨τ', t⟩ => if h : τ' = τ then .ok (h ▸ t)
    else .error s!"{ctx} has sort {repr τ'}, expected {repr τ}"

mutual
def inferTerm (env : Env) : Spec.Term → M (Σ t, Term t)
  | .var x => match env.lookup x with
    | some sort => .ok ⟨sort, .var sort x⟩
    | none => .error s!"unbound variable '{x}'"
  | .int n => .ok ⟨.int, .const (.i n)⟩
  | .bool b => .ok ⟨.bool, .const (.b b)⟩
  | .unit => .ok ⟨.value, .const .unit⟩
  | .binop .add l r => do .ok ⟨.int, .binop .add (← checkTerm env .int l) (← checkTerm env .int r)⟩
  | .binop .sub l r => do .ok ⟨.int, .binop .sub (← checkTerm env .int l) (← checkTerm env .int r)⟩
  | .binop .mul l r => do .ok ⟨.int, .binop .mul (← checkTerm env .int l) (← checkTerm env .int r)⟩
  | .binop .div l r => do .ok ⟨.int, .binop .div (← checkTerm env .int l) (← checkTerm env .int r)⟩
  | .binop .mod l r => do .ok ⟨.int, .binop .mod (← checkTerm env .int l) (← checkTerm env .int r)⟩
  | .binop .eq l r => do
    let ⟨τ, l'⟩ ← inferTerm env l
    .ok ⟨.bool, .binop .eq l' (← checkTerm env τ r)⟩
  | .binop .lt l r => do .ok ⟨.bool, .binop .less (← checkTerm env .int l) (← checkTerm env .int r)⟩
  | .binop .le l r => do .ok ⟨.bool, .binop .ge (← checkTerm env .int r) (← checkTerm env .int l)⟩
  | .binop .gt l r => do .ok ⟨.bool, .binop .gt (← checkTerm env .int l) (← checkTerm env .int r)⟩
  | .binop .ge l r => do .ok ⟨.bool, .binop .ge (← checkTerm env .int l) (← checkTerm env .int r)⟩
  | .binop .and l r => do .ok ⟨.bool, .binop .eq (← checkTerm env .bool l) (← checkTerm env .bool r)⟩
  | .binop .or l r => do .ok ⟨.bool, .binop .eq (← checkTerm env .bool l) (← checkTerm env .bool r)⟩
  | .unop .neg e => do .ok ⟨.int, .unop .neg (← checkTerm env .int e)⟩
  | .unop .not e => do .ok ⟨.bool, .unop .not (← checkTerm env .bool e)⟩
  | .unop .tagof e => do .ok ⟨.int, .unop .tagOf (← checkTerm env .value e)⟩
  | .unop .arityof e => do .ok ⟨.int, .unop .arityOf (← checkTerm env .value e)⟩
  | .unop .payloadof e => do .ok ⟨.value, .unop .payloadOf (← checkTerm env .value e)⟩
  | .unop (.proj n) e => do
    let inner ← checkTerm env .value e
    .ok ⟨.value, .unop .vhead (vtailN (.unop .toValList inner) n)⟩
  | .unop (.inj tag arity) e => do
    .ok ⟨.value, .unop (.mkInj tag arity) (← checkTerm env .value e)⟩
  | .tuple es => do
    let vlist ← checkTermList env es
    .ok ⟨.value, .unop .ofValList vlist⟩
  | .ite c t e => do
    let c' ← checkTerm env .bool c
    let ⟨τ, t'⟩ ← inferTerm env t
    let e' ← checkTerm env τ e
    .ok ⟨τ, .ite c' t' e'⟩

def checkTerm (env : Env) (τ : Srt) : Spec.Term → M (Term τ)
  | .var x => match env.lookup x with
    | none => .error s!"unbound variable '{x}'"
    | some sort =>
      if h : sort = τ then .ok (h ▸ .var sort x)
      else .error s!"variable '{x}' has sort {repr sort}, expected {repr τ}"
  | .int n => match τ with
    | .int => .ok (.const (.i n))
    | .value => .ok (.unop .ofInt (.const (.i n)))
    | .bool => .error "integer literal cannot be bool"
    | .vallist => .error "integer literal cannot be vallist"
  | .bool b => match τ with
    | .bool => .ok (.const (.b b))
    | .value => .ok (.unop .ofBool (.const (.b b)))
    | .int => .error "boolean literal cannot be int"
    | .vallist => .error "boolean literal cannot be vallist"
  | .unit => match τ with
    | .value => .ok (.const .unit)
    | _ => .error s!"unit literal has sort value, expected {repr τ}"
  | .binop op l r => do castTerm τ s!"{repr op}" (← inferTerm env (.binop op l r))
  | .unop op e => do castTerm τ s!"{repr op}" (← inferTerm env (.unop op e))
  | .tuple es => match τ with
    | .value => do
      let vlist ← checkTermList env es
      .ok (.unop .ofValList vlist)
    | _ => .error s!"tuple has sort value, expected {repr τ}"
  | .ite c t e => do
    let c' ← checkTerm env .bool c
    .ok (.ite c' (← checkTerm env τ t) (← checkTerm env τ e))

def checkTermList (env : Env) : List Spec.Term → M (Term .vallist)
  | [] => .ok (.const .vnil)
  | e :: es => do
    let v ← checkTerm env .value e
    let vs ← checkTermList env es
    .ok (.binop .vcons v vs)
end

-- ---------------------------------------------------------------------------
-- Formulas
-- ---------------------------------------------------------------------------

def translateFormula (env : Env) : Spec.Term → M Formula
  | .binop .eq l r => do
    let ⟨τ, l'⟩ ← inferTerm env l
    .ok (.eq τ l' (← checkTerm env τ r))
  | .binop .lt l r => do
    .ok (.binpred .lt (← checkTerm env .int l) (← checkTerm env .int r))
  | .binop .le l r => do
    .ok (.binpred .le (← checkTerm env .int l) (← checkTerm env .int r))
  | .binop .gt l r => do
    .ok (.binpred .lt (← checkTerm env .int r) (← checkTerm env .int l))
  | .binop .ge l r => do
    .ok (.binpred .le (← checkTerm env .int r) (← checkTerm env .int l))
  | .binop .and l r => do
    .ok (.and (← translateFormula env l) (← translateFormula env r))
  | .binop .or l r => do
    .ok (.or (← translateFormula env l) (← translateFormula env r))
  | .unop .not e => do
    .ok (.not (← translateFormula env e))
  | e => .error s!"cannot convert to formula: {repr e}"

-- ---------------------------------------------------------------------------
-- Predicates
-- ---------------------------------------------------------------------------

def translatePred (env : Env) : Spec.Pred → M (Σ t, Atom t)
  | .isint e => do .ok ⟨.int, .isint (← checkTerm env .value e)⟩
  | .isbool e => do .ok ⟨.bool, .isbool (← checkTerm env .value e)⟩
  | .isinj tag arity e => do
    .ok ⟨.value, .isinj tag arity (← checkTerm env .value e)⟩

-- ---------------------------------------------------------------------------
-- Assertions
-- ---------------------------------------------------------------------------

def translateAssert (env : Env) (inner : Env → α → M β) : Spec.Assert α → M (Assertion β)
  | .ret a => do .ok (.ret (← inner env a))
  | .assert cond rest => do
    let φ ← translateFormula env cond
    .ok (.assert φ (← translateAssert env inner rest))
  | .let_ x t rest => do
    let ⟨τ, t'⟩ ← inferTerm env t
    let v : Var := ⟨x, τ⟩
    .ok (.let_ v t' (← translateAssert ((x, τ) :: env) inner rest))
  | .bind pred x rest => do
    let ⟨τ, atom⟩ ← translatePred env pred
    let v : Var := ⟨x, τ⟩
    .ok (.pred v atom (← translateAssert ((x, τ) :: env) inner rest))
  | .ite cond thn els => do
    let φ ← translateFormula env cond
    .ok (.ite φ (← translateAssert env inner thn) (← translateAssert env inner els))

-- ---------------------------------------------------------------------------
-- Top-level: Body → SpecPredicate
-- ---------------------------------------------------------------------------

def translatePost (env : Env) : Spec.Post → M (Assertion Unit) :=
  translateAssert env (fun _ () => .ok ())

def translatePre (env : Env) : Spec.Pre → M PredTrans :=
  translateAssert env fun env (name, post) => do
    let post' ← translatePost ((name, .value) :: env) post
    .ok (name, post')

def translate (body : Spec.Body) : M SpecPredicate :=
  let (names, pre) := body
  let env : Env := names.map (·, .value)
  do
    let pt ← translatePre env pre
    .ok (names, pt)

end SpecTranslation
