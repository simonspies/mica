-- SUMMARY: The failure elaboration can raise and the monad carrying it.
import Mica.SourceTinyML.Types
import Mica.SourceTinyML.Typed
import Mica.SourceTinyML.Printer
import Mica.Base.Except

namespace Typed

open TinyML

/-! ## Type errors -/

inductive TypeError where
  | undefinedVar (name : TinyML.Var)
  | duplicateType (name : TypeName)
  | operatorMismatch (op : BinOp) (lhs rhs : Typ)
  | unaryMismatch (op : UnOp) (arg : Typ)
  | notAFunction (ty : Typ)
  | arityMismatch (expected actual : Nat)
  | typeMismatch (expected actual : Typ)
  | notASum (ty : Typ)
  | notARef (ty : Typ)
  | notAnArray (ty : Typ)
  | missingReturnType
  | subsumptionFailure (sub super : Typ)
  | spec (msg : String)
  | unknownPrimitive (name : String)
  | cannotInstantiate (name : String) (msg : String)
  | unboundTypeVar (name : TyVar)
  deriving Repr, Inhabited, DecidableEq

instance : ToString TypeError where
  toString
    | .undefinedVar name => s!"undefined variable: {name}"
    | .duplicateType name => s!"duplicate type: {name}"
    | .operatorMismatch op lhs rhs =>
        s!"operator {repr op} cannot be applied to {lhs.print} and {rhs.print}"
    | .unaryMismatch op arg =>
        s!"operator {repr op} cannot be applied to {arg.print}"
    | .notAFunction ty => s!"not a function: {ty.print}"
    | .arityMismatch expected actual =>
        s!"arity mismatch: expected {expected}, got {actual}"
    | .typeMismatch expected actual =>
        s!"type mismatch: expected {expected.print}, got {actual.print}"
    | .notASum ty => s!"not a sum type: {ty.print}"
    | .notARef ty => s!"not a ref type: {ty.print}"
    | .notAnArray ty => s!"not an array type: {ty.print}"
    | .missingReturnType => "missing return type"
    | .subsumptionFailure sub super =>
        s!"subsumption failed: {sub.print} is not a subtype of {super.print}"
    | .spec msg => s!"specification error: {msg}"
    | .unknownPrimitive name => s!"unknown primitive: {name}"
    | .cannotInstantiate name msg =>
        s!"cannot instantiate primitive {name}: {msg}"
    | .unboundTypeVar name => s!"unbound type variable '{name}"

/-! ## The typing monad

Typing has exactly one effect of its own — failure. The state is there only to
carry whatever effect the ambient environment's callbacks need, and typing never
reads or writes it: it merely threads it through. -/

abbrev TypeM (σ : Type) := StateT σ (Except TypeError)

/-- Fail with a type error, discarding the state. -/
def TypeM.error (e : TypeError) : TypeM σ α := fun _ => .error e

@[simp] theorem TypeM.error_apply (e : TypeError) (s : σ) :
    (TypeM.error e : TypeM σ α) s = .error e := rfl

@[simp] theorem TypeM.pure_apply (a : α) (s : σ) :
    (pure a : TypeM σ α) s = .ok (a, s) := rfl

@[simp] theorem TypeM.error_bind (e : TypeError) (g : α → TypeM σ β) :
    (TypeM.error e >>= g : TypeM σ β) = TypeM.error e := by
  funext s; rfl

/-- Run a pure `Except` computation in `TypeM`, leaving the state untouched. -/
def TypeM.ofExcept : Except TypeError α → TypeM σ α
  | .ok a => fun s => .ok (a, s)
  | .error e => fun _ => .error e

@[simp] theorem TypeM.ofExcept_pure (a : α) :
    (TypeM.ofExcept (.ok a) : TypeM σ α) = pure a := rfl

@[simp] theorem TypeM.ofExcept_error (e : TypeError) :
    (TypeM.ofExcept (.error e) : TypeM σ α) = TypeM.error e := rfl

@[simp] theorem TypeM.ofExcept_ok {r : Except TypeError α} {s s' : σ} {a : α} :
    (TypeM.ofExcept r : TypeM σ α) s = .ok (a, s') ↔ r = .ok a ∧ s' = s := by
  cases r <;> simp [TypeM.ofExcept, eq_comm]

end Typed
