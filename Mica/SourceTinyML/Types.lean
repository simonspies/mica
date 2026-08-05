-- SUMMARY: TinyML types over a parameter of type variables, their substitution laws, type schemes, and type declarations.
import Mica.TinyML.Common
import Mica.SourceTinyML.Assertions

namespace TinyML

abbrev TyVar := String

/-- Canonical algebraic types supplied by Mica rather than declared by a
program. Their identity is distinct from user-written type names. -/
inductive Predef where
  | list
  | option
  deriving Repr, Inhabited, DecidableEq, BEq

/-- The identity of a recursive named type. Predefined identities unfold to
their canonical declarations independently of the user type environment. -/
inductive TypeName where
  | user (name : String)
  | predef (type : Predef)
  deriving Repr, Inhabited, DecidableEq, BEq

/-- The surface spelling of a named type. -/
def TypeName.print : TypeName → String
  | .user name => name
  | .predef .list => "list"
  | .predef .option => "option"

instance : ToString TypeName := ⟨TypeName.print⟩

/-- Primitive, non-structural TinyML types. -/
inductive PrimitiveType where
  | unit
  | bool
  | int
  | char
  | string
  | float
  deriving Repr, DecidableEq

/-- Decidable equality for primitive types. -/
protected def PrimitiveType.decEq (p q : PrimitiveType) : Decidable (p = q) :=
  inferInstance

/-- Pretty-print a primitive type. -/
def PrimitiveType.print : PrimitiveType → String
  | .unit => "unit"
  | .bool => "bool"
  | .int => "int"
  | .char => "char"
  | .string => "string"
  | .float => "float"

/-- Type primitive binary operators before lifting the result to `Typ`. -/
def PrimitiveType.binOpTypeOf : BinOp → PrimitiveType → PrimitiveType → Option PrimitiveType
  | .add,  .int,  .int  => some .int
  | .sub,  .int,  .int  => some .int
  | .mul,  .int,  .int  => some .int
  | .div,  .int,  .int  => some .int
  | .mod,  .int,  .int  => some .int
  | .eq,   .int,  .int  => some .bool
  | .lt,   .int,  .int  => some .bool
  | .le,   .int,  .int  => some .bool
  | .gt,   .int,  .int  => some .bool
  | .ge,   .int,  .int  => some .bool
  | .and,  .bool, .bool => some .bool
  | .or,   .bool, .bool => some .bool
  | _, _, _             => none

/-- Type primitive unary operators before lifting the result to `Typ`. -/
def PrimitiveType.unOpTypeOf : UnOp → PrimitiveType → Option PrimitiveType
  | .neg, .int  => some .int
  | .not, .bool => some .bool
  | _, _        => none

/-- Arithmetic binary operators require integer primitive inputs and produce integer. -/
theorem PrimitiveType.binOpTypeOf_arith {op : BinOp} {p1 p2 p : PrimitiveType}
    (hop : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .div ∨ op = .mod)
    (hty : PrimitiveType.binOpTypeOf op p1 p2 = some p) :
    p1 = .int ∧ p2 = .int ∧ p = .int := by
  rcases hop with rfl | rfl | rfl | rfl | rfl
  all_goals
    cases p1 <;> cases p2 <;> simp [PrimitiveType.binOpTypeOf] at hty
    subst hty
    simp

/-- Integer comparison binary operators require integer primitive inputs and produce Boolean. -/
theorem PrimitiveType.binOpTypeOf_compare {op : BinOp} {p1 p2 p : PrimitiveType}
    (hop : op = .eq ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (hty : PrimitiveType.binOpTypeOf op p1 p2 = some p) :
    p1 = .int ∧ p2 = .int ∧ p = .bool := by
  rcases hop with rfl | rfl | rfl | rfl | rfl
  all_goals
    cases p1 <;> cases p2 <;> simp [PrimitiveType.binOpTypeOf] at hty
    subst hty
    simp

/-- Boolean binary operators require Boolean primitive inputs and produce Boolean. -/
theorem PrimitiveType.binOpTypeOf_bool {op : BinOp} {p1 p2 p : PrimitiveType}
    (hop : op = .and ∨ op = .or)
    (hty : PrimitiveType.binOpTypeOf op p1 p2 = some p) :
    p1 = .bool ∧ p2 = .bool ∧ p = .bool := by
  rcases hop with rfl | rfl
  all_goals
    cases p1 <;> cases p2 <;> simp [PrimitiveType.binOpTypeOf] at hty
    subst hty
    simp

/-- Integer unary operators require an integer primitive input and produce integer. -/
theorem PrimitiveType.unOpTypeOf_int {op : UnOp} {p p' : PrimitiveType}
    (hop : op = .neg)
    (hty : PrimitiveType.unOpTypeOf op p = some p') :
    p = .int ∧ p' = .int := by
  subst hop
  cases p <;> simp [PrimitiveType.unOpTypeOf] at hty
  subst hty
  simp

/-- Boolean unary operators require a Boolean primitive input and produce Boolean. -/
theorem PrimitiveType.unOpTypeOf_bool {op : UnOp} {p p' : PrimitiveType}
    (hop : op = .not)
    (hty : PrimitiveType.unOpTypeOf op p = some p') :
    p = .bool ∧ p' = .bool := by
  subst hop
  cases p <;> simp [PrimitiveType.unOpTypeOf] at hty
  subst hty
  simp

namespace Typ

/-- TinyML types, parameterized by the variables a `tvar` node may carry. Only
one instantiation is used here: `Typ`, whose `V` is a source type variable.
Type inference adds a second, which admits its metavariables as well. -/
inductive WithTypeVars (V : Type) where
  | prim (p : PrimitiveType)
  | sum (ts : List (WithTypeVars V))
  /-- A function type. `spec` is the specification the function was verified
  against, if it has one; only specified functions are inhabited values. -/
  | arrow (args : List (WithTypeVars V)) (ret : WithTypeVars V)
      (spec : Option (Spec (WithTypeVars V)))
  | ref (t : WithTypeVars V)
  /-- Shared array whose elements have type `t`. -/
  | array (t : WithTypeVars V)
  /-- An owned mutable array. Its contents are tracked by an immutable vector
  snapshot in the ambient spatial context. -/
  | ownedArray (t : WithTypeVars V)
  /-- Immutable vector whose elements have type `t`. Unlike `array`, a vector is
  a pure value: its contents live in the value itself, not in the heap. -/
  | vec (t : WithTypeVars V)
  /-- An owned reference. Its value interpretation records only that the value
  is a location; points-to ownership lives in the ambient spatial context. -/
  | owned (t : WithTypeVars V)
  | empty   -- bottom type (uninhabited)
  | value   -- top type (all runtime values)
  | tuple (ts : List (WithTypeVars V))
  | tvar (v : V)
  | named (T : TypeName) (args : List (WithTypeVars V))
  deriving Repr

namespace WithTypeVars

/-- Abbreviation for the unit primitive type. -/
@[simp] def unit : WithTypeVars V := .prim .unit
/-- Abbreviation for the Boolean primitive type. -/
@[simp] def bool : WithTypeVars V := .prim .bool
/-- Abbreviation for the integer primitive type. -/
@[simp] def int : WithTypeVars V := .prim .int
/-- Abbreviation for the character primitive type. -/
@[simp] def char : WithTypeVars V := .prim .char
/-- Abbreviation for the string primitive type. -/
@[simp] def string : WithTypeVars V := .prim .string
/-- Abbreviation for the float primitive type. -/
@[simp] def float : WithTypeVars V := .prim .float
/-- A canonical predefined type application. -/
@[simp] def predef (p : Predef) (args : List (WithTypeVars V)) : WithTypeVars V :=
  .named (.predef p) args
/-- The canonical list type. -/
@[simp] def list (elem : WithTypeVars V) : WithTypeVars V := .predef .list [elem]
/-- The canonical option type. -/
@[simp] def option (elem : WithTypeVars V) : WithTypeVars V := .predef .option [elem]

end WithTypeVars

-- Both spellings are wanted: `.prim` resolves in the inductive's namespace,
-- `Typ.prim` in the one named after the type it usually builds.
export WithTypeVars (prim sum arrow ref array ownedArray vec owned empty value
  tuple tvar named unit bool int char string float predef list option)

end Typ

/-- The type language the verifier works in. A `tvar` node stands for a type
variable a polymorphic declaration quantifies over; the logical relation
interprets it by the world's assignment. -/
abbrev Typ := Typ.WithTypeVars TyVar

/-- A type every variable of which is implicitly quantified, as an intrinsic's
registry entry is: a use site instantiates all of them at once. The same
language as `Typ` — a scheme with an explicit quantifier is `Scheme` — so the
name records only that intent. -/
abbrev SchemaTyp := Typ.WithTypeVars TyVar

def Typ.primDecEq {V : Type} (p q : PrimitiveType) :
    Decidable (Typ.WithTypeVars.prim (V := V) p = .prim q) :=
  match PrimitiveType.decEq p q with
  | isTrue h => isTrue (by subst h; rfl)
  | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)

mutual

def Typ.decEq {V : Type} [DecidableEq V] :
    (a b : Typ.WithTypeVars V) → Decidable (a = b)
  | .prim p, .prim q => Typ.primDecEq p q
  | .empty, .empty | .value, .value => isTrue rfl
  | .sum ss, .sum ts => match Typ.decEqList ss ts with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .arrow ss s sp, .arrow ts t sp' =>
    match Typ.decEqList ss ts, Typ.decEq s t, Typ.decEqSpec? sp sp' with
    | isTrue h1, isTrue h2, isTrue h3 => isTrue (by subst h1; subst h2; subst h3; rfl)
    | isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
    | _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
    | _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .ref s, .ref t => match Typ.decEq s t with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .array s, .array t => match Typ.decEq s t with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .ownedArray s, .ownedArray t => match Typ.decEq s t with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .vec s, .vec t => match Typ.decEq s t with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .owned s, .owned t => match Typ.decEq s t with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .tuple ss, .tuple ts => match Typ.decEqList ss ts with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .tvar v, .tvar w => match (inferInstance : DecidableEq V) v w with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .named T args, .named U params =>
    match (inferInstance : DecidableEq TypeName) T U, Typ.decEqList args params with
    | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
    | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
    | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .ownedArray .., .prim _ | .ownedArray .., .sum _ | .ownedArray .., .arrow ..
  | .ownedArray .., .ref _ | .ownedArray .., .array _ | .ownedArray .., .vec _
  | .ownedArray .., .owned _ | .ownedArray .., .empty | .ownedArray .., .value
  | .ownedArray .., .tuple _ | .ownedArray .., .tvar _ | .ownedArray .., .named _ _
  | .prim _, .ownedArray .. | .sum _, .ownedArray .. | .arrow .., .ownedArray ..
  | .ref _, .ownedArray .. | .array _, .ownedArray .. | .vec _, .ownedArray ..
  | .owned _, .ownedArray .. | .empty, .ownedArray .. | .value, .ownedArray ..
  | .tuple _, .ownedArray .. | .tvar _, .ownedArray .. | .named _ _, .ownedArray .. =>
      isFalse (by intro h; cases h)
  | .prim _, .sum .. | .prim _, .arrow ..
  | .prim _, .ref .. | .prim _, .array .. | .prim _, .owned .. | .prim _, .empty | .prim _, .value | .prim _, .tuple ..
  | .prim _, .tvar .. | .prim _, .named .. | .prim _, .vec ..
  | .sum .., .prim _
  | .sum .., .arrow .. | .sum .., .ref .. | .sum .., .array .. | .sum .., .owned .. | .sum .., .empty
  | .sum .., .value | .sum .., .tuple .. | .sum .., .tvar .. | .sum .., .named .. | .sum .., .vec ..
  | .arrow .., .prim _
  | .arrow .., .sum .. | .arrow .., .ref .. | .arrow .., .array .. | .arrow .., .owned .. | .arrow .., .empty
  | .arrow .., .value | .arrow .., .tuple .. | .arrow .., .tvar .. | .arrow .., .named .. | .arrow .., .vec ..
  | .ref .., .prim _
  | .ref .., .sum .. | .ref .., .arrow .. | .ref .., .array .. | .ref .., .owned .. | .ref .., .empty
  | .ref .., .value | .ref .., .tuple .. | .ref .., .tvar .. | .ref .., .named .. | .ref .., .vec ..
  | .array .., .prim _
  | .array .., .sum .. | .array .., .arrow .. | .array .., .ref .. | .array .., .owned .. | .array .., .empty
  | .array .., .value | .array .., .tuple .. | .array .., .tvar .. | .array .., .named .. | .array .., .vec ..
  | .vec .., .prim _
  | .vec .., .sum .. | .vec .., .arrow .. | .vec .., .ref .. | .vec .., .array .. | .vec .., .owned ..
  | .vec .., .empty | .vec .., .value | .vec .., .tuple .. | .vec .., .tvar .. | .vec .., .named ..
  | .owned .., .prim _
  | .owned .., .sum .. | .owned .., .arrow .. | .owned .., .ref .. | .owned .., .array .. | .owned .., .empty
  | .owned .., .value | .owned .., .tuple .. | .owned .., .tvar .. | .owned .., .named .. | .owned .., .vec ..
  | .empty, .prim _ | .empty, .sum ..
  | .empty, .arrow .. | .empty, .ref .. | .empty, .array .. | .empty, .owned .. | .empty, .value | .empty, .tuple ..
  | .empty, .tvar .. | .empty, .named .. | .empty, .vec ..
  | .value, .prim _ | .value, .sum ..
  | .value, .arrow .. | .value, .ref .. | .value, .array .. | .value, .owned .. | .value, .empty | .value, .tuple ..
  | .value, .tvar .. | .value, .named .. | .value, .vec ..
  | .tuple .., .prim _
  | .tuple .., .sum .. | .tuple .., .arrow .. | .tuple .., .ref .. | .tuple .., .owned ..
  | .tuple .., .array .. | .tuple .., .vec ..
  | .tuple .., .empty | .tuple .., .value | .tuple .., .tvar .. | .tuple .., .named ..
  | .tvar .., .prim _ | .tvar .., .sum ..
  | .tvar .., .arrow .. | .tvar .., .ref .. | .tvar .., .owned .. | .tvar .., .empty
  | .tvar .., .array .. | .tvar .., .vec ..
  | .tvar .., .value | .tvar .., .tuple .. | .tvar .., .named ..
  | .named .., .prim _ | .named .., .sum ..
  | .named .., .arrow .. | .named .., .ref .. | .named .., .owned .. | .named .., .empty
  | .named .., .array .. | .named .., .vec ..
  | .named .., .value | .named .., .tuple .. | .named .., .tvar .. => isFalse (by intro h; cases h)
termination_by structural a _ => a

/-- Equality of type lists, mutually with `Typ.decEq`. -/
def Typ.decEqList {V : Type} [DecidableEq V] :
    (as bs : List (Typ.WithTypeVars V)) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
  | a :: as, b :: bs => match Typ.decEq a b, Typ.decEqList as bs with
    | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
    | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
    | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)

-- The remaining members of the block decide equality of the specification a
-- function type carries. They cannot go through the generic instances in
-- `Mica/SourceTinyML/Assertions.lean`: those take `DecidableEq Typ` as an instance
-- argument, which is what this block is defining.
termination_by structural a _ => a

/-- Equality of atoms over TinyML types, mutually with `Typ.decEq`. -/
def Typ.decEqAtom {V : Type} [DecidableEq V] {s : Srt} :
    (a b : Atom (Typ.WithTypeVars V) s) → Decidable (a = b)
  | .isint t, .isint u | .isbool t, .isbool u =>
    match _root_.decEq t u with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .isinj tag arity t, .isinj tag' arity' u =>
    match _root_.decEq tag tag', _root_.decEq arity arity', _root_.decEq t u with
    | isTrue h1, isTrue h2, isTrue h3 => isTrue (by subst h1; subst h2; subst h3; rfl)
    | isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
    | _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
    | _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .own t x, .own u y | .arr t x, .arr u y =>
    match _root_.decEq t u, Typ.decEq x y with
    | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
    | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
    | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .rel n t, .rel m u =>
    match _root_.decEq n m, _root_.decEq t u with
    | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
    | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
    | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .isinj .., .own .. | .isinj .., .arr .. | .isinj .., .rel ..
  | .own .., .isinj .. | .own .., .arr .. | .own .., .rel ..
  | .arr .., .isinj .. | .arr .., .own .. | .arr .., .rel ..
  | .rel .., .isinj .. | .rel .., .own .. | .rel .., .arr .. =>
    isFalse (by intro h; cases h)
termination_by structural a _ => a

/-- Equality of postcondition assertions, mutually with `Typ.decEq`. -/
def Typ.decEqPost {V : Type} [DecidableEq V] :
    (a b : Assertion (Typ.WithTypeVars V) Unit) → Decidable (a = b)
  | .ret (), .ret () => isTrue rfl
  | .assert φ k, .assert ψ k' =>
    match _root_.decEq φ ψ, Typ.decEqPost k k' with
    | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
    | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
    | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .let_ v t k, .let_ w u k' =>
    match _root_.decEq v w with
    | isTrue hv => by
        subst hv
        exact match _root_.decEq t u, Typ.decEqPost k k' with
          | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
          | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
          | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .pred v p k, .pred w q k' =>
    match _root_.decEq v w with
    | isTrue hv => by
        subst hv
        exact match Typ.decEqAtom p q, Typ.decEqPost k k' with
          | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
          | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
          | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .ite φ kt ke, .ite ψ kt' ke' =>
    match _root_.decEq φ ψ, Typ.decEqPost kt kt', Typ.decEqPost ke ke' with
    | isTrue h1, isTrue h2, isTrue h3 => isTrue (by subst h1; subst h2; subst h3; rfl)
    | isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
    | _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
    | _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .ret _, .assert .. | .ret _, .let_ .. | .ret _, .pred .. | .ret _, .ite ..
  | .assert .., .ret _ | .assert .., .let_ .. | .assert .., .pred .. | .assert .., .ite ..
  | .let_ .., .ret _ | .let_ .., .assert .. | .let_ .., .pred .. | .let_ .., .ite ..
  | .pred .., .ret _ | .pred .., .assert .. | .pred .., .let_ .. | .pred .., .ite ..
  | .ite .., .ret _ | .ite .., .assert .. | .ite .., .let_ .. | .ite .., .pred .. =>
    isFalse (by intro h; cases h)
termination_by structural a _ => a

/-- Equality of predicate transformers, mutually with `Typ.decEq`. -/
def Typ.decEqPredTrans {V : Type} [DecidableEq V] :
    (a b : Assertion (Typ.WithTypeVars V) (Post (Typ.WithTypeVars V))) → Decidable (a = b)
  | .ret p, .ret q =>
    match _root_.decEq p.name q.name, Typ.decEqPost p.body q.body with
    | isTrue h1, isTrue h2 => isTrue (by cases p; cases q; simp_all)
    | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
    | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .assert φ k, .assert ψ k' =>
    match _root_.decEq φ ψ, Typ.decEqPredTrans k k' with
    | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
    | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
    | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .let_ v t k, .let_ w u k' =>
    match _root_.decEq v w with
    | isTrue hv => by
        subst hv
        exact match _root_.decEq t u, Typ.decEqPredTrans k k' with
          | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
          | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
          | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .pred v p k, .pred w q k' =>
    match _root_.decEq v w with
    | isTrue hv => by
        subst hv
        exact match Typ.decEqAtom p q, Typ.decEqPredTrans k k' with
          | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
          | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
          | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .ite φ kt ke, .ite ψ kt' ke' =>
    match _root_.decEq φ ψ, Typ.decEqPredTrans kt kt', Typ.decEqPredTrans ke ke' with
    | isTrue h1, isTrue h2, isTrue h3 => isTrue (by subst h1; subst h2; subst h3; rfl)
    | isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
    | _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
    | _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .ret _, .assert .. | .ret _, .let_ .. | .ret _, .pred .. | .ret _, .ite ..
  | .assert .., .ret _ | .assert .., .let_ .. | .assert .., .pred .. | .assert .., .ite ..
  | .let_ .., .ret _ | .let_ .., .assert .. | .let_ .., .pred .. | .let_ .., .ite ..
  | .pred .., .ret _ | .pred .., .assert .. | .pred .., .let_ .. | .pred .., .ite ..
  | .ite .., .ret _ | .ite .., .assert .. | .ite .., .let_ .. | .ite .., .pred .. =>
    isFalse (by intro h; cases h)
termination_by structural a _ => a

/-- Equality of specifications, mutually with `Typ.decEq`. -/
def Typ.decEqSpec {V : Type} [DecidableEq V] :
    (a b : Spec (Typ.WithTypeVars V)) → Decidable (a = b)
  | ⟨as, p⟩, ⟨bs, q⟩ =>
    match _root_.decEq as bs, Typ.decEqPredTrans p q with
    | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
    | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
    | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
termination_by structural a _ => a

/-- Equality of optional specifications, mutually with `Typ.decEq`. -/
def Typ.decEqSpec? {V : Type} [DecidableEq V] :
    (a b : Option (Spec (Typ.WithTypeVars V))) → Decidable (a = b)
  | none, none => isTrue rfl
  | none, some _ | some _, none => isFalse (by intro h; cases h)
  | some s, some t =>
    match Typ.decEqSpec s t with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
termination_by structural a _ => a

end

instance {V : Type} [DecidableEq V] : DecidableEq (Typ.WithTypeVars V) := Typ.decEq

instance {V : Type} [DecidableEq V] : BEq (Typ.WithTypeVars V) := ⟨fun a b => decide (a = b)⟩
instance {V : Type} [DecidableEq V] : LawfulBEq (Typ.WithTypeVars V) where
  eq_of_beq h := of_decide_eq_true h
  rfl := by simp [BEq.beq]

/-! ### Substitution and closedness

Both descend into an arrow's specification: the `own` and `arr` atoms of a
specification mention types, so a type variable can occur inside one. Each
traversal is spelled out over the specification syntax the same way `Typ.decEq`
is, since `Typ` nests those types and a single generic map over them would not
be structurally recursive.

Substitution also changes the variables a type is written over, so it is what
moves a type between the instantiations of `Typ.WithTypeVars`: inference embeds
a `Typ` by sending every variable to its rigid counterpart, and closes back by
sending every solved metavariable to its solution. -/

/-- The type with a top-level arrow's specification dropped; the identity on
everything else. Used where only the signature of an arrow matters. -/
def Typ.unspec : Typ.WithTypeVars V → Typ.WithTypeVars V
  | .arrow args ret _ => .arrow args ret none
  | t => t

mutual

/-- Substitution over a type, replacing each type variable by `σ`. -/
def Typ.subst (σ : V → Typ.WithTypeVars W) : Typ.WithTypeVars V → Typ.WithTypeVars W
  | .prim p => .prim p
  | .sum ts => .sum (Typ.substList σ ts)
  | .arrow args ret spec =>
    .arrow (Typ.substList σ args) (Typ.subst σ ret) (Typ.substSpec? σ spec)
  | .ref t => .ref (Typ.subst σ t)
  | .array t => .array (Typ.subst σ t)
  | .ownedArray t => .ownedArray (Typ.subst σ t)
  | .vec t => .vec (Typ.subst σ t)
  | .owned t => .owned (Typ.subst σ t)
  | .empty => .empty
  | .value => .value
  | .tuple ts => .tuple (Typ.substList σ ts)
  | .tvar v => σ v
  | .named T args => .named T (Typ.substList σ args)
termination_by structural t => t

/-- Substitution over a list of types, mutually with `Typ.subst`. -/
def Typ.substList (σ : V → Typ.WithTypeVars W) :
    List (Typ.WithTypeVars V) → List (Typ.WithTypeVars W)
  | [] => []
  | t :: ts => Typ.subst σ t :: Typ.substList σ ts
termination_by structural ts => ts

/-- Substitution in the types an atom mentions, mutually with `Typ.subst`. -/
def Typ.substAtom (σ : V → Typ.WithTypeVars W) :
    {s : Srt} → Atom (Typ.WithTypeVars V) s → Atom (Typ.WithTypeVars W) s
  | _, .isint t => .isint t
  | _, .isbool t => .isbool t
  | _, .isinj tag arity t => .isinj tag arity t
  | _, .own t ty => .own t (Typ.subst σ ty)
  | _, .arr t ty => .arr t (Typ.subst σ ty)
  | _, .rel n t => .rel n t
termination_by structural _ a => a

/-- Substitution in a postcondition assertion, mutually with `Typ.subst`. -/
def Typ.substPost (σ : V → Typ.WithTypeVars W) :
    Assertion (Typ.WithTypeVars V) Unit → Assertion (Typ.WithTypeVars W) Unit
  | .ret () => .ret ()
  | .assert φ k => .assert φ (Typ.substPost σ k)
  | .let_ v t k => .let_ v t (Typ.substPost σ k)
  | .pred v p k => .pred v (Typ.substAtom σ p) (Typ.substPost σ k)
  | .ite φ kt ke => .ite φ (Typ.substPost σ kt) (Typ.substPost σ ke)
termination_by structural a => a

/-- Substitution in a predicate transformer, mutually with `Typ.subst`. -/
def Typ.substPredTrans (σ : V → Typ.WithTypeVars W) :
    Assertion (Typ.WithTypeVars V) (Post (Typ.WithTypeVars V)) →
      Assertion (Typ.WithTypeVars W) (Post (Typ.WithTypeVars W))
  | .ret p => .ret ⟨p.name, Typ.substPost σ p.body⟩
  | .assert φ k => .assert φ (Typ.substPredTrans σ k)
  | .let_ v t k => .let_ v t (Typ.substPredTrans σ k)
  | .pred v p k => .pred v (Typ.substAtom σ p) (Typ.substPredTrans σ k)
  | .ite φ kt ke => .ite φ (Typ.substPredTrans σ kt) (Typ.substPredTrans σ ke)
termination_by structural a => a

/-- Substitution in a specification, mutually with `Typ.subst`. -/
def Typ.substSpec (σ : V → Typ.WithTypeVars W) :
    Spec (Typ.WithTypeVars V) → Spec (Typ.WithTypeVars W)
  | s => { args := s.args, pred := Typ.substPredTrans σ s.pred }
termination_by structural s => s

/-- Substitution in an optional specification, mutually with `Typ.subst`. -/
def Typ.substSpec? (σ : V → Typ.WithTypeVars W) :
    Option (Spec (Typ.WithTypeVars V)) → Option (Spec (Typ.WithTypeVars W))
  | none => none
  | some s => some (Typ.substSpec σ s)
termination_by structural s => s

end

mutual

/-- Substitution that may reject a variable, used where a substitution is only
partial: instantiating a scheme at a solved assignment, say, which fails on a
variable the assignment does not cover. -/
def Typ.substM (σ : V → Except ε (Typ.WithTypeVars W)) :
    Typ.WithTypeVars V → Except ε (Typ.WithTypeVars W)
  | .prim p => pure (.prim p)
  | .sum ts => do pure (.sum (← Typ.substListM σ ts))
  | .arrow args ret spec => do
      pure (.arrow (← Typ.substListM σ args) (← Typ.substM σ ret)
        (← Typ.substSpecM? σ spec))
  | .ref t => do pure (.ref (← Typ.substM σ t))
  | .array t => do pure (.array (← Typ.substM σ t))
  | .ownedArray t => do pure (.ownedArray (← Typ.substM σ t))
  | .vec t => do pure (.vec (← Typ.substM σ t))
  | .owned t => do pure (.owned (← Typ.substM σ t))
  | .empty => pure .empty
  | .value => pure .value
  | .tuple ts => do pure (.tuple (← Typ.substListM σ ts))
  | .tvar v => σ v
  | .named T args => do pure (.named T (← Typ.substListM σ args))
termination_by structural t => t

/-- Rejecting substitution over a list of types, mutually with `Typ.substM`. -/
def Typ.substListM (σ : V → Except ε (Typ.WithTypeVars W)) :
    List (Typ.WithTypeVars V) → Except ε (List (Typ.WithTypeVars W))
  | [] => pure []
  | t :: ts => do pure ((← Typ.substM σ t) :: (← Typ.substListM σ ts))
termination_by structural ts => ts

/-- Rejecting substitution in an atom's types, mutually with `Typ.substM`. -/
def Typ.substAtomM (σ : V → Except ε (Typ.WithTypeVars W)) :
    {s : Srt} → Atom (Typ.WithTypeVars V) s → Except ε (Atom (Typ.WithTypeVars W) s)
  | _, .isint t => pure (.isint t)
  | _, .isbool t => pure (.isbool t)
  | _, .isinj tag arity t => pure (.isinj tag arity t)
  | _, .own t ty => do pure (.own t (← Typ.substM σ ty))
  | _, .arr t ty => do pure (.arr t (← Typ.substM σ ty))
  | _, .rel n t => pure (.rel n t)
termination_by structural _ a => a

/-- Rejecting substitution in a postcondition, mutually with `Typ.substM`. -/
def Typ.substPostM (σ : V → Except ε (Typ.WithTypeVars W)) :
    Assertion (Typ.WithTypeVars V) Unit → Except ε (Assertion (Typ.WithTypeVars W) Unit)
  | .ret () => pure (.ret ())
  | .assert φ k => do pure (.assert φ (← Typ.substPostM σ k))
  | .let_ v t k => do pure (.let_ v t (← Typ.substPostM σ k))
  | .pred v p k => do
      pure (.pred v (← Typ.substAtomM σ p) (← Typ.substPostM σ k))
  | .ite φ kt ke => do
      pure (.ite φ (← Typ.substPostM σ kt) (← Typ.substPostM σ ke))
termination_by structural a => a

/-- Rejecting substitution in a predicate transformer, mutually with
`Typ.substM`. -/
def Typ.substPredTransM (σ : V → Except ε (Typ.WithTypeVars W)) :
    Assertion (Typ.WithTypeVars V) (Post (Typ.WithTypeVars V)) →
      Except ε (Assertion (Typ.WithTypeVars W) (Post (Typ.WithTypeVars W)))
  | .ret p => do pure (.ret ⟨p.name, ← Typ.substPostM σ p.body⟩)
  | .assert φ k => do pure (.assert φ (← Typ.substPredTransM σ k))
  | .let_ v t k => do pure (.let_ v t (← Typ.substPredTransM σ k))
  | .pred v p k => do
      pure (.pred v (← Typ.substAtomM σ p) (← Typ.substPredTransM σ k))
  | .ite φ kt ke => do
      pure (.ite φ (← Typ.substPredTransM σ kt) (← Typ.substPredTransM σ ke))
termination_by structural a => a

/-- Rejecting substitution in a specification, mutually with `Typ.substM`. -/
def Typ.substSpecM (σ : V → Except ε (Typ.WithTypeVars W)) :
    Spec (Typ.WithTypeVars V) → Except ε (Spec (Typ.WithTypeVars W))
  | ⟨args, pred⟩ => do pure ⟨args, ← Typ.substPredTransM σ pred⟩
termination_by structural s => s

/-- Rejecting substitution in an optional specification, mutually with
`Typ.substM`. -/
def Typ.substSpecM? (σ : V → Except ε (Typ.WithTypeVars W)) :
    Option (Spec (Typ.WithTypeVars V)) → Except ε (Option (Spec (Typ.WithTypeVars W)))
  | none => pure none
  | some s => do pure (some (← Typ.substSpecM σ s))
termination_by structural s => s

end

mutual

/-- Every type variable a type mentions, in order of occurrence and with
repetitions. Descends into an arrow's specification for the same reason
substitution does. -/
def Typ.vars : Typ.WithTypeVars V → List V
  | .prim _ | .empty | .value => []
  | .sum ts | .tuple ts | .named _ ts => Typ.varsList ts
  | .arrow args ret spec => Typ.varsList args ++ Typ.vars ret ++ Typ.varsSpec? spec
  | .ref t | .array t | .ownedArray t | .vec t | .owned t => Typ.vars t
  | .tvar v => [v]
termination_by structural t => t

/-- The variables of a list of types, mutually with `Typ.vars`. -/
def Typ.varsList : List (Typ.WithTypeVars V) → List V
  | [] => []
  | t :: ts => Typ.vars t ++ Typ.varsList ts
termination_by structural ts => ts

/-- The variables an atom's types mention, mutually with `Typ.vars`. -/
def Typ.varsAtom : {s : Srt} → Atom (Typ.WithTypeVars V) s → List V
  | _, .isint _ | _, .isbool _ | _, .isinj .. | _, .rel .. => []
  | _, .own _ ty | _, .arr _ ty => Typ.vars ty
termination_by structural _ a => a

/-- The variables a postcondition mentions, mutually with `Typ.vars`. -/
def Typ.varsPost : Assertion (Typ.WithTypeVars V) Unit → List V
  | .ret () => []
  | .assert _ k | .let_ _ _ k => Typ.varsPost k
  | .pred _ p k => Typ.varsAtom p ++ Typ.varsPost k
  | .ite _ kt ke => Typ.varsPost kt ++ Typ.varsPost ke
termination_by structural a => a

/-- The variables a predicate transformer mentions, mutually with `Typ.vars`. -/
def Typ.varsPredTrans : Assertion (Typ.WithTypeVars V) (Post (Typ.WithTypeVars V)) → List V
  | .ret p => Typ.varsPost p.body
  | .assert _ k | .let_ _ _ k => Typ.varsPredTrans k
  | .pred _ p k => Typ.varsAtom p ++ Typ.varsPredTrans k
  | .ite _ kt ke => Typ.varsPredTrans kt ++ Typ.varsPredTrans ke
termination_by structural a => a

/-- The variables a specification mentions, mutually with `Typ.vars`. -/
def Typ.varsSpec : Spec (Typ.WithTypeVars V) → List V
  | s => Typ.varsPredTrans s.pred
termination_by structural s => s

/-- The variables an optional specification mentions, mutually with `Typ.vars`. -/
def Typ.varsSpec? : Option (Spec (Typ.WithTypeVars V)) → List V
  | none => []
  | some s => Typ.varsSpec s
termination_by structural s => s

end

/-! ### Laws of substitution -/

@[simp] theorem Typ.substList_eq (σ : V → Typ.WithTypeVars W) (ts : List (Typ.WithTypeVars V)) :
    Typ.substList σ ts = ts.map (Typ.subst σ) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [Typ.substList, ih]

mutual

@[simp] theorem Typ.subst_id : ∀ t : Typ.WithTypeVars V, Typ.subst .tvar t = t
  | .prim _ | .empty | .value | .tvar _ => rfl
  | .sum ts => by rw [Typ.subst, Typ.substList_id]
  | .tuple ts => by rw [Typ.subst, Typ.substList_id]
  | .named T ts => by rw [Typ.subst, Typ.substList_id]
  | .arrow args ret spec => by
      rw [Typ.subst, Typ.substList_id, Typ.subst_id ret, Typ.substSpec?_id]
  | .ref t => by rw [Typ.subst, Typ.subst_id t]
  | .array t => by rw [Typ.subst, Typ.subst_id t]
  | .ownedArray t => by rw [Typ.subst, Typ.subst_id t]
  | .vec t => by rw [Typ.subst, Typ.subst_id t]
  | .owned t => by rw [Typ.subst, Typ.subst_id t]
termination_by structural t => t

theorem Typ.substList_id : ∀ ts : List (Typ.WithTypeVars V), Typ.substList .tvar ts = ts
  | [] => rfl
  | t :: ts => by rw [Typ.substList, Typ.subst_id t, Typ.substList_id ts]
termination_by structural ts => ts

theorem Typ.substAtom_id :
    ∀ {s : Srt} (a : Atom (Typ.WithTypeVars V) s), Typ.substAtom .tvar a = a
  | _, .isint _ | _, .isbool _ | _, .isinj .. | _, .rel .. => rfl
  | _, .own _ ty => by rw [Typ.substAtom, Typ.subst_id ty]
  | _, .arr _ ty => by rw [Typ.substAtom, Typ.subst_id ty]
termination_by structural _ a => a

theorem Typ.substPost_id :
    ∀ a : Assertion (Typ.WithTypeVars V) Unit, Typ.substPost .tvar a = a
  | .ret () => rfl
  | .assert _ k => by rw [Typ.substPost, Typ.substPost_id k]
  | .let_ _ _ k => by rw [Typ.substPost, Typ.substPost_id k]
  | .pred _ p k => by rw [Typ.substPost, Typ.substAtom_id p, Typ.substPost_id k]
  | .ite _ kt ke => by rw [Typ.substPost, Typ.substPost_id kt, Typ.substPost_id ke]
termination_by structural a => a

theorem Typ.substPredTrans_id :
    ∀ a : Assertion (Typ.WithTypeVars V) (Post (Typ.WithTypeVars V)),
      Typ.substPredTrans .tvar a = a
  | .ret p => by rw [Typ.substPredTrans, Typ.substPost_id p.body]
  | .assert _ k => by rw [Typ.substPredTrans, Typ.substPredTrans_id k]
  | .let_ _ _ k => by rw [Typ.substPredTrans, Typ.substPredTrans_id k]
  | .pred _ p k => by
      rw [Typ.substPredTrans, Typ.substAtom_id p, Typ.substPredTrans_id k]
  | .ite _ kt ke => by
      rw [Typ.substPredTrans, Typ.substPredTrans_id kt, Typ.substPredTrans_id ke]
termination_by structural a => a

theorem Typ.substSpec_id : ∀ s : Spec (Typ.WithTypeVars V), Typ.substSpec .tvar s = s
  | ⟨_, pred⟩ => by rw [Typ.substSpec, Typ.substPredTrans_id pred]
termination_by structural s => s

theorem Typ.substSpec?_id :
    ∀ s : Option (Spec (Typ.WithTypeVars V)), Typ.substSpec? .tvar s = s
  | none => rfl
  | some s => by rw [Typ.substSpec?, Typ.substSpec_id s]
termination_by structural s => s

end

mutual

theorem Typ.subst_comp (σ : V → Typ.WithTypeVars W) (τ : W → Typ.WithTypeVars U) :
    ∀ t : Typ.WithTypeVars V,
      Typ.subst τ (Typ.subst σ t) = Typ.subst (fun v => Typ.subst τ (σ v)) t
  | .prim _ | .empty | .value | .tvar _ => rfl
  | .sum ts => by simp only [Typ.subst, Typ.substList_comp σ τ ts]
  | .tuple ts => by simp only [Typ.subst, Typ.substList_comp σ τ ts]
  | .named T ts => by simp only [Typ.subst, Typ.substList_comp σ τ ts]
  | .arrow args ret spec => by
      simp only [Typ.subst, Typ.substList_comp σ τ args, Typ.subst_comp σ τ ret,
        Typ.substSpec?_comp σ τ spec]
  | .ref t => by simp only [Typ.subst, Typ.subst_comp σ τ t]
  | .array t => by simp only [Typ.subst, Typ.subst_comp σ τ t]
  | .ownedArray t => by simp only [Typ.subst, Typ.subst_comp σ τ t]
  | .vec t => by simp only [Typ.subst, Typ.subst_comp σ τ t]
  | .owned t => by simp only [Typ.subst, Typ.subst_comp σ τ t]
termination_by structural t => t

theorem Typ.substList_comp (σ : V → Typ.WithTypeVars W) (τ : W → Typ.WithTypeVars U) :
    ∀ ts : List (Typ.WithTypeVars V),
      Typ.substList τ (Typ.substList σ ts) = Typ.substList (fun v => Typ.subst τ (σ v)) ts
  | [] => rfl
  | t :: ts => by simp only [Typ.substList, Typ.subst_comp σ τ t, Typ.substList_comp σ τ ts]
termination_by structural ts => ts

theorem Typ.substAtom_comp (σ : V → Typ.WithTypeVars W) (τ : W → Typ.WithTypeVars U) :
    ∀ {s : Srt} (a : Atom (Typ.WithTypeVars V) s),
      Typ.substAtom τ (Typ.substAtom σ a) = Typ.substAtom (fun v => Typ.subst τ (σ v)) a
  | _, .isint _ | _, .isbool _ | _, .isinj .. | _, .rel .. => rfl
  | _, .own _ ty => by simp only [Typ.substAtom, Typ.subst_comp σ τ ty]
  | _, .arr _ ty => by simp only [Typ.substAtom, Typ.subst_comp σ τ ty]
termination_by structural _ a => a

theorem Typ.substPost_comp (σ : V → Typ.WithTypeVars W) (τ : W → Typ.WithTypeVars U) :
    ∀ a : Assertion (Typ.WithTypeVars V) Unit,
      Typ.substPost τ (Typ.substPost σ a) = Typ.substPost (fun v => Typ.subst τ (σ v)) a
  | .ret () => rfl
  | .assert _ k => by simp only [Typ.substPost, Typ.substPost_comp σ τ k]
  | .let_ _ _ k => by simp only [Typ.substPost, Typ.substPost_comp σ τ k]
  | .pred _ p k => by
      simp only [Typ.substPost, Typ.substAtom_comp σ τ p, Typ.substPost_comp σ τ k]
  | .ite _ kt ke => by
      simp only [Typ.substPost, Typ.substPost_comp σ τ kt, Typ.substPost_comp σ τ ke]
termination_by structural a => a

theorem Typ.substPredTrans_comp (σ : V → Typ.WithTypeVars W) (τ : W → Typ.WithTypeVars U) :
    ∀ a : Assertion (Typ.WithTypeVars V) (Post (Typ.WithTypeVars V)),
      Typ.substPredTrans τ (Typ.substPredTrans σ a) =
        Typ.substPredTrans (fun v => Typ.subst τ (σ v)) a
  | .ret p => by simp only [Typ.substPredTrans, Typ.substPost_comp σ τ p.body]
  | .assert _ k => by simp only [Typ.substPredTrans, Typ.substPredTrans_comp σ τ k]
  | .let_ _ _ k => by simp only [Typ.substPredTrans, Typ.substPredTrans_comp σ τ k]
  | .pred _ p k => by
      simp only [Typ.substPredTrans, Typ.substAtom_comp σ τ p, Typ.substPredTrans_comp σ τ k]
  | .ite _ kt ke => by
      simp only [Typ.substPredTrans, Typ.substPredTrans_comp σ τ kt,
        Typ.substPredTrans_comp σ τ ke]
termination_by structural a => a

theorem Typ.substSpec_comp (σ : V → Typ.WithTypeVars W) (τ : W → Typ.WithTypeVars U) :
    ∀ s : Spec (Typ.WithTypeVars V),
      Typ.substSpec τ (Typ.substSpec σ s) = Typ.substSpec (fun v => Typ.subst τ (σ v)) s
  | ⟨_, pred⟩ => by simp only [Typ.substSpec, Typ.substPredTrans_comp σ τ pred]
termination_by structural s => s

theorem Typ.substSpec?_comp (σ : V → Typ.WithTypeVars W) (τ : W → Typ.WithTypeVars U) :
    ∀ s : Option (Spec (Typ.WithTypeVars V)),
      Typ.substSpec? τ (Typ.substSpec? σ s) = Typ.substSpec? (fun v => Typ.subst τ (σ v)) s
  | none => rfl
  | some s => by simp only [Typ.substSpec?, Typ.substSpec_comp σ τ s]
termination_by structural s => s

end

mutual

theorem Typ.subst_congr (σ τ : V → Typ.WithTypeVars W) :
    ∀ (t : Typ.WithTypeVars V), (∀ v ∈ Typ.vars t, σ v = τ v) →
      Typ.subst σ t = Typ.subst τ t
  | .prim _, _ | .empty, _ | .value, _ => rfl
  | .tvar v, h => h v (by simp [Typ.vars])
  | .sum ts, h => by
      simp only [Typ.subst, Typ.substList_congr σ τ ts fun v hv => h v (by simp [Typ.vars, hv])]
  | .tuple ts, h => by
      simp only [Typ.subst, Typ.substList_congr σ τ ts fun v hv => h v (by simp [Typ.vars, hv])]
  | .named T ts, h => by
      simp only [Typ.subst, Typ.substList_congr σ τ ts fun v hv => h v (by simp [Typ.vars, hv])]
  | .arrow args ret spec, h => by
      simp only [Typ.subst,
        Typ.substList_congr σ τ args fun v hv => h v (by simp [Typ.vars, hv]),
        Typ.subst_congr σ τ ret fun v hv => h v (by simp [Typ.vars, hv]),
        Typ.substSpec?_congr σ τ spec fun v hv => h v (by simp [Typ.vars, hv])]
  | .ref t, h => by
      simp only [Typ.subst, Typ.subst_congr σ τ t fun v hv => h v (by simp [Typ.vars, hv])]
  | .array t, h => by
      simp only [Typ.subst, Typ.subst_congr σ τ t fun v hv => h v (by simp [Typ.vars, hv])]
  | .ownedArray t, h => by
      simp only [Typ.subst, Typ.subst_congr σ τ t fun v hv => h v (by simp [Typ.vars, hv])]
  | .vec t, h => by
      simp only [Typ.subst, Typ.subst_congr σ τ t fun v hv => h v (by simp [Typ.vars, hv])]
  | .owned t, h => by
      simp only [Typ.subst, Typ.subst_congr σ τ t fun v hv => h v (by simp [Typ.vars, hv])]
termination_by structural t => t

theorem Typ.substList_congr (σ τ : V → Typ.WithTypeVars W) :
    ∀ (ts : List (Typ.WithTypeVars V)), (∀ v ∈ Typ.varsList ts, σ v = τ v) →
      Typ.substList σ ts = Typ.substList τ ts
  | [], _ => rfl
  | t :: ts, h => by
      simp only [Typ.substList,
        Typ.subst_congr σ τ t fun v hv => h v (by simp [Typ.varsList, hv]),
        Typ.substList_congr σ τ ts fun v hv => h v (by simp [Typ.varsList, hv])]
termination_by structural ts => ts

theorem Typ.substAtom_congr (σ τ : V → Typ.WithTypeVars W) :
    ∀ {s : Srt} (a : Atom (Typ.WithTypeVars V) s), (∀ v ∈ Typ.varsAtom a, σ v = τ v) →
      Typ.substAtom σ a = Typ.substAtom τ a
  | _, .isint _, _ | _, .isbool _, _ | _, .isinj .., _ | _, .rel .., _ => rfl
  | _, .own _ ty, h => by
      simp only [Typ.substAtom, Typ.subst_congr σ τ ty fun v hv => h v (by simp [Typ.varsAtom, hv])]
  | _, .arr _ ty, h => by
      simp only [Typ.substAtom, Typ.subst_congr σ τ ty fun v hv => h v (by simp [Typ.varsAtom, hv])]
termination_by structural _ a => a

theorem Typ.substPost_congr (σ τ : V → Typ.WithTypeVars W) :
    ∀ (a : Assertion (Typ.WithTypeVars V) Unit), (∀ v ∈ Typ.varsPost a, σ v = τ v) →
      Typ.substPost σ a = Typ.substPost τ a
  | .ret (), _ => rfl
  | .assert _ k, h => by
      simp only [Typ.substPost, Typ.substPost_congr σ τ k fun v hv => h v (by simp [Typ.varsPost, hv])]
  | .let_ _ _ k, h => by
      simp only [Typ.substPost, Typ.substPost_congr σ τ k fun v hv => h v (by simp [Typ.varsPost, hv])]
  | .pred _ p k, h => by
      simp only [Typ.substPost,
        Typ.substAtom_congr σ τ p fun v hv => h v (by simp [Typ.varsPost, hv]),
        Typ.substPost_congr σ τ k fun v hv => h v (by simp [Typ.varsPost, hv])]
  | .ite _ kt ke, h => by
      simp only [Typ.substPost,
        Typ.substPost_congr σ τ kt fun v hv => h v (by simp [Typ.varsPost, hv]),
        Typ.substPost_congr σ τ ke fun v hv => h v (by simp [Typ.varsPost, hv])]
termination_by structural a => a

theorem Typ.substPredTrans_congr (σ τ : V → Typ.WithTypeVars W) :
    ∀ (a : Assertion (Typ.WithTypeVars V) (Post (Typ.WithTypeVars V))),
      (∀ v ∈ Typ.varsPredTrans a, σ v = τ v) →
      Typ.substPredTrans σ a = Typ.substPredTrans τ a
  | .ret p, h => by
      simp only [Typ.substPredTrans,
        Typ.substPost_congr σ τ p.body fun v hv => h v (by simp [Typ.varsPredTrans, hv])]
  | .assert _ k, h => by
      simp only [Typ.substPredTrans,
        Typ.substPredTrans_congr σ τ k fun v hv => h v (by simp [Typ.varsPredTrans, hv])]
  | .let_ _ _ k, h => by
      simp only [Typ.substPredTrans,
        Typ.substPredTrans_congr σ τ k fun v hv => h v (by simp [Typ.varsPredTrans, hv])]
  | .pred _ p k, h => by
      simp only [Typ.substPredTrans,
        Typ.substAtom_congr σ τ p fun v hv => h v (by simp [Typ.varsPredTrans, hv]),
        Typ.substPredTrans_congr σ τ k fun v hv => h v (by simp [Typ.varsPredTrans, hv])]
  | .ite _ kt ke, h => by
      simp only [Typ.substPredTrans,
        Typ.substPredTrans_congr σ τ kt fun v hv => h v (by simp [Typ.varsPredTrans, hv]),
        Typ.substPredTrans_congr σ τ ke fun v hv => h v (by simp [Typ.varsPredTrans, hv])]
termination_by structural a => a

theorem Typ.substSpec_congr (σ τ : V → Typ.WithTypeVars W) :
    ∀ (s : Spec (Typ.WithTypeVars V)), (∀ v ∈ Typ.varsSpec s, σ v = τ v) →
      Typ.substSpec σ s = Typ.substSpec τ s
  | ⟨_, pred⟩, h => by
      simp only [Typ.substSpec,
        Typ.substPredTrans_congr σ τ pred fun v hv => h v (by simp [Typ.varsSpec, hv])]
termination_by structural s => s

theorem Typ.substSpec?_congr (σ τ : V → Typ.WithTypeVars W) :
    ∀ (s : Option (Spec (Typ.WithTypeVars V))), (∀ v ∈ Typ.varsSpec? s, σ v = τ v) →
      Typ.substSpec? σ s = Typ.substSpec? τ s
  | none, _ => rfl
  | some s, h => by
      simp only [Typ.substSpec?,
        Typ.substSpec_congr σ τ s fun v hv => h v (by simp [Typ.varsSpec?, hv])]
termination_by structural s => s

end

/-! ## Schemes

What a name is bound at: a type, together with the variables a use site may
choose. Only a context entry carries a scheme, which is what makes the
polymorphism rank-1 — no type has a quantifier inside it. A local binding
quantifies nothing, so its scheme is its type. -/

/-- A type scheme: the variables a use site instantiates, and the type they
stand in. -/
structure Scheme where
  tparams : List TyVar
  ty : Typ
  deriving Repr, DecidableEq

/-- The scheme of a binding nothing may instantiate. -/
def Scheme.mono (t : Typ) : Scheme := ⟨[], t⟩

/-- The substitution an instantiation recorded on a use site stands for. A
variable the instantiation does not mention is one the scheme does not
quantify, so what it maps to is never looked at. -/
def Typ.ofInst (inst : List (TyVar × Typ)) : TyVar → Typ :=
  fun v => (inst.lookup v).getD .empty

/-- Instantiate a scheme by a substitution: only the quantified variables are
replaced. -/
def Scheme.instantiate (s : Scheme) (σ : TyVar → Typ) : Typ :=
  Typ.subst (fun v => if v ∈ s.tparams then σ v else .tvar v) s.ty

@[simp] theorem Scheme.instantiate_mono (t : Typ) (σ : TyVar → Typ) :
    (Scheme.mono t).instantiate σ = t := by
  simp [Scheme.instantiate, Scheme.mono]

/-- A data declaration: type parameters, and one payload type per constructor.
The payloads are schema types, since they mention the declaration's own
parameters. -/
structure DataDecl where
  tparams : List TyVar
  payloads : List SchemaTyp
  deriving Repr, Inhabited, DecidableEq

namespace Predef

/-- All predefined types exposed by the frontend. -/
def all : List Predef := [.list, .option]

/-- The surface type name. -/
def name : Predef → String
  | .list => "list"
  | .option => "option"

/-- Type parameters of a predefined declaration. -/
def tparams : Predef → List TyVar
  | .list | .option => ["a"]

/-- Ordered constructors. Their position is the runtime injection tag. -/
def ctors : Predef → List (String × SchemaTyp)
  | .option => [
      ("None", .unit),
      ("Some", .tvar "a")]
  | .list => [
      ("[]", .unit),
      ("::", .tuple [.tvar "a", .list (.tvar "a")])]

/-- The canonical core declaration of a predefined type. -/
def decl (p : Predef) : DataDecl :=
  { tparams := p.tparams, payloads := (p.ctors.map Prod.snd) }

/-- Number of type arguments accepted by the predefined type. -/
def arity (p : Predef) : Nat := p.tparams.length

end Predef

abbrev TypeEnv := TypeName → Option DataDecl

def TypeEnv.empty : TypeEnv := fun _ => none

/-- The sum of a declaration's payloads at the given type arguments. Callers
check the argument count against `tparams` first; a parameter left unmatched by
a mis-sized application is instantiated at the uninhabited type. -/
def DataDecl.instantiate (d : DataDecl) (args : List (Typ.WithTypeVars V)) :
    Typ.WithTypeVars V :=
  let σ := fun v =>
    match (d.tparams.zip args).find? (fun p => p.1 == v) with
    | some (_, ty) => ty
    | none => .empty
  .sum (d.payloads.map (Typ.subst σ))

/-- How many type arguments a name takes, `none` when it has no declaration. -/
def TypeName.params (Θ : TypeEnv) : TypeName → Option Nat
  | .user T => (Θ (.user T)).map (·.tparams.length)
  | .predef p => some p.arity

def TypeName.unfold (Θ : TypeEnv) (T : TypeName) (args : List (Typ.WithTypeVars V)) :
    Option (Typ.WithTypeVars V) :=
  match T with
  | .user _ => (Θ T).map (·.instantiate args)
  | .predef p =>
      if args.length = p.arity then some (p.decl.instantiate args) else none

@[simp] theorem TypeName.unfold_predef (Θ : TypeEnv) (p : Predef)
    (args : List (Typ.WithTypeVars V)) :
    TypeName.unfold Θ (.predef p) args =
      if args.length = p.arity then some (p.decl.instantiate args) else none := rfl

/-- Looking a parameter up among substituted arguments finds the substituted
argument, since substitution touches neither the parameter names nor their
order. -/
private theorem find?_zip_map {α β γ : Type} [BEq α] (f : β → γ) (p : α → Bool) :
    ∀ (as : List α) (bs : List β),
      (as.zip (bs.map f)).find? (fun q => p q.1) =
        ((as.zip bs).find? (fun q => p q.1)).map (fun q => (q.1, f q.2))
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
      simp only [List.map_cons, List.zip_cons_cons, List.find?_cons]
      cases p a
      · simpa using find?_zip_map f p as bs
      · simp

/-- Instantiating a declaration commutes with substitution: a parameter is
replaced by the substituted argument either way, and a payload variable the
declaration does not bind goes to the uninhabited type either way. -/
theorem DataDecl.instantiate_subst (d : DataDecl) (σ : V → Typ.WithTypeVars W)
    (args : List (Typ.WithTypeVars V)) :
    d.instantiate (args.map (Typ.subst σ)) = Typ.subst σ (d.instantiate args) := by
  simp only [DataDecl.instantiate, Typ.subst, Typ.substList_eq, List.map_map]
  refine congrArg _ (List.map_congr_left fun payload _ => ?_)
  rw [Function.comp_apply, Typ.subst_comp]
  refine congrArg (Typ.subst · payload) (funext fun v => ?_)
  rw [find?_zip_map (Typ.subst σ) (· == v) d.tparams args]
  cases (d.tparams.zip args).find? (fun q => q.1 == v) <;> rfl

/-- Unfolding a name commutes with substitution. -/
theorem TypeName.unfold_subst (Θ : TypeEnv) (T : TypeName) (σ : V → Typ.WithTypeVars W)
    (args : List (Typ.WithTypeVars V)) :
    TypeName.unfold Θ T (args.map (Typ.subst σ)) =
      (TypeName.unfold Θ T args).map (Typ.subst σ) := by
  cases T with
  | user T =>
      simp [TypeName.unfold, Option.map_map, Function.comp_def, DataDecl.instantiate_subst]
  | predef p =>
      by_cases h : args.length = p.arity <;>
        simp [TypeName.unfold, h, DataDecl.instantiate_subst]

/-! ## Operator typing -/

def BinOp.typeOf : BinOp → Typ → Typ → Option Typ
  | op, .prim p1, .prim p2 => (PrimitiveType.binOpTypeOf op p1 p2).map Typ.prim
  | _, _, _ => none

/-- Arithmetic binary operators require integer inputs and produce an integer. -/
theorem BinOp.typeOf_arith {op : BinOp} {t1 t2 ty : Typ}
    (hop : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .div ∨ op = .mod)
    (hty : BinOp.typeOf op t1 t2 = some ty) :
    t1 = Typ.int ∧ t2 = Typ.int ∧ ty = Typ.int := by
  rcases hop with rfl | rfl | rfl | rfl | rfl
  all_goals
    cases t1 <;> cases t2 <;> simp [BinOp.typeOf] at hty
    rename_i p1 p2
    rcases hty with ⟨p, hprim, rfl⟩
    obtain ⟨rfl, rfl, rfl⟩ := PrimitiveType.binOpTypeOf_arith (by simp) hprim
    simp [Typ.int]

/-- Integer comparison binary operators require integer inputs and produce a Boolean. -/
theorem BinOp.typeOf_compare {op : BinOp} {t1 t2 ty : Typ}
    (hop : op = .eq ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (hty : BinOp.typeOf op t1 t2 = some ty) :
    t1 = Typ.int ∧ t2 = Typ.int ∧ ty = Typ.bool := by
  rcases hop with rfl | rfl | rfl | rfl | rfl
  all_goals
    cases t1 <;> cases t2 <;> simp [BinOp.typeOf] at hty
    rename_i p1 p2
    rcases hty with ⟨p, hprim, rfl⟩
    obtain ⟨rfl, rfl, rfl⟩ := PrimitiveType.binOpTypeOf_compare (by simp) hprim
    simp [Typ.int, Typ.bool]

/-- Boolean binary operators require Boolean inputs and produce a Boolean. -/
theorem BinOp.typeOf_bool {op : BinOp} {t1 t2 ty : Typ}
    (hop : op = .and ∨ op = .or)
    (hty : BinOp.typeOf op t1 t2 = some ty) :
    t1 = Typ.bool ∧ t2 = Typ.bool ∧ ty = Typ.bool := by
  rcases hop with rfl | rfl
  all_goals
    cases t1 <;> cases t2 <;> simp [BinOp.typeOf] at hty
    rename_i p1 p2
    rcases hty with ⟨p, hprim, rfl⟩
    obtain ⟨rfl, rfl, rfl⟩ := PrimitiveType.binOpTypeOf_bool (by simp) hprim
    simp [Typ.bool]

def UnOp.typeOf : UnOp → Typ → Option Typ
  | op, .prim p => (PrimitiveType.unOpTypeOf op p).map Typ.prim
  | .proj n, .tuple ts => ts[n]?
  | _, _             => none

/-- Integer unary operators require an integer input and produce an integer. -/
theorem UnOp.typeOf_int {op : UnOp} {t ty : Typ}
    (hop : op = .neg)
    (hty : UnOp.typeOf op t = some ty) :
    t = Typ.int ∧ ty = Typ.int := by
  subst hop
  cases t <;> simp [UnOp.typeOf] at hty
  rename_i p
  rcases hty with ⟨p', hprim, rfl⟩
  obtain ⟨rfl, rfl⟩ := PrimitiveType.unOpTypeOf_int rfl hprim
  simp [Typ.int]

/-- Boolean unary operators require a Boolean input and produce a Boolean. -/
theorem UnOp.typeOf_bool {op : UnOp} {t ty : Typ}
    (hop : op = .not)
    (hty : UnOp.typeOf op t = some ty) :
    t = Typ.bool ∧ ty = Typ.bool := by
  subst hop
  cases t <;> simp [UnOp.typeOf] at hty
  rename_i p
  rcases hty with ⟨p', hprim, rfl⟩
  obtain ⟨rfl, rfl⟩ := PrimitiveType.unOpTypeOf_bool rfl hprim
  simp [Typ.bool]

end TinyML
