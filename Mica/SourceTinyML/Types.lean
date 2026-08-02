-- SUMMARY: TinyML types over a parameter of type variables, type declarations, and subtyping.
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
two instantiations are used here: `Typ`, whose `V` is uninhabited, and
`SchemaTyp`, whose `V` is a source type variable. Type inference adds a third. -/
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

/-- The type language the verifier works in. No `tvar` node can be built, so a
`Typ` is closed by construction. -/
abbrev Typ := Typ.WithTypeVars Empty

/-- The type language source annotations and polymorphic signatures are written
in: a `Typ` that may still mention named type variables. -/
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
moves a type between the instantiations of `Typ.WithTypeVars`: `Typ.subst
Empty.elim` embeds a `Typ` into any of them, and a substitution into `Typ`
closes a `SchemaTyp`. -/

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

/-- Close a schema by instantiating each variable, failing on the first one the
assignment does not cover. -/
def SchemaTyp.close (inst : TyVar → Option Typ) (t : SchemaTyp) : Except TyVar Typ :=
  Typ.substM (fun v => (inst v).elim (.error v) .ok) t

mutual

/-- A type is closed when it contains no type variables. -/
def Typ.closed : Typ.WithTypeVars V → Bool
  | .prim _ => true
  | .sum ts => Typ.closedList ts
  | .arrow args ret spec => Typ.closedList args && Typ.closed ret && Typ.closedSpec? spec
  | .ref t => Typ.closed t
  | .array t => Typ.closed t
  | .ownedArray t => Typ.closed t
  | .vec t => Typ.closed t
  | .owned t => Typ.closed t
  | .empty => true
  | .value => true
  | .tuple ts => Typ.closedList ts
  | .tvar _ => false
  | .named _ args => Typ.closedList args
termination_by structural t => t

/-- Closedness of a list of types, mutually with `Typ.closed`. -/
def Typ.closedList : List (Typ.WithTypeVars V) → Bool
  | [] => true
  | t :: ts => Typ.closed t && Typ.closedList ts
termination_by structural ts => ts

/-- Closedness of the types an atom mentions, mutually with `Typ.closed`. -/
def Typ.closedAtom : {s : Srt} → Atom (Typ.WithTypeVars V) s → Bool
  | _, .isint _ | _, .isbool _ | _, .isinj .. | _, .rel .. => true
  | _, .own _ ty => Typ.closed ty
  | _, .arr _ ty => Typ.closed ty
termination_by structural _ a => a

/-- Closedness of a postcondition assertion, mutually with `Typ.closed`. -/
def Typ.closedPost : Assertion (Typ.WithTypeVars V) Unit → Bool
  | .ret () => true
  | .assert _ k => Typ.closedPost k
  | .let_ _ _ k => Typ.closedPost k
  | .pred _ p k => Typ.closedAtom p && Typ.closedPost k
  | .ite _ kt ke => Typ.closedPost kt && Typ.closedPost ke
termination_by structural a => a

/-- Closedness of a predicate transformer, mutually with `Typ.closed`. -/
def Typ.closedPredTrans : Assertion (Typ.WithTypeVars V) (Post (Typ.WithTypeVars V)) → Bool
  | .ret p => Typ.closedPost p.body
  | .assert _ k => Typ.closedPredTrans k
  | .let_ _ _ k => Typ.closedPredTrans k
  | .pred _ p k => Typ.closedAtom p && Typ.closedPredTrans k
  | .ite _ kt ke => Typ.closedPredTrans kt && Typ.closedPredTrans ke
termination_by structural a => a

/-- Closedness of a specification, mutually with `Typ.closed`. -/
def Typ.closedSpec : Spec (Typ.WithTypeVars V) → Bool
  | s => Typ.closedPredTrans s.pred
termination_by structural s => s

/-- Closedness of an optional specification, mutually with `Typ.closed`. -/
def Typ.closedSpec? : Option (Spec (Typ.WithTypeVars V)) → Bool
  | none => true
  | some s => Typ.closedSpec s
termination_by structural s => s

end

@[simp] theorem Typ.substList_eq (σ : V → Typ.WithTypeVars W) (ts : List (Typ.WithTypeVars V)) :
    Typ.substList σ ts = ts.map (Typ.subst σ) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [Typ.substList, ih]

@[simp] theorem Typ.closedList_eq (ts : List (Typ.WithTypeVars V)) :
    Typ.closedList ts = (ts.map Typ.closed).all id := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [Typ.closedList, ih]

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
def DataDecl.instantiate (d : DataDecl) (args : List Typ) : Typ :=
  let σ := fun v =>
    match (d.tparams.zip args).find? (fun p => p.1 == v) with
    | some (_, ty) => ty
    | none => .empty
  .sum (d.payloads.map (Typ.subst σ))

def TypeName.unfold (Θ : TypeEnv) (T : TypeName) (args : List Typ) : Option Typ :=
  match T with
  | .user _ => (Θ T).map (·.instantiate args)
  | .predef p =>
      if args.length = p.arity then some (p.decl.instantiate args) else none

@[simp] theorem TypeName.unfold_predef (Θ : TypeEnv) (p : Predef) (args : List Typ) :
    TypeName.unfold Θ (.predef p) args =
      if args.length = p.arity then some (p.decl.instantiate args) else none := rfl

/-! ## Weight and depth measures

Both skip an arrow's specification. They exist to justify termination of
subtyping, joins, and meets, and none of those descend into a specification: a
specified arrow is invariant, so two are compared by equality. -/

mutual
  @[reducible]
  def Typ.weight : Typ → Nat
    | .prim _ | .empty | .value | .tvar _ => 1
    | .sum ts => 1 + Typ.weights ts
    | .arrow args ret _ => 1 + Typ.weights args + Typ.weight ret
    | .ref t => 1 + Typ.weight t
    | .array t => 1 + Typ.weight t
    | .ownedArray t => 1 + Typ.weight t
    | .vec t => 1 + Typ.weight t
    | .owned t => 1 + Typ.weight t
    | .tuple ts => 1 + Typ.weights ts
    | .named _ args => 1 + Typ.weights args

  @[reducible]
  def Typ.weights : List Typ → Nat
    | [] => 0
    | t :: ts => Typ.weight t + Typ.weights ts
end

mutual
  @[reducible]
  def Typ.depth : Typ → Nat
    | .prim _ | .empty | .value | .tvar _ => 1
    | .sum ts => 1 + Typ.depths ts
    | .arrow args ret _ => 1 + max (Typ.depths args) (Typ.depth ret)
    | .ref t => 1 + Typ.depth t
    | .array t => 1 + Typ.depth t
    | .ownedArray t => 1 + Typ.depth t
    | .vec t => 1 + Typ.depth t
    | .owned t => 1 + Typ.depth t
    | .tuple ts => 1 + Typ.depths ts
    | .named _ args => 1 + Typ.depths args

  @[reducible]
  def Typ.depths : List Typ → Nat
    | [] => 0
    | t :: ts => max (Typ.depth t) (Typ.depths ts)
end

theorem Typ.weight_pos (t : Typ) : 0 < Typ.weight t := by
  cases t <;> simp [Typ.weight] <;> omega

/-! ## Subtyping decision procedure -/

mutual

  def Typ.subBody (Θ : TypeEnv) (recur : Typ → Typ → Bool) : Typ → Typ → Bool :=
      fun s t =>
        match s, t with
        | .empty, _ => true
        | _, .value => true
        | .sum ss, .sum ts => Typ.subListBody Θ recur ss ts
        | .arrow ss s none, .arrow ts t none =>
            Typ.subListBody Θ recur ts ss && Typ.subBody Θ recur s t
        | .arrow ss s (some p), .arrow ts t (some q) =>
            ss == ts && s == t && p == q
        | .arrow .., .arrow .. => false
        | .tuple ss, .tuple ts => Typ.subListBody Θ recur ss ts
        | _, _ =>
            if s == t then true
            else match s, t with
              | .named T args, _ => match TypeName.unfold Θ T args with
                  | some s' => recur s' t
                  | none => false
              | _, .named T args => match TypeName.unfold Θ T args with
                  | some t' => recur s t'
                  | none => false
              | _, _ => false
  termination_by s t => Typ.weight s + Typ.weight t
  decreasing_by
    all_goals
      simp [Typ.weight]
      try omega

  def Typ.subListBody (Θ : TypeEnv) (recur : Typ → Typ → Bool) : List Typ → List Typ → Bool
    | [], [] => true
    | s :: ss, t :: ts => Typ.subBody Θ recur s t && Typ.subListBody Θ recur ss ts
    | _, _ => false
  termination_by ss ts => 1 + Typ.weights ss + Typ.weights ts
  decreasing_by
    all_goals
      have hs : 0 < Typ.weight s := Typ.weight_pos s
      have ht : 0 < Typ.weight t := Typ.weight_pos t
      simp [Typ.weights]
      omega
end

def Typ.subi (Θ : TypeEnv) (steps : Nat) : Typ → Typ → Bool :=
  match steps with
  | 0 => fun _ _ => false
  | n + 1 => Typ.subBody Θ (Typ.subi Θ n)

def Typ.subListi (Θ : TypeEnv) (steps : Nat) : List Typ → List Typ → Bool :=
  match steps with
  | 0 => fun _ _ => false
  | n + 1 => Typ.subListBody Θ (Typ.subi Θ n)

def Typ.sub (Θ : TypeEnv) : Typ → Typ → Bool :=
  fun s t => Typ.subi Θ (max (Typ.depth s) (Typ.depth t)) s t

def Typ.subList (Θ : TypeEnv) : List Typ → List Typ → Bool :=
  fun ss ts => Typ.subListi Θ (max (Typ.depths ss) (Typ.depths ts)) ss ts

/-! ## Subtyping relation -/

mutual
  -- Converting `owned A` to `ref A` allocates a shared invariant from the
  -- spatial points-to assertion; it is a logical view shift, not subtyping.
  inductive Typ.Sub (Θ : TypeEnv) : Typ → Typ → Prop where
    | refl  : Typ.Sub Θ t t
    | bot   : Typ.Sub Θ .empty t
    | top   : Typ.Sub Θ t .value
    | trans : Typ.Sub Θ s t → Typ.Sub Θ t u → Typ.Sub Θ s u
    | sum   : Typ.SubList Θ ss ts
            → Typ.Sub Θ (.sum ss) (.sum ts)
    /-- Only unspecified arrows are structural. A specified arrow is invariant
    in its whole signature and specification, so it is related to another type
    only by `refl` (or through `top`/`bot`). -/
    | arrow : Typ.SubList Θ ts ss
            → Typ.Sub Θ s t
            → Typ.Sub Θ (.arrow ss s none) (.arrow ts t none)
    | tuple : Typ.SubList Θ ss ts
            → Typ.Sub Θ (.tuple ss) (.tuple ts)
    | named_left : TypeName.unfold Θ T args = some ty
                 → Typ.Sub Θ ty t
                 → Typ.Sub Θ (.named T args) t
    | named_right : TypeName.unfold Θ T args = some ty
                  → Typ.Sub Θ s ty
                  → Typ.Sub Θ s (.named T args)

  inductive Typ.SubList (Θ : TypeEnv) : List Typ → List Typ → Prop where
    | nil  : Typ.SubList Θ [] []
    | cons : Typ.Sub Θ s t → Typ.SubList Θ ss ts → Typ.SubList Θ (s :: ss) (t :: ts)
end

theorem Typ.SubList.length_eq : Typ.SubList Θ ss ts → ss.length = ts.length
  | .nil => rfl
  | .cons _ h => by simp [List.length_cons, h.length_eq]

-- Forward direction: decision procedure is sound.
mutual
  private theorem Typ.subBody_sound {Θ : TypeEnv} {recur : Typ → Typ → Bool}
      (hrecur : ∀ {s t}, recur s t = true → Typ.Sub Θ s t)
      {s t : Typ} (h : Typ.subBody Θ recur s t = true) : Typ.Sub Θ s t := by
    unfold Typ.subBody at h
    split at h
    · exact .bot
    · exact .top
    · exact .sum (subListBody_sound hrecur h)
    · simp [Bool.and_eq_true] at h
      exact .arrow (subListBody_sound hrecur h.1) (subBody_sound hrecur h.2)
    · simp [Bool.and_eq_true] at h
      obtain ⟨⟨hargs, hret⟩, hspec⟩ := h
      subst hargs; subst hret; subst hspec
      exact .refl
    · exact absurd h (by simp)
    · exact .tuple (subListBody_sound hrecur h)
    · -- catchall: if s == t then true else match (s, t) for named
      split at h
      · -- s == t
        rename_i hbeq
        have heq : s = t := by simpa using hbeq
        subst heq; exact .refl
      · -- s ≠ t, check if either side is named
        split at h
        · -- s = .named T args
          rename_i T args hneq
          split at h
          · rename_i s' hunfold
            exact .named_left hunfold (hrecur h)
          · cases h
        · -- t = .named T args (s is not named)
          rename_i T args hneq
          split at h
          · rename_i t' hunfold
            exact .named_right hunfold (hrecur h)
          · cases h
        · -- neither named
          cases h
  termination_by Typ.weight s + Typ.weight t
  decreasing_by
    all_goals
      subst_vars
      try simp [Typ.weight]
      try omega

  private theorem Typ.subListBody_sound {Θ : TypeEnv} {recur : Typ → Typ → Bool}
      (hrecur : ∀ {s t}, recur s t = true → Typ.Sub Θ s t)
      {ss ts : List Typ}
      (h : Typ.subListBody Θ recur ss ts = true) : Typ.SubList Θ ss ts := by
    match ss, ts with
    | [], [] =>
        exact .nil
    | s :: ss, t :: ts =>
        simp [Typ.subListBody, Bool.and_eq_true] at h
        exact .cons (subBody_sound hrecur h.1) (subListBody_sound hrecur h.2)
    | [], _ :: _ | _ :: _, [] =>
        simp [Typ.subListBody] at h
  termination_by 1 + Typ.weights ss + Typ.weights ts
  decreasing_by
    all_goals
      have hs : 0 < Typ.weight s := Typ.weight_pos s
      have ht : 0 < Typ.weight t := Typ.weight_pos t
      simp [Typ.weights]
      omega

  private theorem Typ.subi_sound {Θ : TypeEnv} {steps : Nat} {s t : Typ}
      (h : Typ.subi Θ steps s t = true) : Typ.Sub Θ s t := by
    induction steps generalizing s t with
    | zero =>
      simp [Typ.subi] at h
    | succ n ih =>
      simpa [Typ.subi] using
        (Typ.subBody_sound (Θ := Θ) (recur := Typ.subi Θ n) (hrecur := fun {s t} h => ih h) h)

  private theorem Typ.subListi_sound {Θ : TypeEnv} {steps : Nat}
      {ss ts : List Typ} (h : Typ.subListi Θ steps ss ts = true) : Typ.SubList Θ ss ts := by
    induction steps generalizing ss ts with
    | zero =>
      simp [Typ.subListi] at h
    | succ n ih =>
      simpa [Typ.subListi] using
        (Typ.subListBody_sound (Θ := Θ) (recur := Typ.subi Θ n) (hrecur := fun {s t} h => Typ.subi_sound h) h)
end

theorem Typ.sub_sound {Θ : TypeEnv} {s t : Typ}
    (h : Typ.sub Θ s t = true) : Typ.Sub Θ s t := by
  exact Typ.subi_sound (Θ := Θ) (steps := max (Typ.depth s) (Typ.depth t)) h

theorem Typ.subList_sound {Θ : TypeEnv} {ss ts : List Typ}
    (h : Typ.subList Θ ss ts = true) : Typ.SubList Θ ss ts := by
  exact Typ.subListi_sound (Θ := Θ) (steps := max (Typ.depths ss) (Typ.depths ts)) h

/-! ## Join and meet -/

mutual
  def Typ.join (Θ : TypeEnv) : Typ → Typ → Typ
    | .empty, t | t, .empty => t
    | .value, _ | _, .value => .value
    | .sum  ss,     .sum  ts     => if ss.length == ts.length
                                    then .sum (Typ.joinList Θ ss ts)
                                    else .value
    | .arrow ss s none, .arrow ts t none => if ss.length == ts.length
                                  then .arrow (Typ.meetList Θ ss ts) (Typ.join Θ s t) none
                                  else .value
    | .arrow ss s (some p), .arrow ts t (some q) =>
        if ss == ts && s == t && p == q then .arrow ss s (some p) else .value
    | .arrow .., .arrow .. => .value
    | .ref s,       .ref t       => if s == t then .ref s else .value
    | .array s,     .array t     => if s == t then .array s else .value
    | .ownedArray s, .ownedArray t => if s == t then .ownedArray s else .value
    | .vec s,       .vec t       => if s == t then .vec s else .value
    | .owned s,     .owned t     => if s == t then .owned s else .value
    | .tuple ss,    .tuple ts    => if ss.length == ts.length
                                    then .tuple (Typ.joinList Θ ss ts)
                                    else .value
    | s, t =>
        if Typ.sub Θ s t then t
        else if Typ.sub Θ t s then s
        else .value

  def Typ.meet (Θ : TypeEnv) : Typ → Typ → Typ
    | .value, t | t, .value => t
    | .empty, _ | _, .empty => .empty
    | .sum  ss,     .sum  ts     => if ss.length == ts.length
                                    then .sum (Typ.meetList Θ ss ts)
                                    else .empty
    | .arrow ss s none, .arrow ts t none => if ss.length == ts.length
                                  then .arrow (Typ.joinList Θ ss ts) (Typ.meet Θ s t) none
                                  else .empty
    | .arrow ss s (some p), .arrow ts t (some q) =>
        if ss == ts && s == t && p == q then .arrow ss s (some p) else .empty
    | .arrow .., .arrow .. => .empty
    | .ref s,       .ref t       => if s == t then .ref s else .empty
    | .array s,     .array t     => if s == t then .array s else .empty
    | .ownedArray s, .ownedArray t => if s == t then .ownedArray s else .empty
    | .vec s,       .vec t       => if s == t then .vec s else .empty
    | .owned s,     .owned t     => if s == t then .owned s else .empty
    | .tuple ss,    .tuple ts    => if ss.length == ts.length
                                    then .tuple (Typ.meetList Θ ss ts)
                                    else .empty
    | s, t =>
        if Typ.sub Θ s t then s
        else if Typ.sub Θ t s then t
        else .empty

  def Typ.joinList (Θ : TypeEnv) : List Typ → List Typ → List Typ
    | s :: ss, t :: ts => Typ.join Θ s t :: Typ.joinList Θ ss ts
    | _, _             => []

  def Typ.meetList (Θ : TypeEnv) : List Typ → List Typ → List Typ
    | s :: ss, t :: ts => Typ.meet Θ s t :: Typ.meetList Θ ss ts
    | _, _             => []
end

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
