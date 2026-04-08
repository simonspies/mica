namespace TinyML

abbrev Var := String

inductive Typ where
  | unit
  | bool
  | int
  | sum (ts : List Typ)
  | arrow (t1 t2 : Typ)
  | ref (t: Typ)
  | empty   -- bottom type (uninhabited)
  | value   -- top type (all runtime values)
  | tuple (ts : List Typ)
  deriving Repr

def Typ.decEq : (a b : Typ) → Decidable (a = b)
  | .unit, .unit | .bool, .bool | .int, .int | .empty, .empty | .value, .value => isTrue rfl
  | .sum ss, .sum ts => match typesDecEq ss ts with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .arrow s1 s2, .arrow t1 t2 =>
    match s1.decEq t1, s2.decEq t2 with
    | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
    | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
    | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .ref s, .ref t => match s.decEq t with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .tuple ss, .tuple ts => match typesDecEq ss ts with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .unit, .bool | .unit, .int | .unit, .sum .. | .unit, .arrow ..
  | .unit, .ref .. | .unit, .empty | .unit, .value | .unit, .tuple ..
  | .bool, .unit | .bool, .int | .bool, .sum .. | .bool, .arrow ..
  | .bool, .ref .. | .bool, .empty | .bool, .value | .bool, .tuple ..
  | .int, .unit | .int, .bool | .int, .sum .. | .int, .arrow ..
  | .int, .ref .. | .int, .empty | .int, .value | .int, .tuple ..
  | .sum .., .unit | .sum .., .bool | .sum .., .int
  | .sum .., .arrow .. | .sum .., .ref .. | .sum .., .empty | .sum .., .value | .sum .., .tuple ..
  | .arrow .., .unit | .arrow .., .bool | .arrow .., .int
  | .arrow .., .sum .. | .arrow .., .ref .. | .arrow .., .empty | .arrow .., .value | .arrow .., .tuple ..
  | .ref .., .unit | .ref .., .bool | .ref .., .int
  | .ref .., .sum .. | .ref .., .arrow .. | .ref .., .empty | .ref .., .value | .ref .., .tuple ..
  | .empty, .unit | .empty, .bool | .empty, .int | .empty, .sum ..
  | .empty, .arrow .. | .empty, .ref .. | .empty, .value | .empty, .tuple ..
  | .value, .unit | .value, .bool | .value, .int | .value, .sum ..
  | .value, .arrow .. | .value, .ref .. | .value, .empty | .value, .tuple ..
  | .tuple .., .unit | .tuple .., .bool | .tuple .., .int
  | .tuple .., .sum .. | .tuple .., .arrow .. | .tuple .., .ref .. | .tuple .., .empty
  | .tuple .., .value => isFalse (by intro h; cases h)
where
  typesDecEq : (as bs : List Typ) → Decidable (as = bs)
    | [], [] => isTrue rfl
    | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
    | a :: as, b :: bs => match a.decEq b, typesDecEq as bs with
      | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
      | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)

instance : DecidableEq Typ := Typ.decEq
instance : BEq Typ := ⟨fun a b => decide (a = b)⟩
instance : LawfulBEq Typ where
  eq_of_beq h := of_decide_eq_true h
  rfl := by simp [BEq.beq]

inductive BinOp where
  | add | sub | mul | div | mod
  | eq | lt | le | gt | ge
  | and | or
  deriving Repr, BEq, Inhabited, DecidableEq

inductive UnOp where
  | neg | not
  | proj (n : Nat)
  deriving Repr, BEq, Inhabited, DecidableEq

inductive Const where
  | int  (n : Int)
  | bool (b : Bool)
  | unit
  deriving Repr, BEq, DecidableEq

end TinyML
