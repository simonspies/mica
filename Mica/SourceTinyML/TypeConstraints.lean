-- SUMMARY: First-order constraint formulas asserting that a term has a given TinyML type.
import Mica.SourceTinyML.Types
import Mica.FOL.Formulas
import Mica.Base.Fresh

/-!
# SMT type constraints

Formulas encoding `ValHasType` checks as first-order constraints. The
generators need only `TinyML.Typ` and the FOL term/formula language, so they sit
*below* typing, which lets elaboration emit them directly. Their soundness
lemmas (`_wfIn`, `_hold`) depend on `ValHasType` and stay in
`SourceTinyML/LogicalRelation.lean`.
-/

namespace TinyML

/-- Generate SMT formulas for a primitive TinyML type. -/
def PrimitiveType.typeConstraints (p : PrimitiveType) (t : Term .value) : List Formula :=
  match p with
  | .int => [.unpred .isInt t]
  | .bool => [.unpred .isBool t]
  | .char => [.unpred .isChar t]
  | .string => [.unpred .isStr t]
  | .float => [.unpred .isFloat t]
  | .unit => []

mutual
/-- Generate SMT formulas asserting that a value-sorted term has a given TinyML type.
    For `int`: `is-of_int(t)`, for `bool`: `is-of_bool(t)`,
    for `tuple ts`: `is-of_tuple(t)` plus recursive constraints on elements. -/
def typeConstraints (ty : TinyML.Typ) (t : Term .value) : List Formula :=
  match ty with
  | .prim p => p.typeConstraints t
  | .owned _ => [.unpred .isLoc t]
  | .array _ =>
      [.binpred .le (.const (.i 0)) (.unop .arrayLengthOf t)]
  | .ownedArray _ =>
      [.binpred .le (.const (.i 0)) (.unop .arrayLengthOf t)]
  | .vec _ =>
      [.unpred .isVec t,
       .binpred .le (.const (.i 0)) (.unop .vecLen (.unop .toVec t))]
  | .tuple ts =>
      .unpred .isTuple t ::
      typeConstraintsList ts (.unop .toValList t)
  | _ => []

def typeConstraintsList (ts : List TinyML.Typ) (tl : Term .vallist) : List Formula :=
    match ts with
    | [] => []
    | ty :: rest =>
        typeConstraints ty (.unop .vhead tl) ++
        typeConstraintsList rest (.unop .vtail tl)
end

/-- Quantify a single element constraint over the in-bounds integer indices of
`contents`, triggered by the selected `vecGet` term. -/
def elementConstraint (contents : Term .value) (name : String)
    (constraint : Formula) : Formula :=
  let i : Term .int := .var .int name
  let elem : Term .value := .binop .vecGet (.unop .toVec contents) i
  let bounds := Formula.and
    (.binpred .le (.const (.i 0)) i)
    (.binpred .lt i (.unop .vecLen (.unop .toVec contents)))
  .forall_ name .int [.term elem] (.implies bounds constraint)

/-- Generate bounded element-type constraints for a vector snapshot. Each
ordinary constraint becomes a quantified implication over in-bounds integer
indices, triggered by the selected `vecGet` term. -/
def elementConstraints (ty : TinyML.Typ) (contents : Term .value) : List Formula :=
  let name := Fresh.freshName contents.names "i"
  let elem : Term .value := .binop .vecGet (.unop .toVec contents) (.var .int name)
  (TinyML.typeConstraints ty elem).map (elementConstraint contents name)

end TinyML
