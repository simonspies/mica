-- SUMMARY: First-order constraint formulas asserting that a term has a given TinyML type.
import Mica.SourceTinyML.Types
import Mica.FOL.Formulas
import Mica.Base.Fresh

/-!
# SMT type constraints

Formulas encoding `ValHasType` checks as first-order constraints. The
generators need only `TinyML.Typ` and the FOL term/formula language, so they sit
*below* typing, which lets elaboration emit them directly.
-/

namespace TinyML

/-- Generate SMT formulas for a primitive TinyML type. -/
def PrimitiveType.typeConstraints (p : PrimitiveType) (t : Term .value) : List Formula :=
  match p with
  | .int => [.unpred .isInt t]
  | .int32 => [.unpred .isInt32 t]
  | .int64 => [.unpred .isInt64 t]
  | .bool => [.unpred .isBool t]
  | .char => [.unpred .isChar t]
  | .string => [.unpred .isStr t]
  | .float => [.unpred .isFloat t]
  | .unit => [.eq .value t (.const .unit)]

/-- Primitive type constraints only reference free variables of the constrained term. -/
theorem PrimitiveType.typeConstraints_wfIn {p : PrimitiveType} {t : Term .value} {Δ : Signature}
    (ht : t.wfIn Δ) : ∀ φ ∈ p.typeConstraints t, φ.wfIn Δ := by
  cases p <;>
    simp only [PrimitiveType.typeConstraints, List.mem_singleton, forall_eq] <;>
    refine ⟨?_, ?_⟩ <;> first | exact ht | trivial

/-- The first `ts.length` elements of `tl`. -/
def components (ts : List TinyML.Typ) (tl : Term .vallist) : Term .vallist :=
  match ts with
  | [] => .const .vnil
  | _ :: rest => .binop .vcons (.unop .vhead tl) (components rest (.unop .vtail tl))

theorem components_wfIn {ts : List TinyML.Typ} {tl : Term .vallist} {Δ : Signature}
    (htl : tl.wfIn Δ) : (components ts tl).wfIn Δ := by
  induction ts generalizing tl with
  | nil => simp [components, Term.wfIn, Const.wfIn]
  | cons _ rest ih =>
    exact ⟨trivial, ⟨trivial, htl⟩, ih (by simp only [Term.wfIn]; exact ⟨trivial, htl⟩)⟩

/-- On a list with one element per type, `components` is the identity. -/
theorem components_eval {ts : List TinyML.Typ} {tl : Term .vallist} {ρ : Env}
    {vs : List Runtime.Val} (htl : tl.eval ρ = vs) (hlen : vs.length = ts.length) :
    (components ts tl).eval ρ = vs := by
  induction ts generalizing tl vs with
  | nil =>
    cases vs with
    | nil => simp [components, Term.eval]
    | cons _ _ => simp at hlen
  | cons _ rest ih =>
    cases vs with
    | nil => simp at hlen
    | cons v vs' =>
      have htail : (Term.unop UnOp.vtail tl).eval ρ = vs' := by
        simp [Term.eval, UnOp.eval, htl]
      simp only [components, Term.eval, BinOp.eval, UnOp.eval, htl, List.headD_cons,
        ih htail (by simpa using hlen)]

mutual
/-- Generate SMT formulas asserting that a value-sorted term has a given TinyML type.
    For `int`: `is-of_int(t)`, for `bool`: `is-of_bool(t)`,
    for `tuple ts`: `is-of_tuple(t)`, `t = of_tuple(components ts (to_tuple t))`,
    and recursive constraints on elements.
    The equation for tuples and the one for `unit` say that a value has no other
    content. Without them, the solver cannot prove that a `match` which rebuilds
    its argument returns an equal value. -/
def typeConstraints (ty : TinyML.Typ) (t : Term .value) : List Formula :=
  match ty with
  | .prim p => p.typeConstraints t
  | .owned _ => [.unpred .isLoc t]
  | .array _ =>
      [.binpred .le (.const (.i 0)) (.unop .arrayLen t)]
  | .ownedArray _ =>
      [.binpred .le (.const (.i 0)) (.unop .arrayLen t)]
  | .vec _ =>
      [.unpred .isVec t,
       .binpred .le (.const (.i 0)) (.unop .vecLen (.unop .toVec t))]
  | .tuple ts =>
      .unpred .isTuple t ::
      .eq .value t (.unop .ofValList (components ts (.unop .toValList t))) ::
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



mutual
  /-- All formulas in `typeConstraints ty t` only reference free variables of `t`. -/
  theorem typeConstraints_wfIn {ty : TinyML.Typ} {t : Term .value} {Δ : Signature}
      (ht : t.wfIn Δ) : ∀ φ ∈ typeConstraints ty t, φ.wfIn Δ := by
    cases ty with
    | prim p =>
      simpa [typeConstraints] using PrimitiveType.typeConstraints_wfIn (p := p) ht
    | owned _ =>
      simp [typeConstraints]
      simp only [Formula.wfIn]; exact ⟨trivial, ht⟩
    | array _ | ownedArray _ =>
      simp only [typeConstraints, List.mem_cons, List.not_mem_nil]
      intro φ hφ
      rcases hφ with rfl | hfalse
      · simp only [Formula.wfIn, Term.wfIn]; exact ⟨trivial, trivial, ⟨trivial, ht⟩⟩
      · cases hfalse
    | vec _ =>
      simp only [typeConstraints, List.mem_cons, List.not_mem_nil]
      intro φ hφ
      rcases hφ with rfl | rfl | hfalse
      · simp only [Formula.wfIn]; exact ⟨trivial, ht⟩
      · simp only [Formula.wfIn, Term.wfIn]; exact ⟨trivial, trivial, ⟨trivial, ⟨trivial, ht⟩⟩⟩
      · cases hfalse
    | tuple ts =>
      have htl : (Term.unop UnOp.toValList t).wfIn Δ := by
        simp only [Term.wfIn]; exact ⟨trivial, ht⟩
      simp only [typeConstraints]
      intro φ hφ
      cases hφ with
      | head =>
        simp only [Formula.wfIn]; exact ⟨trivial, ht⟩
      | tail _ hφ =>
        cases hφ with
        | head =>
          simp only [Formula.wfIn]
          exact ⟨ht, trivial, components_wfIn htl⟩
        | tail _ hφ =>
          exact typeConstraintsList_wfIn htl φ hφ
    | _ => simp [typeConstraints]

  theorem typeConstraintsList_wfIn {ts : List TinyML.Typ} {tl : Term .vallist} {Δ : Signature}
      (htl : tl.wfIn Δ) : ∀ φ ∈ typeConstraintsList ts tl, φ.wfIn Δ := by
    cases ts with
    | nil => simp [typeConstraintsList]
    | cons ty rest =>
      simp only [typeConstraintsList]
      intro φ hφ
      cases List.mem_append.mp hφ with
      | inl h =>
        exact typeConstraints_wfIn (by simp only [Term.wfIn]; exact ⟨trivial, htl⟩) φ h
      | inr h =>
        exact typeConstraintsList_wfIn (by simp only [Term.wfIn]; exact ⟨trivial, htl⟩) φ h

  /-- Bounded vector-element constraints are well-formed whenever the snapshot
  term is well-formed. -/
  theorem elementConstraints_wfIn {ty : TinyML.Typ} {contents : Term .value}
      {Δ : Signature} (hcontents : contents.wfIn Δ) :
      ∀ φ ∈ elementConstraints ty contents, φ.wfIn Δ := by
    intro φ hφ
    simp only [elementConstraints, List.mem_map] at hφ
    obtain ⟨constraint, hconstraint, rfl⟩ := hφ
    let name := Fresh.freshName contents.names "i"
    have hname : name ∉ contents.names := Fresh.freshName_not_in_avoid contents.names "i"
    have hcontents' : contents.wfIn (Δ.declVar ⟨name, .int⟩) :=
      Term.wfIn_declVar_of_fresh hcontents hname
    have hi : (Term.var .int name).wfIn (Δ.declVar ⟨name, .int⟩) := by
      refine ⟨Signature.var_mem_declVar Δ ⟨name, .int⟩, ?_, ?_⟩
      · intro τ hconst
        simp [Signature.declVar, Signature.addVar, Signature.remove] at hconst
      · intro τ hvar
        simpa [Signature.declVar, Signature.addVar, Signature.remove] using hvar
    have helem : (Term.binop .vecGet (.unop .toVec contents) (.var .int name)).wfIn
        (Δ.declVar ⟨name, .int⟩) := ⟨trivial, ⟨trivial, hcontents'⟩, hi⟩
    have hconstraint' := typeConstraints_wfIn helem constraint hconstraint
    simp only [elementConstraint]
    change
      Pattern.List.wfIn
          [.term (.binop .vecGet (.unop .toVec contents) (.var .int name))]
          (Δ.declVar ⟨name, .int⟩) ∧
        (Formula.implies
          (.and
            (.binpred .le (.const (.i 0)) (.var .int name))
            (.binpred .lt (.var .int name) (.unop .vecLen (.unop .toVec contents))))
          constraint).wfIn (Δ.declVar ⟨name, .int⟩)
    constructor
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst p
      exact helem
    · exact
        ⟨⟨⟨trivial, trivial, hi⟩,
            ⟨trivial, hi, ⟨trivial, ⟨trivial, hcontents'⟩⟩⟩⟩,
          hconstraint'⟩
end


end TinyML
