-- SUMMARY: Syntactic spatial atoms and contexts for verifier state, together with their well-formedness conditions and basic operations.
import Mica.FOL.Terms
import Mica.SeparationLogic.Wp
import Mica.SeparationLogic.LogicalRelation
import Mica.TinyML.Types

open Iris Iris.BI

/-! # Spatial Atoms and Contexts (Syntactic)

A `SpatialAtom` is a syntactic ownership item stored in the verifier state.
A `SpatialContext` is a list of such items. We define their well-formedness
and basic operations (insert = cons, lookup+remove), plus interpretation of a
single atom. -/

/-- A syntactic ownership item. -/
inductive SpatialAtom where
  /-- Field `0` of the block at location term `l` holds value term `v`, whose TinyML type is `ty`.
  The interpretation carries the value typing fact as part of the same spatial atom. -/
  | pointsTo : Term .value → Term .value → TinyML.Typ → SpatialAtom
  /-- An owned mutable array and its immutable vector snapshot. -/
  | arrayPointsTo : Term .value → Term .value → TinyML.Typ → SpatialAtom
  deriving DecidableEq

/-- The spatial part of the verifier state: a list of ownership items. -/
abbrev SpatialContext := List SpatialAtom

namespace SpatialAtom

/-- The head constructor of a spatial atom. Both constructors carry a key
term, a value term, and a type, so atoms can be processed generically by
kind. -/
inductive Kind where
  | ref
  | array
  deriving DecidableEq

/-- The atom of a given kind, from its key term, value term, and type. -/
def Kind.atom : Kind → Term .value → Term .value → TinyML.Typ → SpatialAtom
  | .ref => .pointsTo
  | .array => .arrayPointsTo

/-- Human-readable name of an atom kind, for error messages. -/
def Kind.print : Kind → String
  | .ref => "points-to"
  | .array => "owned array"

/-- The kind of an atom. -/
def kind : SpatialAtom → Kind
  | .pointsTo .. => .ref
  | .arrayPointsTo .. => .array

/-- The key term an atom asserts ownership of: the location of a points-to,
the array value of an owned array. -/
def key : SpatialAtom → Term .value
  | .pointsTo l _ _ => l
  | .arrayPointsTo a _ _ => a

/-- The value term stored under an atom's key: the contents of a reference,
the vector snapshot of an owned array. -/
def val : SpatialAtom → Term .value
  | .pointsTo _ v _ => v
  | .arrayPointsTo _ v _ => v

/-- The element type carried by an atom. -/
def ty : SpatialAtom → TinyML.Typ
  | .pointsTo _ _ ty => ty
  | .arrayPointsTo _ _ ty => ty

@[simp] theorem eta (a : SpatialAtom) : a.kind.atom a.key a.val a.ty = a := by
  cases a <;> rfl

/-- A spatial atom is well-formed in a signature when all terms it mentions are. -/
def wfIn : SpatialAtom → Signature → Prop
  | .pointsTo l v _, Δ => l.wfIn Δ ∧ v.wfIn Δ
  | .arrayPointsTo a v _, Δ => a.wfIn Δ ∧ v.wfIn Δ

@[simp] theorem atom_wfIn {k : Kind} {t v : Term .value} {ty : TinyML.Typ} {Δ : Signature} :
    (k.atom t v ty).wfIn Δ ↔ t.wfIn Δ ∧ v.wfIn Δ := by
  cases k <;> exact Iff.rfl

/-- The key term of a well-formed atom is well-formed. -/
theorem wfIn.key {a : SpatialAtom} {Δ : Signature} (h : a.wfIn Δ) : a.key.wfIn Δ := by
  cases a <;> exact h.1

/-- The value term of a well-formed atom is well-formed. -/
theorem wfIn.val {a : SpatialAtom} {Δ : Signature} (h : a.wfIn Δ) : a.val.wfIn Δ := by
  cases a <;> exact h.2

/-- Well-formedness is stable under signature extension. -/
theorem wfIn_mono {a : SpatialAtom} {Δ Δ' : Signature}
    (h : a.wfIn Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) : a.wfIn Δ' := by
  cases a with
  | pointsTo l v _ => exact ⟨Term.wfIn_mono l h.1 hsub hwf, Term.wfIn_mono v h.2 hsub hwf⟩
  | arrayPointsTo a v _ => exact ⟨Term.wfIn_mono a h.1 hsub hwf, Term.wfIn_mono v h.2 hsub hwf⟩

/-- Iris interpretation of a single spatial atom. -/
def interp [MicaGS HasLC.hasLC Sig] (Θ : TinyML.TypeEnv) (ρ : Env) :
    SpatialAtom → iProp
  | .pointsTo l v ty => ∃ (loc : Runtime.Location),
      ⌜Term.eval ρ l = .loc loc⌝ ∗ loc ↦ [Term.eval ρ v] ∗
        TinyML.ValHasType Θ (Term.eval ρ v) ty
  | .arrayPointsTo a v ty => ∃ (loc : Runtime.Location) (vs : List Runtime.Val),
      ⌜Term.eval ρ a = .array vs.length loc⌝ ∗
      ⌜Term.eval ρ v = .vec vs⌝ ∗ loc ↦ vs ∗
        TinyML.ValHasType Θ (.vec vs) (.vec ty)

/-- Congruence of interpretation in the key and value terms, at equal evaluation. -/
theorem congr [MicaGS HasLC.hasLC Sig] (Θ : TinyML.TypeEnv) {ρ : Env} {k : Kind}
    {t t' v v' : Term .value} {ty : TinyML.Typ}
    (ht : Term.eval ρ t = Term.eval ρ t')
    (hv : Term.eval ρ v = Term.eval ρ v') :
    interp Θ ρ (k.atom t v ty) ⊣⊢ interp Θ ρ (k.atom t' v' ty) := by
  cases k <;> simp only [Kind.atom, interp, ht, hv] <;>
    exact ⟨BIBase.Entails.rfl, BIBase.Entails.rfl⟩

/-- Pure formulas implied by an atom's interpretation. They are assumed
alongside the atom whenever it enters the verifier's spatial context. -/
def facts : SpatialAtom → List Formula
  | .pointsTo .. => []
  | .arrayPointsTo a v _ =>
      [.eq .int (.unop .vecLen (.unop .toVec v)) (.unop .arrayLengthOf a)]

/-- The pure facts of a well-formed atom are well-formed. -/
theorem facts_wfIn {a : SpatialAtom} {Δ : Signature} (h : a.wfIn Δ) :
    ∀ φ ∈ a.facts, φ.wfIn Δ := by
  cases a with
  | pointsTo l v ty => simp [facts]
  | arrayPointsTo a v ty =>
    intro φ hφ
    simp only [facts, List.mem_cons, List.not_mem_nil, or_false] at hφ
    subst hφ
    exact ⟨⟨trivial, ⟨trivial, h.2⟩⟩, ⟨trivial, h.1⟩⟩

end SpatialAtom

namespace SpatialContext

/-- A spatial context is well-formed when each of its atoms is. -/
def wfIn (ctx : SpatialContext) (Δ : Signature) : Prop :=
  ∀ a ∈ ctx, a.wfIn Δ

@[simp] theorem wfIn_nil (Δ : Signature) : wfIn ([] : SpatialContext) Δ := by
  intro a ha
  cases ha

@[simp] theorem wfIn_cons (a : SpatialAtom) (ctx : SpatialContext) (Δ : Signature) :
    wfIn (a :: ctx) Δ ↔ a.wfIn Δ ∧ wfIn ctx Δ := by
  constructor
  · intro h
    refine ⟨h a (by simp), ?_⟩
    intro b hb
    exact h b (by simp [hb])
  · intro h b hb
    simp at hb
    rcases hb with rfl | hb
    · exact h.1
    · exact h.2 b hb

/-- Well-formedness is stable under signature extension. -/
theorem wfIn_mono {ctx : SpatialContext} {Δ Δ' : Signature}
    (h : wfIn ctx Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) : wfIn ctx Δ' :=
  fun a ha => SpatialAtom.wfIn_mono (h a ha) hsub hwf

/-- Insert an atom into the context (just cons). -/
abbrev insert (a : SpatialAtom) (ctx : SpatialContext) : SpatialContext := a :: ctx

@[simp] theorem wfIn_insert {a : SpatialAtom} {ctx : SpatialContext} {Δ : Signature} :
    wfIn (insert a ctx) Δ ↔ a.wfIn Δ ∧ wfIn ctx Δ := by
  simp [insert, wfIn_cons]

/-- Remove the atom at index `n`, returning the atom and remaining context. -/
def remove : List SpatialAtom → Nat → Option (SpatialAtom × List SpatialAtom)
  | [],     _     => none
  | a :: Γ, 0     => some (a, Γ)
  | a :: Γ, n + 1 => (remove Γ n).map fun (b, Γ') => (b, a :: Γ')

@[simp] theorem remove_nil (n : Nat) : remove [] n = none := by
  cases n <;> simp [remove]

@[simp] theorem remove_cons_zero (a : SpatialAtom) (Γ : List SpatialAtom) :
    remove (a :: Γ) 0 = some (a, Γ) := rfl

@[simp] theorem remove_cons_succ (a : SpatialAtom) (Γ : List SpatialAtom) (n : Nat) :
    remove (a :: Γ) (n + 1) = (remove Γ n).map fun (b, Γ') => (b, a :: Γ') := rfl

/-- Find the index of the first occurrence of `a` in the context. -/
def find (a : SpatialAtom) : SpatialContext → Option Nat
  | []     => none
  | b :: Γ => if a == b then some 0 else (find a Γ).map (· + 1)

@[simp] theorem find_nil (a : SpatialAtom) : find a [] = none := rfl

theorem find_remove {a : SpatialAtom} {ctx : SpatialContext} {n : Nat}
    (h : find a ctx = some n) :
    ∃ rest, remove ctx n = some (a, rest) := by
  induction ctx generalizing n with
  | nil => simp at h
  | cons b Γ ih =>
    simp only [find] at h
    split at h
    · next heq =>
      simp at h; subst h
      simp [remove, beq_iff_eq.mp heq]
    · next hne =>
      match hm : find a Γ, h with
      | some m, h =>
        simp at h; subst h
        obtain ⟨rest, hr⟩ := ih hm
        exact ⟨b :: rest, by simp [remove, hr]⟩

theorem find_remove_eq {a b : SpatialAtom} {ctx : SpatialContext} {n : Nat} {rest : SpatialContext}
    (hf : find a ctx = some n) (hr : remove ctx n = some (b, rest)) : a = b := by
  obtain ⟨rest', hr'⟩ := find_remove hf
  simp [hr] at hr'; exact hr'.1.symm

/-- Removing an entry from a well-formed context preserves well-formedness of
    both the removed atom and the remaining context. -/
theorem wfIn_remove {ctx : SpatialContext} {Δ : Signature} {n : Nat}
    {a : SpatialAtom} {rest : SpatialContext}
    (hctx : wfIn ctx Δ) (hrem : remove ctx n = some (a, rest)) :
    a.wfIn Δ ∧ wfIn rest Δ := by
  induction ctx generalizing n a rest with
  | nil => simp at hrem
  | cons b ctx ih =>
    cases n with
    | zero =>
      simp [remove] at hrem
      obtain ⟨rfl, rfl⟩ := hrem
      simpa [wfIn_cons] using hctx
    | succ n =>
      have htail : wfIn ctx Δ := (wfIn_cons b ctx Δ).1 hctx |>.2
      have hhead : b.wfIn Δ := (wfIn_cons b ctx Δ).1 hctx |>.1
      simp only [remove_cons_succ] at hrem
      match hr : remove ctx n with
      | none => simp [hr] at hrem
      | some (a', rest') =>
        simp [hr] at hrem
        obtain ⟨rfl, rfl⟩ := hrem
        obtain ⟨ha, hrest⟩ := ih htail hr
        exact ⟨ha, (wfIn_cons b rest' Δ).2 ⟨hhead, hrest⟩⟩

/-- Looking up an atom in a well-formed context yields a well-formed atom. -/
theorem wfIn_find {ctx : SpatialContext} {Δ : Signature} {a : SpatialAtom} {n : Nat}
    (hctx : wfIn ctx Δ) (hfind : find a ctx = some n) : a.wfIn Δ := by
  obtain ⟨rest, hrem⟩ := find_remove hfind
  have := wfIn_remove hctx hrem
  simpa [find_remove_eq hfind hrem] using this.1

end SpatialContext
