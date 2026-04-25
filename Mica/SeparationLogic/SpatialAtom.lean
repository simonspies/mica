-- SUMMARY: Syntactic spatial atoms and contexts for verifier state, together with their well-formedness conditions and basic operations.
import Mica.FOL.Terms
import Mica.SeparationLogic.Axioms

open Iris Iris.BI

/-! # Spatial Atoms and Contexts (Syntactic)

A `SpatialAtom` is a syntactic ownership item stored in the verifier state.
A `SpatialContext` is a list of such items. We define their well-formedness
and basic operations (insert = cons, lookup+remove), plus interpretation of a
single atom. -/

/-- A syntactic ownership item. Initially, only points-to assertions. -/
inductive SpatialAtom where
  | pointsTo : Term .value → Term .value → SpatialAtom
  deriving DecidableEq

/-- The spatial part of the verifier state: a list of ownership items. -/
abbrev SpatialContext := List SpatialAtom

namespace SpatialAtom

/-- A spatial atom is well-formed in a signature when all terms it mentions are. -/
def wfIn : SpatialAtom → Signature → Prop
  | .pointsTo l v, Δ => l.wfIn Δ ∧ v.wfIn Δ

/-- Well-formedness is stable under signature extension. -/
theorem wfIn_mono {a : SpatialAtom} {Δ Δ' : Signature}
    (h : a.wfIn Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) : a.wfIn Δ' := by
  cases a with
  | pointsTo l v => exact ⟨Term.wfIn_mono l h.1 hsub hwf, Term.wfIn_mono v h.2 hsub hwf⟩

/-- Iris interpretation of a single spatial atom. -/
def interp (ρ : Env) : SpatialAtom → iProp
  | .pointsTo l v => ∃ (loc : Runtime.Location),
      ⌜Term.eval ρ l = .loc loc⌝ ∗ loc ↦ Term.eval ρ v

/-- Congruence for points-to interpretation under equal location and value evaluation. -/
theorem pointsTo_congr {ρ : Env} {l l' v v' : Term .value}
    (hl : Term.eval ρ l = Term.eval ρ l')
    (hv : Term.eval ρ v = Term.eval ρ v') :
    interp ρ (.pointsTo l v) ⊣⊢ interp ρ (.pointsTo l' v') := by
  simp only [interp, hl, hv]
  exact ⟨BIBase.Entails.rfl, BIBase.Entails.rfl⟩

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
