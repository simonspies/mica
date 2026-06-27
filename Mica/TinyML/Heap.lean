-- SUMMARY: Heap operations and basic facts for TinyML runtime locations and value blocks.
import Std.Data.ExtTreeMap
import Mathlib.Data.Set.Insert
import Mica.TinyML.RuntimeExpr

namespace TinyML

/-- A heap block: the ordered fields stored at a single location. A plain
    `ref` allocates a singleton block; arrays will allocate larger ones. -/
abbrev Block := List Runtime.Val

/-- The finite-map functor underlying the TinyML heap. Shaped as a functor
    (rather than fixing the value type) so it can instantiate iris-lean's
    generic heap resources (`Std.LawfulFiniteMap`). -/
abbrev HeapF := fun V => Std.ExtTreeMap Runtime.Location V compare

/-- The TinyML heap: each location maps to a block of values. -/
abbrev Heap := HeapF Block

namespace Heap

/-- The whole block stored at `l`, if any. -/
def lookup (l : Runtime.Location) (μ : Heap) : Option Block := μ[l]?
/-- Replace the whole block at `l` with `b`. -/
def update (l : Runtime.Location) (b : Block) (μ : Heap) : Heap := μ.insert l b
def dom    (μ : Heap) : Set Runtime.Location := {l | l ∈ μ}
def Fresh  (l : Runtime.Location) (μ : Heap) : Prop := l ∉ μ.dom

/-- Read field `i` of the block at `l`. The offset is `0` for plain references;
    it generalises to array indexing. -/
def lookupField (l : Runtime.Location) (i : Nat) (μ : Heap) : Option Runtime.Val :=
  (μ.lookup l).bind (·[i]?)

/-- Write `v` into field `i` of the block at `l`. The heap is unchanged if `i`
  is out of bounds.  -/
def updateField (l : Runtime.Location) (i : Nat) (v : Runtime.Val) (μ : Heap) : Heap :=
  match μ.lookup l with
  | some b => μ.update l (b.set i v)
  | none   => μ

theorem lookupField_of_lookup {μ : Heap} {l : Runtime.Location} {i : Nat} {b : Block}
    (h : μ.lookup l = some b) : μ.lookupField l i = b[i]? := by
  simp [lookupField, h]

theorem updateField_of_lookup {μ : Heap} {l : Runtime.Location} {i : Nat} {v : Runtime.Val}
    {b : Block} (h : μ.lookup l = some b) :
    μ.updateField l i v = μ.update l (b.set i v) := by
  simp [updateField, h]

theorem lookup_update_eq (μ : Heap) (l : Runtime.Location) (b : Block) :
    (μ.update l b).lookup l = some b := by
  simp [lookup, update]

theorem lookup_update_ne (μ : Heap) (l l' : Runtime.Location) (b : Block) (h : l ≠ l') :
    (μ.update l b).lookup l' = μ.lookup l' := by
  simp [lookup, update, Std.ExtTreeMap.getElem?_insert, h]

theorem lookup_fresh (μ : Heap) (l : Runtime.Location) (h : μ.Fresh l) :
    μ.lookup l = none := by
  simp only [Fresh, dom, Set.mem_setOf_eq] at h
  simpa [lookup] using h

theorem update_dom (μ : Heap) (l : Runtime.Location) (b : Block) :
    (μ.update l b).dom = μ.dom ∪ {l} := by
  ext a
  simp only [dom, update, Set.mem_setOf_eq, Std.ExtTreeMap.mem_insert, Set.mem_union,
    Set.mem_singleton_iff, Std.LawfulEqOrd.compare_eq_iff_eq]
  rw [or_comm]
  exact or_congr_right eq_comm

end Heap
end TinyML
