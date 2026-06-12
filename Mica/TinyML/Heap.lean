-- SUMMARY: Heap operations and basic facts for TinyML runtime locations and values.
import Std.Data.ExtTreeMap
import Mathlib.Data.Set.Insert
import Mica.TinyML.RuntimeExpr

namespace TinyML

/-- The finite-map functor underlying the TinyML heap. Shaped as a functor
    (rather than fixing the value type) so it can instantiate iris-lean's
    generic heap resources (`Std.LawfulFiniteMap`). -/
abbrev HeapF := fun V => Std.ExtTreeMap Runtime.Location V compare

abbrev Heap := HeapF Runtime.Val

namespace Heap

def lookup (l : Runtime.Location) (μ : Heap) : Option Runtime.Val := μ[l]?
def update (l : Runtime.Location) (v : Runtime.Val) (μ : Heap) : Heap := μ.insert l v
def dom    (μ : Heap) : Set Runtime.Location := {l | l ∈ μ}
def Fresh  (l : Runtime.Location) (μ : Heap) : Prop := l ∉ μ.dom

theorem lookup_update_eq (μ : Heap) (l : Runtime.Location) (v : Runtime.Val) :
    (μ.update l v).lookup l = some v := by
  simp [lookup, update]

theorem lookup_update_ne (μ : Heap) (l l' : Runtime.Location) (v : Runtime.Val) (h : l ≠ l') :
    (μ.update l v).lookup l' = μ.lookup l' := by
  simp [lookup, update, Std.ExtTreeMap.getElem?_insert, h]

theorem lookup_fresh (μ : Heap) (l : Runtime.Location) (h : μ.Fresh l) :
    μ.lookup l = none := by
  simp only [Fresh, dom, Set.mem_setOf_eq] at h
  simpa [lookup] using h

theorem update_dom (μ : Heap) (l : Runtime.Location) (v : Runtime.Val) :
    (μ.update l v).dom = μ.dom ∪ {l} := by
  ext a
  simp only [dom, update, Set.mem_setOf_eq, Std.ExtTreeMap.mem_insert, Set.mem_union,
    Set.mem_singleton_iff, Std.LawfulEqOrd.compare_eq_iff_eq]
  rw [or_comm]
  exact or_congr_right eq_comm

end Heap
end TinyML
