-- SUMMARY: Heap operations and basic facts for TinyML runtime locations and values.
import Mathlib.Data.Finmap
import Mica.TinyML.RuntimeExpr

namespace TinyML

abbrev Heap := Finmap (fun _ : Runtime.Location => Runtime.Val)

namespace Heap

def lookup (l : Runtime.Location) (μ : Heap) : Option Runtime.Val := Finmap.lookup l μ
def update (l : Runtime.Location) (v : Runtime.Val) (μ : Heap) : Heap := μ.insert l v
def dom    (μ : Heap) : Finset Runtime.Location := μ.keys
def Fresh  (l : Runtime.Location) (μ : Heap) : Prop := l ∉ μ.dom

theorem lookup_update_eq (μ : Heap) (l : Runtime.Location) (v : Runtime.Val) :
    (μ.update l v).lookup l = some v := by
  simp [lookup, update, Finmap.lookup_insert]

theorem lookup_update_ne (μ : Heap) (l l' : Runtime.Location) (v : Runtime.Val) (h : l ≠ l') :
    (μ.update l v).lookup l' = μ.lookup l' := by
  simp [lookup, update, Finmap.lookup_insert_of_ne _ h.symm]

theorem lookup_fresh (μ : Heap) (l : Runtime.Location) (h : μ.Fresh l) :
    μ.lookup l = none := by
  simp [Fresh, dom, lookup] at *
  exact Finmap.lookup_eq_none.mpr h

theorem update_dom (μ : Heap) (l : Runtime.Location) (v : Runtime.Val) :
    (μ.update l v).dom = μ.dom ∪ {l} := by
  ext a
  simp [dom, update, Finmap.mem_keys, Finmap.mem_insert]

end Heap
end TinyML
