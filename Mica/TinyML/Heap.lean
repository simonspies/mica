import Mathlib.Data.Finmap
import Mica.TinyML.Expr

namespace TinyML

abbrev Heap := Finmap (fun _ : Location => Val)

namespace Heap

def lookup (l : Location) (μ : Heap) : Option Val := Finmap.lookup l μ
def update (l : Location) (v : Val)  (μ : Heap) : Heap := μ.insert l v
def dom    (μ : Heap) : Finset Location := μ.keys
def Fresh  (l : Location) (μ : Heap) : Prop := l ∉ μ.dom

theorem lookup_update_eq (μ : Heap) (l : Location) (v : Val) :
    (μ.update l v).lookup l = some v := by
  simp [lookup, update, Finmap.lookup_insert]

theorem lookup_update_ne (μ : Heap) (l l' : Location) (v : Val) (h : l ≠ l') :
    (μ.update l v).lookup l' = μ.lookup l' := by
  simp [lookup, update, Finmap.lookup_insert_of_ne _ h.symm]

theorem fresh_not_lookup (μ : Heap) (l : Location) (h : μ.Fresh l) :
    μ.lookup l = none := by
  simp [Fresh, dom, lookup] at *
  exact Finmap.lookup_eq_none.mpr h

theorem dom_update (μ : Heap) (l : Location) (v : Val) :
    (μ.update l v).dom = μ.dom ∪ {l} := by
  ext a
  simp [dom, update, Finmap.mem_keys, Finmap.mem_insert]

end Heap
end TinyML
