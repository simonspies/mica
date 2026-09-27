-- SUMMARY: Removal of every entry under a key from an association list.

namespace List

/-- `l` without any of its entries under `k`. -/
def removeKey [BEq α] (l : List (α × β)) (k : α) : List (α × β) :=
  l.filter fun p => p.1 != k

@[simp] theorem lookup_removeKey [BEq α] [LawfulBEq α] (l : List (α × β)) (k k' : α) :
    (l.removeKey k).lookup k' = if k' == k then none else l.lookup k' := by
  induction l with
  | nil => simp [removeKey]
  | cons p l ih =>
    obtain ⟨z, v⟩ := p
    by_cases hzk : z = k
    · subst hzk
      have hl : ((z, v) :: l).removeKey z = l.removeKey z := by simp [removeKey]
      rw [hl, ih]
      by_cases hk'z : k' = z
      · simp [hk'z]
      · have hb : (k' == z) = false := by simpa using hk'z
        simp only [List.lookup, hb]
    · have hl : ((z, v) :: l).removeKey k = (z, v) :: l.removeKey k := by
        simp [removeKey, hzk]
      rw [hl]
      by_cases hk'z : k' = z
      · subst hk'z
        have hb : (k' == k) = false := by simpa using hzk
        simp [List.lookup, hb]
      · have hb : (k' == z) = false := by simpa using hk'z
        simp only [List.lookup, hb, ih]

theorem mem_of_mem_removeKey [BEq α] {l : List (α × β)} {k : α} {p : α × β}
    (h : p ∈ l.removeKey k) : p ∈ l :=
  (List.mem_filter.mp h).1

end List
