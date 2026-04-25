-- SUMMARY: Auxiliary lemmas for reasoning about successful computations in the `Except` monad.
-- Base/Except.lean — Auxiliary lemmas for Except

namespace Except

theorem bind_ok {ε α β} {a : Except ε α} {f : α → Except ε β} {b : β}
    (h : (a >>= f) = .ok b) :
    ∃ x, a = .ok x ∧ f x = .ok b := by
  cases a with
  | error e =>
    simp [bind, Except.bind] at h
  | ok x =>
    exact ⟨x, rfl, h⟩

end Except
