-- SUMMARY: Auxiliary lemmas for reasoning about successful computations in the `Except` monad and in `StateT` over it.
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

namespace StateT

/-- Destructure a successful `StateT σ (Except ε)` bind: the first computation
succeeded on the incoming state, and the continuation succeeded on the state it
handed on. The `Except` version with one extra existential for the intermediate
state. -/
theorem bind_ok {σ ε α β} {f : StateT σ (Except ε) α} {g : α → StateT σ (Except ε) β}
    {s s' : σ} {b : β} (h : (f >>= g) s = .ok (b, s')) :
    ∃ a s₀, f s = .ok (a, s₀) ∧ g a s₀ = .ok (b, s') := by
  simp only [bind, StateT.bind] at h
  have ⟨p, hf, hg⟩ := Except.bind_ok h
  exact ⟨p.1, p.2, hf, hg⟩

end StateT
