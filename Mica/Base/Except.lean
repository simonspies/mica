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

theorem bind_ok {σ ε α β} {f : StateT σ (Except ε) α} {g : α → StateT σ (Except ε) β}
    {s s' : σ} {b : β} (h : (f >>= g) s = .ok (b, s')) :
    ∃ a s₀, f s = .ok (a, s₀) ∧ g a s₀ = .ok (b, s') := by
  simp only [bind, StateT.bind] at h
  have ⟨p, hf, hg⟩ := Except.bind_ok h
  exact ⟨p.1, p.2, hf, hg⟩

theorem bind_ok₂ {σ₁ σ₂ ε α β}
    {f : StateT σ₁ (StateT σ₂ (Except ε)) α} {g : α → StateT σ₁ (StateT σ₂ (Except ε)) β}
    {s₁ s₁' : σ₁} {s₂ s₂' : σ₂} {b : β}
    (h : (f >>= g) s₁ s₂ = .ok ((b, s₁'), s₂')) :
    ∃ a t₁ t₂, f s₁ s₂ = .ok ((a, t₁), t₂) ∧ g a t₁ t₂ = .ok ((b, s₁'), s₂') := by
  have h' : (f s₁ >>= fun p => g p.1 p.2) s₂ = .ok ((b, s₁'), s₂') := h
  have ⟨p, s₀, hf, hg⟩ := StateT.bind_ok h'
  exact ⟨p.1, p.2, s₀, hf, hg⟩

end StateT
