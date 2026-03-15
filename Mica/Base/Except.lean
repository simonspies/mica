-- Base/Except.lean — Auxiliary lemmas for Except

theorem bind_ok {a : Except String Unit} {f : Unit → Except String Unit}
    (h : (a >>= f) = .ok ()) : a = .ok () ∧ f () = .ok () := by
  cases a with
  | error e => simp [bind, Except.bind] at h
  | ok u => cases u; exact ⟨rfl, h⟩
