-- SUMMARY: Generic intrinsic application encoding from an explicit table of primitive encodings.
import Mica.FOL.Formulas

namespace Verifier.RelationalEncoding

/-- One named primitive encoding and the structural laws required by the
    relational encoder. The shared wrapper checks arity and availability;
    entries only construct terms and justify their solver semantics. -/
structure PrimEncoding where
  name : String
  arity : Nat
  available : Signature → Bool
  encode : (Δ : Signature) → (vs : List (Term .value)) →
    vs.length = arity → Term .value
  wfIn : ∀ {Δ Δ' : Signature} {vs : List (Term .value)}
      (hlen : vs.length = arity),
    available Δ = true → Δ.Subset Δ' → Δ'.wf →
      (∀ w ∈ vs, w.wfIn Δ') → (encode Δ vs hlen).wfIn Δ'
  eval : ∀ {Δ : Signature} {vs₁ vs₂ : List (Term .value)}
      (hlen₁ : vs₁.length = arity) (hlen₂ : vs₂.length = arity) {ρ₁ ρ₂ : Env},
    available Δ = true → Env.agreeOn Δ ρ₁ ρ₂ →
    vs₁.map (fun t => Term.eval ρ₁ t) = vs₂.map (fun t => Term.eval ρ₂ t) →
      Term.eval ρ₁ (encode Δ vs₁ hlen₁) = Term.eval ρ₂ (encode Δ vs₂ hlen₂)

abbrev PrimEncodings := List PrimEncoding

def PrimEncodings.lookup? (primitives : PrimEncodings) (name : String) : Option PrimEncoding :=
  primitives.find? (·.name == name)

/-- Encode a saturated intrinsic application from the explicit primitive table. -/
def encodePrim (primitives : PrimEncodings) (Δ : Signature) (name : String)
    (vs : List (Term .value)) : Except String (Term .value) :=
  match primitives.lookup? name with
  | none => .error s!"relational encoding: unknown intrinsic `{name}`"
  | some encoding =>
      if hlen : vs.length = encoding.arity then
        if encoding.available Δ then .ok (encoding.encode Δ vs hlen)
        else .error s!"relational encoding: unavailable intrinsic `{name}`"
      else .error s!"relational encoding: intrinsic `{name}` applied at unsupported arity"

theorem encodePrim_wfIn {primitives : PrimEncodings} {Δ Δ' : Signature}
    {n : String} {vs : List (Term .value)} {v : Term .value}
    (h : encodePrim primitives Δ n vs = .ok v)
    (hsub : Δ.Subset Δ') (hΔ' : Δ'.wf)
    (hvs : ∀ w ∈ vs, w.wfIn Δ') : v.wfIn Δ' := by
  unfold encodePrim at h
  split at h
  · simp at h
  · split at h
    · rename_i encoding _ hlen
      split at h
      · rename_i hav
        simp only [Except.ok.injEq] at h
        subst v
        exact encoding.wfIn hlen (by simpa using hav) hsub hΔ' hvs
      · simp at h
    · simp at h

theorem encodePrim_ok_irrel {primitives : PrimEncodings} {Δ : Signature} {n : String}
    {vs vs' : List (Term .value)} {v : Term .value}
    (h : encodePrim primitives Δ n vs = .ok v) (hlen : vs'.length = vs.length) :
    ∃ v', encodePrim primitives Δ n vs' = .ok v' := by
  unfold encodePrim at h ⊢
  split at h
  · simp at h
  · rename_i encoding hlookup
    split at h
    · rename_i hvs
      rw [dif_pos (hlen.trans hvs)]
      split at h
      · rename_i hav
        rw [if_pos hav]
        exact ⟨_, rfl⟩
      · simp at h
    · simp at h

theorem encodePrim_error_irrel {primitives : PrimEncodings} {Δ : Signature} {n : String}
    {vs vs' : List (Term .value)} {msg : String}
    (h : encodePrim primitives Δ n vs = .error msg) (hlen : vs'.length = vs.length) :
    encodePrim primitives Δ n vs' = .error msg := by
  unfold encodePrim at h ⊢
  split at h
  · exact h
  · rename_i encoding hlookup
    split at h
    · rename_i hvs
      rw [dif_pos (hlen.trans hvs)]
      split at h
      · simp at h
      · rename_i hav
        rw [if_neg hav]
        exact h
    · rename_i hvs
      rw [dif_neg (fun hvs' => hvs (hlen.symm.trans hvs'))]
      exact h

theorem encodePrim_eval {primitives : PrimEncodings} {Δ : Signature} {n : String}
    {vs₁ vs₂ : List (Term .value)} {v₁ v₂ : Term .value} {ρ₁ ρ₂ : Env}
    (h₁ : encodePrim primitives Δ n vs₁ = .ok v₁)
    (h₂ : encodePrim primitives Δ n vs₂ = .ok v₂)
    (hagree : Env.agreeOn Δ ρ₁ ρ₂)
    (hvals : vs₁.map (fun t => Term.eval ρ₁ t) = vs₂.map (fun t => Term.eval ρ₂ t)) :
    Term.eval ρ₁ v₁ = Term.eval ρ₂ v₂ := by
  unfold encodePrim at h₁ h₂
  split at h₁
  · simp at h₁
  · rename_i encoding hlookup
    simp only [hlookup] at h₂
    split at h₁
    · rename_i hlen₁
      split at h₁
      · rename_i hav
        split at h₂
        · rename_i hlen₂
          simp only [Except.ok.injEq] at h₁ h₂
          subst v₁
          subst v₂
          exact encoding.eval hlen₁ hlen₂ (by simpa using hav) hagree hvals
        · simp at h₂
      · simp at h₁
    · simp at h₁

end Verifier.RelationalEncoding
