-- SUMMARY: Encoding of saturated intrinsic applications into FOL terms, with well-formedness, arity-irrelevance, and evaluation lemmas.
import Mica.FOL.Formulas

namespace Verifier.RelationalEncoding

/-! ## Intrinsic application encoder -/

/-- Encode an intrinsic application `n vs` into a value-sorted FOL
term over the intrinsic's uninterpreted symbol. The symbol must already be
declared in the encoding signature `Δ` at the arity implied by the argument
count. -/
def encodePrim (Δ : Signature) (n : String) :
    List (Term .value) → Except String (Term .value)
  | [] =>
    if (⟨n, .value⟩ : FOL.Const) ∈ Δ.consts then
      .ok (.const (.uninterpreted n .value))
    else .error s!"relational encoding: unknown nullary intrinsic `{n}`"
  | [a] =>
    if (⟨n, .value, .value⟩ : FOL.Unary) ∈ Δ.unary then
      .ok (.unop (.uninterpreted n .value .value) a)
    else .error s!"relational encoding: unknown unary intrinsic `{n}`"
  | [a, b] =>
    if (⟨n, .value, .value, .value⟩ : FOL.Binary) ∈ Δ.binary then
      .ok (.binop (.uninterpreted n .value .value .value) a b)
    else .error s!"relational encoding: unknown binary intrinsic `{n}`"
  | _ => .error s!"relational encoding: intrinsic `{n}` applied at unsupported arity"

/-- A successful intrinsic encoding is well-formed in any extension of the
signature. The intrinsic symbol's membership is established at the base
signature `Δ` and lifted to `Δ'`; the freshness and
uniqueness side conditions of `wfIn` follow from `Δ'.wf`. -/
theorem encodePrim_wfIn {Δ Δ' : Signature} {n : String} {vs : List (Term .value)}
    {v : Term .value} (h : encodePrim Δ n vs = .ok v)
    (hsub : Δ.Subset Δ') (hΔ' : Δ'.wf)
    (hvs : ∀ w ∈ vs, w.wfIn Δ') : v.wfIn Δ' := by
  cases vs with
  | nil =>
    simp only [encodePrim] at h
    split at h
    · rename_i hmem
      simp only [Except.ok.injEq] at h; subst h
      have hmem' : (⟨n, .value⟩ : FOL.Const) ∈ Δ'.consts := hsub.consts _ hmem
      exact ⟨hmem', fun τ' hv => Signature.wf_no_var_of_const hΔ' hmem' hv,
        fun τ' hc => Signature.wf_unique_const hΔ' hmem' hc⟩
    · simp at h
  | cons a tl =>
    cases tl with
    | nil =>
      simp only [encodePrim] at h
      split at h
      · rename_i hmem
        simp only [Except.ok.injEq] at h; subst h
        have hmem' : (⟨n, .value, .value⟩ : FOL.Unary) ∈ Δ'.unary := hsub.unary _ hmem
        exact ⟨⟨hmem', fun τ' hrel => Signature.wf_no_unaryRel_of_unary hΔ' hmem' hrel,
            fun τ₁' τ₂' hu => Signature.wf_unique_unary hΔ' hmem' hu⟩,
          hvs a (by simp)⟩
      · simp at h
    | cons b tl2 =>
      cases tl2 with
      | nil =>
        simp only [encodePrim] at h
        split at h
        · rename_i hmem
          simp only [Except.ok.injEq] at h; subst h
          have hmem' : (⟨n, .value, .value, .value⟩ : FOL.Binary) ∈ Δ'.binary :=
            hsub.binary _ hmem
          exact ⟨⟨hmem', fun τ₁' τ₂' hrel => Signature.wf_no_binaryRel_of_binary hΔ' hmem' hrel,
              fun τ₁' τ₂' τ₃' hb => Signature.wf_unique_binary hΔ' hmem' hb⟩,
            hvs a (by simp), hvs b (by simp)⟩
        · simp at h
      | cons c tl3 =>
        simp [encodePrim] at h

/-- The success of `encodePrim` depends only on the name, signature, and
argument count, not the argument terms: equal-length argument lists succeed
together. -/
theorem encodePrim_ok_irrel {Δ : Signature} {n : String}
    {vs vs' : List (Term .value)} {v : Term .value}
    (h : encodePrim Δ n vs = .ok v) (hlen : vs'.length = vs.length) :
    ∃ v', encodePrim Δ n vs' = .ok v' := by
  cases vs with
  | nil =>
      cases vs' with
      | nil => exact ⟨v, h⟩
      | cons a' tl' =>
          cases tl' with
          | nil => simp at hlen
          | cons b' tl2' =>
              cases tl2' <;> simp at hlen
  | cons a tl =>
      cases tl with
      | nil =>
          cases vs' with
          | nil => simp at hlen
          | cons a' tl' =>
              cases tl' with
              | nil =>
                  simp only [encodePrim] at h ⊢
                  split at h <;> simp_all
              | cons b' tl2' =>
                  cases tl2' <;> simp at hlen
      | cons b tl2 =>
          cases tl2 with
          | nil =>
              cases vs' with
              | nil => simp at hlen
              | cons a' tl' =>
                  cases tl' with
                  | nil => simp at hlen
                  | cons b' tl2' =>
                      cases tl2' with
                      | nil =>
                          simp only [encodePrim] at h ⊢
                          split at h <;> simp_all
                      | cons c' rest => simp at hlen
          | cons c rest =>
              simp [encodePrim] at h

/-- The failure of `encodePrim` likewise depends only on the name, signature,
and argument count: equal-length argument lists fail with the same message. -/
theorem encodePrim_error_irrel {Δ : Signature} {n : String}
    {vs vs' : List (Term .value)} {msg : String}
    (h : encodePrim Δ n vs = .error msg) (hlen : vs'.length = vs.length) :
    encodePrim Δ n vs' = .error msg := by
  cases vs with
  | nil =>
      cases vs' with
      | nil => exact h
      | cons a' tl' =>
          cases tl' with
          | nil => simp at hlen
          | cons b' tl2' =>
              cases tl2' <;> simp at hlen
  | cons a tl =>
      cases tl with
      | nil =>
          cases vs' with
          | nil => simp at hlen
          | cons a' tl' =>
              cases tl' with
              | nil =>
                  simp only [encodePrim] at h ⊢
                  split at h <;> simp_all
              | cons b' tl2' =>
                  cases tl2' <;> simp at hlen
      | cons b tl2 =>
          cases tl2 with
          | nil =>
              cases vs' with
              | nil => simp at hlen
              | cons a' tl' =>
                  cases tl' with
                  | nil => simp at hlen
                  | cons b' tl2' =>
                      cases tl2' with
                      | nil =>
                          simp only [encodePrim] at h ⊢
                          split at h <;> simp_all
                      | cons c' rest => simp at hlen
          | cons c rest =>
              cases vs' with
              | nil => simp at hlen
              | cons a' tl' =>
                  cases tl' with
                  | nil => simp at hlen
                  | cons b' tl2' =>
                      cases tl2' with
                      | nil => simp at hlen
                      | cons c' rest' =>
                          simp [encodePrim] at h ⊢
                          exact h

/-- `encodePrim` is a pure uninterpreted-symbol application: when the two
environments agree on the signature `Δ` (hence on the intrinsic symbol)
and the argument evaluations agree pointwise, the results evaluate equally. -/
theorem encodePrim_eval {Δ : Signature} {n : String}
    {vs₁ vs₂ : List (Term .value)} {v₁ v₂ : Term .value} {ρ₁ ρ₂ : Env}
    (h₁ : encodePrim Δ n vs₁ = .ok v₁) (h₂ : encodePrim Δ n vs₂ = .ok v₂)
    (hagree : Env.agreeOn Δ ρ₁ ρ₂)
    (hvals : vs₁.map (fun t => Term.eval ρ₁ t) = vs₂.map (fun t => Term.eval ρ₂ t)) :
    Term.eval ρ₁ v₁ = Term.eval ρ₂ v₂ := by
  rcases vs₁ with _ | ⟨a₁, _ | ⟨b₁, r₁⟩⟩
  · -- vs₁ = []  (nullary constant)
    rcases vs₂ with _ | ⟨a₂, t₂⟩
    · simp only [encodePrim] at h₁ h₂
      split at h₁
      · rename_i hmem
        rw [if_pos hmem] at h₂
        simp only [Except.ok.injEq] at h₁ h₂; subst h₁; subst h₂
        simpa [Term.eval, Const.denote] using hagree.2.1 ⟨n, .value⟩ hmem
      · simp at h₁
    · simp at hvals
  · -- vs₁ = [a₁]  (unary)
    rcases vs₂ with _ | ⟨a₂, _ | ⟨b₂, t₂⟩⟩
    · simp at hvals
    · simp only [List.map_cons, List.map_nil, List.cons.injEq] at hvals
      obtain ⟨ha, _⟩ := hvals
      simp only [encodePrim] at h₁ h₂
      split at h₁
      · rename_i hmem
        rw [if_pos hmem] at h₂
        simp only [Except.ok.injEq] at h₁ h₂; subst h₁; subst h₂
        simp only [Term.eval, UnOp.eval]
        rw [hagree.2.2.1 ⟨n, .value, .value⟩ hmem, ha]
      · simp at h₁
    · simp at hvals
  · -- vs₁ = b₁ :: r₁
    rcases r₁ with _ | ⟨c₁, s₁⟩
    · -- vs₁ = [a₁, b₁]  (binary)
      rcases vs₂ with _ | ⟨a₂, _ | ⟨b₂, _ | _⟩⟩ <;> try (exfalso; simp at hvals; done)
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at hvals
      obtain ⟨ha, hb, _⟩ := hvals
      simp only [encodePrim] at h₁ h₂
      split at h₁
      · rename_i hmem
        rw [if_pos hmem] at h₂
        simp only [Except.ok.injEq] at h₁ h₂; subst h₁; subst h₂
        simp only [Term.eval, BinOp.eval]
        rw [hagree.2.2.2.1 ⟨n, .value, .value, .value⟩ hmem, ha, hb]
      · simp at h₁
    · -- vs₁ length ≥ 3: encodePrim errors
      simp [encodePrim] at h₁

end Verifier.RelationalEncoding
