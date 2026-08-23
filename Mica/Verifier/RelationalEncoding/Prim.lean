-- SUMMARY: Encoding of intrinsic applications, driven by an explicit table of primitive encodings.
import Mica.Base.Arity
import Mica.FOL.Formulas

namespace Verifier.RelationalEncoding

/-! ## The primitive encoding table -/

/-- One named primitive encoding. It tells the encoder how to make a value
    term from a saturated application of an intrinsic. This structure holds
    data only. `PrimEncoding.Lawful` gives the laws that the relational
    encoder requires of an entry. -/
structure PrimEncoding where
  /-- The name of the intrinsic that this entry encodes. `encodePrim` uses
      this name as the search key. -/
  name : String
  /-- The number of arguments that the encoding expects. -/
  arity : Arity
  /-- True if you can use the encoding in the signature. An entry that
      applies a declared symbol needs that declaration. An entry that builds
      a term without a symbol does not. -/
  available : Signature → Bool
  /-- Make the value term for a saturated application. `encodePrim` checks
      the number of arguments. Therefore the arguments arrive as a tuple. -/
  encode : Signature → Arity.tup arity (Term .value) → Term .value

/-- The laws that the relational encoder requires of a table entry. -/
structure PrimEncoding.Lawful (e : PrimEncoding) : Prop where
  /-- Let the encoding be available in `Δ`. Let `Δ'` extend `Δ`. If the
      arguments are well-formed in `Δ'`, then the term is also well-formed
      in `Δ'`. -/
  wfIn : ∀ {Δ Δ' : Signature} {args : Arity.tup e.arity (Term .value)},
    e.available Δ = true → Δ.Subset Δ' → Δ'.wf →
    Arity.All (·.wfIn Δ') e.arity args → (e.encode Δ args).wfIn Δ'
  /-- The encoding is a pure function of the values of its arguments. Let two
      environments agree on `Δ`. If each pair of arguments evaluates to the
      same value, then the two terms also evaluate to the same value. -/
  eval : ∀ {Δ : Signature} {args₁ args₂ : Arity.tup e.arity (Term .value)}
      {ρ₁ ρ₂ : Env},
    e.available Δ = true → Env.agreeOn Δ ρ₁ ρ₂ →
    Arity.map (Term.eval ρ₁) e.arity args₁ = Arity.map (Term.eval ρ₂) e.arity args₂ →
    Term.eval ρ₁ (e.encode Δ args₁) = Term.eval ρ₂ (e.encode Δ args₂)

/-- The primitive table of the encoder. It holds one entry for each
    intrinsic that the encoder can encode. -/
abbrev PrimEncodings := List PrimEncoding

/-- A table is lawful if each of its entries is lawful. -/
def PrimEncodings.Lawful (primitives : PrimEncodings) : Prop :=
  ∀ e ∈ primitives, e.Lawful

/-- Find the encoding for a name. This is the first entry with that `name`. -/
def PrimEncodings.lookup? (primitives : PrimEncodings) (name : String) : Option PrimEncoding :=
  primitives.find? (·.name == name)

/-- An encoding that the table returns is an entry of that table. -/
theorem PrimEncodings.mem_of_lookup? {primitives : PrimEncodings} {name : String}
    {e : PrimEncoding} (h : primitives.lookup? name = some e) : e ∈ primitives :=
  List.mem_of_find?_eq_some h

/-- An entry that a lawful table returns is itself lawful. -/
theorem PrimEncodings.Lawful.lookup? {primitives : PrimEncodings} (hlaw : primitives.Lawful)
    {name : String} {e : PrimEncoding} (h : primitives.lookup? name = some e) : e.Lawful :=
  hlaw e (PrimEncodings.mem_of_lookup? h)

/-! ## Intrinsic application encoder -/

/-- Encode a saturated intrinsic application with the primitive table. This
function makes the two checks that all entries share. It checks that the
table holds the name. It also checks that the application has the arity of
the entry. Therefore an entry only makes a term from an argument tuple. -/
def encodePrim (primitives : PrimEncodings) (Δ : Signature) (name : String)
    (vs : List (Term .value)) : Except String (Term .value) :=
  match primitives.lookup? name with
  | none => .error s!"relational encoding: unknown intrinsic `{name}`"
  | some encoding =>
      if hlen : vs.length = encoding.arity.toNat then
        if encoding.available Δ then
          .ok (encoding.encode Δ (Arity.ofList encoding.arity vs hlen))
        else .error s!"relational encoding: unavailable intrinsic `{name}`"
      else .error s!"relational encoding: intrinsic `{name}` applied at unsupported arity"

/-- A successful encoding is well-formed in each extension of the signature.
The encoding is available in the base signature `Δ`. The `wfIn` law of the
entry then gives well-formedness in `Δ'`. -/
theorem encodePrim_wfIn {primitives : PrimEncodings} {Δ Δ' : Signature}
    {n : String} {vs : List (Term .value)} {v : Term .value}
    (hlaw : primitives.Lawful) (h : encodePrim primitives Δ n vs = .ok v)
    (hsub : Δ.Subset Δ') (hΔ' : Δ'.wf)
    (hvs : ∀ w ∈ vs, w.wfIn Δ') : v.wfIn Δ' := by
  unfold encodePrim at h
  split at h
  · simp at h
  · rename_i encoding hlookup
    split at h
    · rename_i hlen
      split at h
      · rename_i hav
        simp only [Except.ok.injEq] at h
        subst v
        exact (hlaw.lookup? hlookup).wfIn (by simpa using hav) hsub hΔ'
          (Arity.ofList_all encoding.arity vs hlen hvs)
      · simp at h
    · simp at h

/-- The success of `encodePrim` depends on the name, the signature, and the
number of arguments. It does not depend on the argument terms. Therefore two
argument lists of the same length both succeed. -/
theorem encodePrim_ok_irrel {primitives : PrimEncodings} {Δ : Signature} {n : String}
    {vs vs' : List (Term .value)} {v : Term .value}
    (h : encodePrim primitives Δ n vs = .ok v) (hlen : vs'.length = vs.length) :
    ∃ v', encodePrim primitives Δ n vs' = .ok v' := by
  unfold encodePrim at h ⊢
  split at h
  · simp at h
  · split at h
    · rename_i hvs
      rw [dif_pos (hlen.trans hvs)]
      split at h
      · rename_i hav
        rw [if_pos hav]
        exact ⟨_, rfl⟩
      · simp at h
    · simp at h

/-- The failure of `encodePrim` depends on the same three things. Therefore
two argument lists of the same length fail with the same message. -/
theorem encodePrim_error_irrel {primitives : PrimEncodings} {Δ : Signature} {n : String}
    {vs vs' : List (Term .value)} {msg : String}
    (h : encodePrim primitives Δ n vs = .error msg) (hlen : vs'.length = vs.length) :
    encodePrim primitives Δ n vs' = .error msg := by
  unfold encodePrim at h ⊢
  split at h
  · exact h
  · split at h
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

/-- `encodePrim` is a pure function of the values of its arguments. Let two
environments agree on the signature `Δ`. If each pair of arguments evaluates
to the same value, then the two results also evaluate to the same value. -/
theorem encodePrim_eval {primitives : PrimEncodings} {Δ : Signature} {n : String}
    {vs₁ vs₂ : List (Term .value)} {v₁ v₂ : Term .value} {ρ₁ ρ₂ : Env}
    (hlaw : primitives.Lawful)
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
          exact (hlaw.lookup? hlookup).eval (by simpa using hav) hagree
            (Arity.map_ofList_eq _ _ encoding.arity vs₁ vs₂ hlen₁ hlen₂ hvals)
        · simp at h₂
      · simp at h₁
    · simp at h₁

end Verifier.RelationalEncoding
