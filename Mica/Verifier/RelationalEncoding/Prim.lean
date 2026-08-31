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

end Verifier.RelationalEncoding
