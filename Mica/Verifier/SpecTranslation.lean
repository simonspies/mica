-- SUMMARY: Translation of one typechecked specification leaf into its FOL value term and definedness condition.
import Mica.SourceTinyML.Spec
import Mica.FOL.Printing
import Mica.Verifier.Assertions
import Mica.Verifier.PredicateTransformers
import Mica.Verifier.RelationalEncoding

/-!
# Spec Translation

Encodes one typed spec leaf into FOL via `encodeWith Skolemize.encoderOps`,
producing a `DefVal` — a value term together with its definedness condition.

The *spine* of a specification is not walked here: `Typed.elabAssert` walks it
once during elaboration, calling `translateLeaf` at each leaf and asserting the
definedness obligation before the value it guards is bound or tested.
-/

namespace SpecTranslation

open Verifier.RelationalEncoding

private abbrev M := Except String

/-- Encode a spec expression into a `DefVal`. -/
def encodeExpr (Δ : Signature) (Γfn : FunCtx) (δ : VarEnv) (e : Typed.Expr) :
    M Skolemize.DefVal :=
  encodeWith Skolemize.encoderOps Δ Γfn δ e (fun v => .ok (Skolemize.DefVal.pure v))

/-- Translate one typechecked spec leaf into its value term and definedness
condition. The encoder environment is the identity over the spec-level names in
scope: `δ` carries real terms only *inside* a leaf — for let-expressions and
match payloads — never across the spine, so the names alone determine it. -/
def translateLeaf (Δ : Signature) (Γfn : FunCtx) (names : List String) (e : Typed.Expr) :
    M (Term .value × Formula) := do
  let dv ← encodeExpr Δ Γfn (names.map (fun n => (n, .var .value n))) e
  .ok (dv.value, dv.defined)

end SpecTranslation
