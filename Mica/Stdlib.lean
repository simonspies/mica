-- SUMMARY: The concrete stdlib: the intrinsic registry, its soundness aggregate, and the prelude resolver.
import Mica.Verifier.Intrinsic
import Mica.Stdlib.IntStd
import Mica.Stdlib.StringStd
import Mica.Frontend.Resolver

open Iris Iris.BI

namespace Stdlib

open Verifier

def registry : Registry := [
  Intrinsics.stringEndsWith,
  Intrinsics.stringStartsWith,
  Intrinsics.stringEqual,
  Intrinsics.stringCat,
  Intrinsics.stringLength,
  Intrinsics.intMax,
  Intrinsics.intMin
]

theorem registry_sound : Registry.Sound registry := by
  simp [registry, Registry.Sound, Registry.SoundIn]
  -- Keep `registry` above as the single place where declared intrinsics are
  -- listed. Do not repeat concrete intrinsic names in this proof: infer each
  -- local dependency fragment, then prove only that it is contained in the
  -- registry.
  repeat' apply And.intro
  all_goals
    try trivial
    apply IntrinsicSound.mono
    · infer_instance
    · simp

theorem registry_wf : Registry.Wf registry := by
  -- The per-symbol freshness side conditions reduce to literal-name
  -- disequalities; the `@[simp]` `*_folSym`/`*Sym_name` lemmas expose the
  -- names, so this stays generic over the registry contents.
  simp [registry, Registry.Wf, Registry.WfFrom, Signature.extendWithSym,
    Signature.empty, Signature.addUnary, Signature.addBinary,
    Signature.allNames]

private def resolvedType (i : Intrinsic) : TinyML.Typ :=
  i.argTysList.foldr TinyML.Typ.arrow i.resultTy

private def resolverEntry (i : Intrinsic) :
    Option (Frontend.Path × Frontend.ResolvedValue) :=
  i.path.map (fun (head, tail) =>
    (⟨head, tail⟩, .primitive i.name (resolvedType i)))

/-- The prelude resolver: which surface qualified paths route to which built-in
    primitives. Derived from `registry`; injected into the frontend by `Main`. -/
def stdResolver : Frontend.Resolver := {
  values := registry.filterMap resolverEntry
}

end Stdlib
