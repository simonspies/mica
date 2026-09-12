-- SUMMARY: The concrete stdlib: the intrinsic registry, its soundness aggregate, and the prelude resolver.
import Mica.Verifier.Intrinsic
import Mica.Verifier.BoundedQuantifier
import Mica.Stdlib.IntStd
import Mica.Stdlib.FixedIntStd
import Mica.Stdlib.CharStd
import Mica.Stdlib.StringStd
import Mica.Stdlib.FloatStd
import Mica.Stdlib.FunStd
import Mica.Stdlib.VecStd
import Mica.Stdlib.ListStd
import Mica.Stdlib.OptionStd
import Mica.Stdlib.ErrorStd
import Mica.Stdlib.LogicStd
import Mica.Frontend.Resolver

open Iris Iris.BI

namespace Stdlib

open Verifier

def registry : Registry := [
  Verifier.BoundedQuantifier.allIntrinsic,
  Verifier.BoundedQuantifier.existsIntrinsic,
  Intrinsics.failwith,
  Intrinsics.invalidArg,
  Intrinsics.logicEq,
  Intrinsics.logicSize,
  Intrinsics.vecMake,
  Intrinsics.vecSet,
  Intrinsics.vecGet,
  Intrinsics.vecLength,
  Intrinsics.listLengthIntrinsic,
  Intrinsics.listAppendIntrinsic,
  Intrinsics.listRevIntrinsic,
  Intrinsics.optionIsSomeIntrinsic,
  Intrinsics.optionIsNoneIntrinsic,
  Intrinsics.optionValueIntrinsic,
  Intrinsics.funId,
  Intrinsics.int32Const .zero,
  Intrinsics.int32Const .one,
  Intrinsics.int32Const .minusOne,
  Intrinsics.int32Const .minInt,
  Intrinsics.int32Const .maxInt,
  Intrinsics.int32Unary .neg,
  Intrinsics.int32Unary .lognot,
  Intrinsics.int32Binary .add,
  Intrinsics.int32Binary .sub,
  Intrinsics.int32Binary .mul,
  Intrinsics.int32Binary .div,
  Intrinsics.int32Binary .unsignedDiv,
  Intrinsics.int32Binary .rem,
  Intrinsics.int32Binary .unsignedRem,
  Intrinsics.int32Binary .logand,
  Intrinsics.int32Binary .logor,
  Intrinsics.int32Binary .logxor,
  Intrinsics.int32Binary .min,
  Intrinsics.int32Binary .max,
  Intrinsics.int32Compare .compare,
  Intrinsics.int32Compare .unsignedCompare,
  Intrinsics.int32Compare .equal,
  Intrinsics.int32Shift .left,
  Intrinsics.int32Shift .right,
  Intrinsics.int32Shift .rightLogical,
  Intrinsics.int32OfInt,
  Intrinsics.int32ToInt,
  Intrinsics.int64Const .zero,
  Intrinsics.int64Const .one,
  Intrinsics.int64Const .minusOne,
  Intrinsics.int64Const .minInt,
  Intrinsics.int64Const .maxInt,
  Intrinsics.int64Unary .neg,
  Intrinsics.int64Unary .lognot,
  Intrinsics.int64Binary .add,
  Intrinsics.int64Binary .sub,
  Intrinsics.int64Binary .mul,
  Intrinsics.int64Binary .div,
  Intrinsics.int64Binary .unsignedDiv,
  Intrinsics.int64Binary .rem,
  Intrinsics.int64Binary .unsignedRem,
  Intrinsics.int64Binary .logand,
  Intrinsics.int64Binary .logor,
  Intrinsics.int64Binary .logxor,
  Intrinsics.int64Binary .min,
  Intrinsics.int64Binary .max,
  Intrinsics.int64Compare .compare,
  Intrinsics.int64Compare .unsignedCompare,
  Intrinsics.int64Compare .equal,
  Intrinsics.int64Shift .left,
  Intrinsics.int64Shift .right,
  Intrinsics.int64Shift .rightLogical,
  Intrinsics.int64OfInt,
  Intrinsics.int64ToInt,
  Intrinsics.int64OfInt32,
  Intrinsics.int64ToInt32,
  Intrinsics.floatNegInfinity,
  Intrinsics.floatInfinity,
  Intrinsics.floatNan,
  Intrinsics.floatLe,
  Intrinsics.floatLt,
  Intrinsics.floatEqual,
  Intrinsics.floatMax,
  Intrinsics.floatMin,
  Intrinsics.floatDiv,
  Intrinsics.floatMul,
  Intrinsics.floatSub,
  Intrinsics.floatAdd,
  Intrinsics.floatOfInt,
  Intrinsics.floatIsFinite,
  Intrinsics.floatIsNan,
  Intrinsics.floatSqrt,
  Intrinsics.floatNeg,
  Intrinsics.floatAbs,
  Intrinsics.stringEndsWith,
  Intrinsics.stringStartsWith,
  Intrinsics.stringEqual,
  Intrinsics.stringSub,
  Intrinsics.stringGet,
  Intrinsics.stringCat,
  Intrinsics.stringLength,
  Intrinsics.charEqual,
  Intrinsics.charChr,
  Intrinsics.charCode,
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
    Signature.empty, Signature.addConst, Signature.addUnary, Signature.addBinary,
    Signature.addTernary, Signature.allNames]

private def resolverEntry (i : Intrinsic) :
    Option (Frontend.Path × Frontend.ResolvedValue) :=
  i.path.map (fun (head, tail) =>
    (⟨head, tail⟩, .primitive i.name
      (match i.arity with | .zero => .nullary | _ => .function)))

/-- The prelude resolver: which surface qualified paths route to which built-in
    primitives. Derived from `registry`; injected into the frontend by `Main`. -/
def stdResolver : Frontend.Resolver := {
  values := registry.filterMap resolverEntry ++ [
    (⟨"Array", ["make"]⟩, .special .arrayMake),
    (⟨"Array", ["length"]⟩, .special .arrayLength),
    (⟨"Array", ["get"]⟩, .special .arrayGet),
    (⟨"Array", ["set"]⟩, .special .arraySet)
  ]
}

end Stdlib
