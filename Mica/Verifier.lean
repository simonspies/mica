-- SUMMARY: Bundle for `Verifier/`, containing the verifier itself, stratified into monadic layers with correctness proofs.

import Mica.Verifier.SpatialAtom
import Mica.Verifier.PrimitiveLaws
import Mica.Verifier.Monad
import Mica.Verifier.Seq
import Mica.Verifier.Ownership
import Mica.Verifier.Bindings
import Mica.Verifier.GhostFunctions
import Mica.Verifier.FiniteSubst
import Mica.Verifier.Lemma
import Mica.Verifier.Assertions
import Mica.Verifier.Intrinsic
import Mica.Verifier.BoundedQuantifier
import Mica.Verifier.Context
import Mica.Verifier.Compilation
import Mica.Verifier.Ghost
import Mica.Verifier.Expressions
import Mica.Verifier.Declaration
import Mica.Verifier.RelationalEncoding
import Mica.Verifier.Specifications
import Mica.Verifier.Programs
