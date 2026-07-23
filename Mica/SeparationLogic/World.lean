-- SUMMARY: The fixed meta-level world in which the logical relation interprets types.
import Mica.TinyML.Types
import Mica.TinyML.OpSem

namespace TinyML

/-- The fixed model in which the logical relation interprets types: the
    primitive-operational context its weakest preconditions are taken in, and
    the type environment unfolding named types.

    A world appears only in semantic definitions and correctness theorems;
    executable verifier definitions never receive one. -/
structure World where
  pctx : PrimCtx
  Θ    : TypeEnv

end TinyML
