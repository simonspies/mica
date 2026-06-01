**Mica/Verifier/RelationalEncoding**

- `Axioms.lean` — Solver-facing axioms and validity theorems for skolemized relational encoding.
- `Monad.lean` — Generic monadic skeleton for TinyML-to-FOL encoders.
- `Prim.lean` — Encoding of saturated intrinsic applications into FOL terms, with well-formedness, arity-irrelevance, and evaluation lemmas.
- `Relation.lean` — Stage 1 — encode a recursive TinyML body as a binary FOL relation defined by least fixpoint.
- `SkolemizeCommon.lean` — Shared split encoding and semantic infrastructure for Skolemization.
- `SkolemizeCompleteness.lean` — Completeness of Skolemization: relational encoding implies split definedness/value.
- `SkolemizeSoundness.lean` — Soundness of Skolemization: split definedness/value implies the relational encoding.
- `Variables.lean` — Shared names, signatures, and freshness helpers for relational encoding.
