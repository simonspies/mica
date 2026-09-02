**Mica/Verifier/RelationalEncoding**

- `Axioms.lean` — Solver-facing axioms and validity theorems for skolemized relational encoding.
- `Expr.lean` — The encoder intermediate language, the traversal into it, and its well-formedness.
- `Relation.lean` — Stage 1 — encode a recursive TinyML body as a binary FOL relation defined by least fixpoint.
- `SkolemizeCommon.lean` — Shared split encoding and semantic infrastructure for Skolemization.
- `SkolemizeCompleteness.lean` — Completeness of Skolemization: relational encoding implies split definedness/value.
- `SkolemizeSoundness.lean` — Soundness of Skolemization: split definedness/value implies the relational encoding.
- `Variables.lean` — Name supply, function context, and local variable environments for relational encoding.
