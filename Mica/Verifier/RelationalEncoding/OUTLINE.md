**Mica/Verifier/RelationalEncoding**

- `Axioms.lean` — Solver-facing axioms and validity theorems for the skolemized relational encoding.
- `Expr.lean` — The encoder intermediate language, the traversal into it, and its well-formedness.
- `Relation.lean` — Stage 1 — encode a recursive TinyML body as a binary FOL relation defined by least fixpoint.
- `Skolemize.lean` — Skolemization: the definedness/value encoding, what it denotes, and its equivalence with the relational encoding.
- `Termination.lean` — Integer induction for total definedness of specification functions.
- `Variables.lean` — Fresh-name allocation, function context, local variable environments, and the head signatures and freshness conditions of the relational encoding.
