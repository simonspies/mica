**Mica/SeparationLogic**

- `Adequacy.lean` — Adequacy of the Mica weakest precondition: programs with a proven `pwp` never get stuck.
- `GhostState.lean` — Concrete Iris ghost-state signature for Mica: invariants, later credits, and heap resources over TinyML heaps.
- `Interpretations.lean` — Iris interpretations of spatial atoms and contexts, with lemmas relating syntax to separation-logic assertions.
- `LogicalRelation.lean` — Iris logical relations for TinyML values and types, together with formula generation for type constraints.
- `PrimitiveLaws.lean` — Spatially lifted weakest-precondition laws for TinyML primitive operations.
- `ProofModePatterns.lean` — Worked examples of Iris proof mode patterns used in the project.
- `SpatialAtom.lean` — Syntactic spatial atoms and contexts for verifier state, together with their well-formedness conditions and basic operations.
- `World.lean` — The fixed meta-level world in which the logical relation interprets types.
- `Wp.lean` — The Iris weakest precondition for TinyML and its derived proof rules, including invariant-based heap rules and primitive-call lifting.
