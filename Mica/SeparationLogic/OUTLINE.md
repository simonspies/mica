**Mica/SeparationLogic**

- `Adequacy.lean` — Adequacy of the Mica weakest precondition: programs with a proven `pwp` never get stuck.
- `GhostState.lean` — Concrete Iris ghost-state signature for Mica: invariants, later credits, and heap resources over TinyML heaps.
- `ProofModePatterns.lean` — Worked examples of Iris proof mode patterns used in the project.
- `Wp.lean` — The Iris weakest precondition for TinyML and its derived proof rules, including invariant-based heap rules and primitive-call lifting.
