**Mica/Verifier**

- `Assertions.lean` — Assertion language for specifications, together with its semantics, well-formedness conditions, and verifier operations.
- `Atoms.lean` — Verifier atoms for pure and spatial facts, together with their interpretations, resolution procedures, and correctness lemmas.
- `Bindings.lean` — Verifier variable-to-constant bindings, their semantic linkage to runtime substitutions, and typing/lookup lemmas.
- `Expressions.lean` — Compilation of typed TinyML expressions into verifier terms, with weakest-precondition correctness proofs.
- `Functions.lean` — Verification of function bodies against specifications, including the soundness of specification checking.
- `Monad.lean` — Verification monad with SMT operations, branching, and its operational and semantic correctness interfaces.
- `PredicateTransformers.lean` — Predicate transformers for function specifications, together with their semantics and call and implementation protocols.
- `Programs.lean` — End-to-end preparation and verification of programs, from typed elaboration to program-level soundness.
- `Scoped.lean` — Scoped SMT command language and its translation to solver strategies and flat contexts.
- `SpecMaps.lean` — Finite maps of function specifications, together with satisfaction, update, and well-formedness lemmas.
- `SpecTranslation.lean` — Sort-checked translation from frontend specifications into verifier terms, formulas, assertions, and predicate transformers.
- `Specifications.lean` — Function specifications, their semantics, and the protocols for specification calls and implementations.
- `State.lean` — Verifier state and environments, together with their well-formedness conditions and fresh-name infrastructure.
- `Utils.lean` — Supporting infrastructure for verifier finite substitutions and argument-handling helpers.
