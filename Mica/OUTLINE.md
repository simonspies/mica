**Mica**

- `Base.lean` — Bundle for `Base/`, containing shared utilities.
- `Engine.lean` — Bundle for `Engine/`, containing the SMT solver interaction protocol and its Z3 implementation.
- `FOL.lean` — Bundle for `FOL/`, containing first-order logic with Tarski semantics, targeting SMT encoding.
- `Frontend.lean` — Bundle for `Frontend/`, containing the lexer, parser, elaborator, and spec parser for the OCaml surface syntax.
- `SeparationLogic.lean` — Bundle for `SeparationLogic/`, containing Iris-based separation logic reasoning principles for TinyML.
- `TinyML.lean` — Bundle for `TinyML/`, containing the core IR in three stages: Untyped (surface), Typed (elaborated), Runtime (operational semantics).
- `Verifier.lean` — Bundle for `Verifier/`, containing the verifier itself, stratified into monadic layers with correctness proofs.
