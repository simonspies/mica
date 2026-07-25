**Mica**

- `Base.lean` — Bundle for `Base/`, containing shared utilities.
- `Engine.lean` — Bundle for `Engine/`, containing the SMT solver interaction protocol and its Z3 implementation.
- `FOL.lean` — Bundle for `FOL/`, containing first-order logic with Tarski semantics, targeting SMT encoding.
- `Frontend.lean` — Bundle for `Frontend/`, containing the lexer, parser, elaborator, and spec parser for the OCaml surface syntax.
- `SeparationLogic.lean` — Bundle for `SeparationLogic/`, containing the Iris program logic over the TinyML runtime: ghost state, weakest preconditions, and adequacy.
- `SourceTinyML.lean` — Bundle for `SourceTinyML/`, containing the source language: types, the untyped and typed IRs, elaboration, specifications, and their interpretation.
- `Stdlib.lean` — The concrete stdlib: the intrinsic registry, its soundness aggregate, and the prelude resolver.
- `TinyML.lean` — Bundle for `TinyML/`, containing the runtime language: shared vocabulary, runtime IR, heap, operational semantics, and Iris language instance.
- `Verifier.lean` — Bundle for `Verifier/`, containing the verifier itself, stratified into monadic layers with correctness proofs.
