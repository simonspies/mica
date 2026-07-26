**Mica/SourceTinyML**

- `Assertions.lean` — Assertion data for specifications: atoms, the assertion language, predicate transformers, and specs.
- `LogicalRelation.lean` — Iris logical relations for TinyML values and types, together with formula generation for type constraints.
- `Printer.lean` — Pretty-printing for the untyped TinyML IR and declarations.
- `Spec.lean` — Abstract syntax for specifications embedded in TinyML programs.
- `TypeConstraints.lean` — First-order constraint formulas asserting that a term has a given TinyML type.
- `Typed.lean` — Typed TinyML IR, with erasure to the runtime IR.
- `Types.lean` — TinyML types, type declarations, and subtyping structure.
- `Typing.lean` — Elaboration and typechecking from the untyped IR to the typed IR.
- `Untyped.lean` — Untyped TinyML IR, with annotations carried where available.
- `World.lean` — The fixed meta-level world in which the logical relation interprets types.
