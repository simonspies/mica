**Mica/SourceTinyML**

- `Assertions.lean` — Data of atoms, assertions, and completed specifications, parametric in the type language they mention.
- `LogicalRelation.lean` — Iris logical relations for TinyML values and types, together with soundness proofs for type constraints.
- `Printer.lean` — Pretty-printing for the untyped TinyML IR and declarations.
- `Semantics.lean` — Semantics of atoms, assertions, and specifications, parametric in the value relation interpreting types.
- `TypeConstraints.lean` — First-order constraint formulas asserting that a term has a given TinyML type.
- `Typed.lean` — Typed TinyML IR, its typing contexts, and erasure to the runtime IR.
- `Types.lean` — TinyML types over a parameter of type variables, type declarations, and subtyping.
- `Typing.lean` — Elaboration and typechecking from the untyped IR to the typed IR.
- `Unification.lean` — The failure elaboration can raise and the monad carrying it.
- `Untyped.lean` — Untyped TinyML IR and specification syntax, with annotations carried where available.
- `World.lean` — The fixed meta-level world in which the logical relation interprets types.
