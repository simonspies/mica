**Mica/SourceTinyML**

- `Assertions.lean` — Data of atoms, assertions, and completed specifications, parametric in the type language they mention.
- `Erasure.lean` — Elaboration preserves runtime erasure, one theorem per elaboration rule.
- `LogicalRelation.lean` — Iris logical relations for TinyML values and types, together with soundness proofs for type constraints.
- `Printer.lean` — Pretty-printing for the untyped TinyML IR and declarations.
- `Semantics.lean` — Semantics of atoms, assertions, and specifications, parametric in the value relation interpreting types.
- `TypeConstraints.lean` — First-order constraint formulas asserting that a term has a given TinyML type.
- `Typed.lean` — Typed TinyML IR, its typing contexts, and erasure to the runtime IR.
- `Types.lean` — TinyML types over a parameter of type variables, their substitution laws, type schemes, and type declarations.
- `Typing.lean` — Elaboration from the untyped IR to the typed IR, by unification.
- `Unification.lean` — Unification variables, the state that solves them, the IR they annotate, and the monad elaboration runs in.
- `Untyped.lean` — Untyped TinyML IR and specification syntax, with annotations carried where available.
- `World.lean` — The fixed meta-level world in which the logical relation interprets types, including its assignment of meanings to type variables.
