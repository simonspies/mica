**Mica/Engine**

- `Command.lean` — SMT commands, their responses, and their effect on the abstract solver state.
- `Driver.lean` — Execution of SMT strategies against a live Z3 process.
- `SMTLIB.lean` — Serialization of first-order syntax to SMT-LIB.
- `Scoped.lean` — Scoped SMT command language and its translation to solver strategies and flat contexts.
- `State.lean` — Abstract SMT states and the satisfiability notion used in the solver interface.
- `Strategy.lean` — Interactive SMT strategies and their relative semantics.
- `Trace.lean` — Execution traces and the soundness condition imposed on solver replies.
