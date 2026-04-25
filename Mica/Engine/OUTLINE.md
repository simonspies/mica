**Mica/Engine**

- `Command.lean` — SMT commands, their responses, and their effect on the abstract solver state.
- `Driver.lean` — Execution of SMT strategies against a live Z3 process.
- `State.lean` — Abstract SMT states and the satisfiability notion used in the solver interface.
- `Strategy.lean` — Interactive SMT strategies and their relative semantics.
- `Trace.lean` — Execution traces and the soundness condition imposed on solver replies.
