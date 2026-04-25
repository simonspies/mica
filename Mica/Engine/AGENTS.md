## Engine

`Mica.Engine` isolates the verifier's interaction with Z3 behind a small semantic interface. A `Strategy` describes an interactive protocol between Lean and the SMT solver, while its meaning records only the assumption we are willing to trust from the solver: whenever it answers `unsat`, the current SMT state is in fact unsatisfiable. The rest of the verification development is proved relative to this interface: the verifier is compiled to a strategy, and correctness says that if every `unsat` answer used along that strategy is sound, then the desired verification property follows.

@OUTLINE.md
