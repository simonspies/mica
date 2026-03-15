/-
  Experiment: dynamically creating and solving proof goals at runtime from IO.

  This demonstrates that we can bootstrap a Lean Environment at runtime,
  construct Lean.Expr propositions, and discharge them using tactics (here, refl).
  The environment bootstrap (~260ms) loads Init's .olean files; the actual
  tactic invocation is essentially free.

  This is the foundation for a runtime verification tool: parse a TinyML program,
  translate proof obligations into Lean Exprs, and solve them via MetaM tactics
  (refl, omega, simp, etc.) — all from a compiled binary.
-/
import Lean

open Lean Meta in
def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Init }] {}
  let ctx : Core.Context := { fileName := "<dynamic-goal>", fileMap := default }
  let state : Core.State := { env }

  try
    let _ ← (MetaM.run' (do
      -- Build the proposition: Nat.add 1 1 = 2
      let nat := mkConst ``Nat
      let one := mkNatLit 1
      let two := mkNatLit 2
      let sum := mkApp2 (mkConst ``Nat.add) one one
      let prop := mkApp3 (mkConst ``Eq [.succ .zero]) nat sum two
      IO.println s!"Proposition: {← ppExpr prop}"

      -- Create a metavariable goal and close it with refl
      let goal ← mkFreshExprMVar (some prop)
      try
        goal.mvarId!.refl
        IO.println "✓ refl solved it!"
      catch _ =>
        IO.println "✗ could not solve"
    ) : CoreM Unit).toIO ctx state
  catch e =>
    IO.eprintln s!"error: {e}"
