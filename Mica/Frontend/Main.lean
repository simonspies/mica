import Mica.Frontend.AST
import Mica.Frontend.Parser
import Mica.Frontend.Printer

def main (args : List String) : IO UInt32 := do
  match args with
  | [file] =>
    let source ← IO.FS.readFile file
    match Frontend.parseFile file source with
    | .ok prog =>
      IO.println (Frontend.Program.print prog)
      return 0
    | .error e =>
      IO.eprintln (toString e)
      return 1
  | _ =>
    IO.eprintln "Usage: frontend <file.ml>"
    return 1
