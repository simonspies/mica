import Mica.TinyML
import Mica.Verifier.Programs
import Mica.Engine.Driver

private def bold (s : String) : String := s!"\x1b[1m{s}\x1b[0m"

def main (args : List String) : IO Unit := do
  let verbose := args.contains "-v" || args.contains "--verbose"
  let fileArgs := args.filter (fun a => a != "-v" && a != "--verbose")
  match fileArgs with
  | [filename] =>
    let contents ← IO.FS.readFile filename
    match TinyML.parseFile contents with
    | .error msg => IO.eprintln s!"parse error: {msg}"
    | .ok prog =>
      let strategy := Program.verify prog
      let session ← SmtSession.create
      let outcome ← run (log := verbose) strategy session
      session.close
      match outcome with
      | .ok () => IO.println s!"{bold "Status:"} all declarations verified"
      | .error msg => IO.println s!"{bold "Status:"} failed: {msg}"
  | _ => IO.eprintln "usage: mica [-v|--verbose] <file.ml>"
