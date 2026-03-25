import Mica.TinyML
import Mica.Frontend.Parser
import Mica.Frontend.Elaborate
import Mica.Verifier.Programs
import Mica.Engine.Driver

private def bold (s : String) : String := s!"\x1b[1m{s}\x1b[0m"

private structure Options where
  verbose    : Bool := false
  noCheck    : Bool := false
  printTinyML : Bool := false
  file       : Option String := none

private def parseArgs : List String → Options → Options
  | [], opts => opts
  | "-v" :: rest, opts | "--verbose" :: rest, opts =>
    parseArgs rest { opts with verbose := true }
  | "--no-check" :: rest, opts =>
    parseArgs rest { opts with noCheck := true }
  | "--print-tiny-ml" :: rest, opts =>
    parseArgs rest { opts with printTinyML := true }
  | arg :: rest, opts =>
    parseArgs rest { opts with file := some arg }

def main (args : List String) : IO Unit := do
  let opts := parseArgs args {}
  match opts.file with
  | none => do
    IO.eprintln "usage: mica [--verbose] [--no-check] [--print-tiny-ml] <file.ml>"
    IO.Process.exit 1
  | some filename => do
    let contents ← IO.FS.readFile filename
    -- Try frontend parser first, fall back to TinyML parser
    let prog ← match Frontend.parseFile filename contents with
      | .ok frontendProg =>
        match Frontend.Program.elaborate frontendProg with
        | .ok tinymlProg => pure tinymlProg
        | .error e => do
          IO.eprintln s!"elaboration error: {e}"
          IO.Process.exit 1
      | .error _ =>
        -- Fall back to TinyML parser
        match TinyML.parseFile contents with
        | .ok prog => pure prog
        | .error msg => do
          IO.eprintln s!"parse error: {msg}"
          IO.Process.exit 1
    if opts.printTinyML then
      IO.println (TinyML.Program.print prog)
    if opts.noCheck then
      return
    let strategy := Program.verify prog
    let session ← SmtSession.create
    let outcome ← run (log := opts.verbose) strategy session
    session.close
    match outcome with
    | .ok () => IO.println s!"{bold "Status:"} all declarations verified"
    | .error msg => do
      IO.println s!"{bold "Status:"} failed: {msg}"
      IO.Process.exit 1
