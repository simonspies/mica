import Mica.SourceTinyML.Untyped
import Mica.SourceTinyML.Printer
import Mica.Frontend.ParenPrinter
import Mica.Frontend.Parser
import Mica.Frontend.Printer
import Mica.Frontend.Elaborate
import Mica.Verifier.Programs
import Mica.Engine.Driver
import Mica.Stdlib

private def bold (ansi : Bool) (s : String) : String :=
  if ansi then s!"\x1b[1m{s}\x1b[0m" else s

private structure Options where
  verbose     : Bool := false
  noCheck     : Bool := false
  ansi        : Bool := true
  printOcaml  : Bool := false
  printTinyML : Bool := false
  parseOnly   : Bool := false
  parens      : Bool := false
  smtCmdsOnly : Bool := false
  file        : Option String := none
  error       : Option String := none

private def parseArgs : List String → Options → Options
  | [], opts => opts
  | "-v" :: rest, opts | "--verbose" :: rest, opts =>
    parseArgs rest { opts with verbose := true }
  | "--no-check" :: rest, opts =>
    parseArgs rest { opts with noCheck := true }
  | "--ansi" :: rest, opts =>
    parseArgs rest { opts with ansi := true }
  | "--no-ansi" :: rest, opts =>
    parseArgs rest { opts with ansi := false }
  | "--print-ocaml" :: rest, opts =>
    parseArgs rest { opts with printOcaml := true }
  | "--print-tiny-ml" :: rest, opts =>
    parseArgs rest { opts with printTinyML := true }
  | "--parse-only" :: rest, opts =>
    parseArgs rest { opts with parseOnly := true, printOcaml := true }
  | "--parens" :: rest, opts =>
    parseArgs rest { opts with parens := true }
  | "--smt-commands-only" :: rest, opts =>
    parseArgs rest { opts with smtCmdsOnly := true }
  | arg :: rest, opts =>
    if opts.error.isSome then opts
    else if arg.startsWith "-" then { opts with error := some s!"unknown option: {arg}" }
    else if opts.file.isSome then { opts with error := some "multiple files provided" }
    else parseArgs rest { opts with file := some arg }

/-- Adequacy of the verifier as actually configured by the CLI: a successful
    `Program.verify Stdlib.registry` run guarantees that executions of the
    program never gets stuck.
    Instantiates the generic `Program.verify_adequate` at the concrete stdlib
    registry, discharging its obligations from `Stdlib.registry_sound`. -/
theorem verify_adequate (p : Untyped.Program Untyped.SpecBody) :
    Smt.Strategy.checks (Program.verify Stdlib.registry p)
      (∀ {e' : Runtime.Expr} {μ' : TinyML.Heap},
        TinyML.Steps Stdlib.registry.primCtx (Untyped.Program.runtime p).expr ∅ e' μ' →
        (∃ v, e' = .val v) ∨ ∃ e'' μ'', TinyML.Step Stdlib.registry.primCtx e' μ' e'' μ'') :=
  Program.verify_adequate Stdlib.registry Stdlib.registry_sound p

def main (args : List String) : IO Unit := do
  let opts := parseArgs args {}
  if let some e := opts.error then
    IO.eprintln s!"error: {e}"
    IO.Process.exit 1
  match opts.file with
  | none => do
    IO.eprintln "usage: mica [--verbose] [--no-check] [--ansi|--no-ansi] [--print-ocaml] [--print-tiny-ml] [--parse-only] [--parens] [--smt-commands-only] <file.ml>"
    IO.Process.exit 1
  | some filename => do
    let contents ← IO.FS.readFile filename
    let frontendProg ← match Frontend.parseFile filename contents with
      | .ok prog => pure prog
      | .error e => do
        IO.eprintln s!"parse error: {e}"
        IO.Process.exit 1
    if opts.printOcaml then
      IO.println <|
        if opts.parens then Frontend.Program.printParen frontendProg
        else Frontend.Program.print frontendProg
    if opts.parseOnly then
      return
    let untypedProg ← match Frontend.Program.elaborate Stdlib.stdResolver frontendProg with
      | .ok prog => pure prog
      | .error e => do
        IO.eprintln s!"elaboration error: {e}"
        IO.Process.exit 1
    if opts.printTinyML then
      IO.println (Untyped.Program.print untypedProg)
    if opts.noCheck then
      return
    let strategy := Program.verify Stdlib.registry untypedProg
    let logMode : Smt.LogMode :=
      if opts.smtCmdsOnly then .script
      else if opts.verbose then .trace
      else .quiet
    let outcome ← Smt.Strategy.execute strategy (log := logMode)
    if opts.smtCmdsOnly then
      return
    match outcome with
    | .ok () => IO.println s!"{bold opts.ansi "Status:"} all declarations verified"
    | .error msg => do
      IO.println s!"{bold opts.ansi "Status:"} failed: {msg}"
      IO.Process.exit 1
