import Mica.TinyML.Untyped
import Mica.TinyML.Printer
import Mica.Frontend.Parser
import Mica.Frontend.Printer
import Mica.Frontend.Elaborate
import Mica.Verifier.Programs
import Mica.Engine.Driver
import Mica.Stdlib

private def bold (s : String) : String := s!"\x1b[1m{s}\x1b[0m"

private structure Options where
  verbose     : Bool := false
  noCheck     : Bool := false
  printOcaml  : Bool := false
  printTinyML : Bool := false
  smtCmdsOnly : Bool := false
  file        : Option String := none
  error       : Option String := none

private def parseArgs : List String → Options → Options
  | [], opts => opts
  | "-v" :: rest, opts | "--verbose" :: rest, opts =>
    parseArgs rest { opts with verbose := true }
  | "--no-check" :: rest, opts =>
    parseArgs rest { opts with noCheck := true }
  | "--print-ocaml" :: rest, opts =>
    parseArgs rest { opts with printOcaml := true }
  | "--print-tiny-ml" :: rest, opts =>
    parseArgs rest { opts with printTinyML := true }
  | "--smt-commands-only" :: rest, opts =>
    parseArgs rest { opts with smtCmdsOnly := true }
  | arg :: rest, opts =>
    if opts.error.isSome then opts
    else if arg.startsWith "-" then { opts with error := some s!"unknown option: {arg}" }
    else if opts.file.isSome then { opts with error := some "multiple files provided" }
    else parseArgs rest { opts with file := some arg }

open Iris Iris.BI in
/-- Soundness of the verifier as actually configured by the CLI: a successful
    `Program.verify Stdlib.registry` run guarantees the program's weakest
    precondition holds under the registry-derived `wp` context. Instantiates the
    generic `Program.verify_correct` at the concrete stdlib registry, discharging
    its obligations from `Stdlib.registry_sound`. -/
theorem verify_sound [MicaGS HasLC.hasLC Sig]
    (p : Untyped.Program (Spec.Body Untyped.Expr)) :
    Smt.Strategy.checks (Program.verify Stdlib.registry p)
      (⊢ pwp Stdlib.registry.primCtx (Untyped.Program.runtime p)) :=
  Program.verify_correct Stdlib.registry Stdlib.registry_sound p

def main (args : List String) : IO Unit := do
  let opts := parseArgs args {}
  if let some e := opts.error then
    IO.eprintln s!"error: {e}"
    IO.Process.exit 1
  match opts.file with
  | none => do
    IO.eprintln "usage: mica [--verbose] [--no-check] [--print-ocaml] [--print-tiny-ml] [--smt-commands-only] <file.ml>"
    IO.Process.exit 1
  | some filename => do
    let contents ← IO.FS.readFile filename
    let frontendProg ← match Frontend.parseFile filename contents with
      | .ok prog => pure prog
      | .error e => do
        IO.eprintln s!"parse error: {e}"
        IO.Process.exit 1
    if opts.printOcaml then
      IO.println (Frontend.Program.print frontendProg)
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
    let session ← Smt.Session.create (log := logMode)
    let outcome ← Smt.Strategy.run (log := logMode) strategy session
    session.close
    if opts.smtCmdsOnly then
      return
    match outcome with
    | .ok () => IO.println s!"{bold "Status:"} all declarations verified"
    | .error msg => do
      IO.println s!"{bold "Status:"} failed: {msg}"
      IO.Process.exit 1
