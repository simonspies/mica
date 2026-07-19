-- SUMMARY: Test representation: the TEST directive, expected `.out` files, and discovery.

/-!
# Test format

A test is a single `.ml` file. An optional directive on its first line
configures the run:

  (* TEST: <token>* *)

where a token starting with `-` is passed to mica as a flag and the bare
tokens `no-compile` (skip the ocamlopt phase) and `roundtrip` (additionally
check the print∘parse fixpoint of `--print-ocaml`) toggle runner behavior.

Expectations: without a sibling `foo.out`, the mica run must exit 0. With
one, the captured output (stdout ++ stderr, plus a trailing `[<code>]` line
for nonzero exits) must match it; `--promote` rewrites existing `.out` files
with the actual output instead of failing. Successful runs print no captured
output either way.
-/

open System (FilePath)

namespace Testsuite

/-- Per-test configuration from the `(* TEST: ... *)` directive. -/
structure Config where
  flags : Array String := #[]
  noCompile : Bool := false
  roundtrip : Bool := false

/-- A single `.ml` test file with its configuration and optional
    expected-output file (a sibling `.out`). -/
structure Test where
  path : FilePath
  label : String
  config : Config
  expected : Option FilePath

def parseDirective (path : FilePath) (line : String) : Except String Config := do
  let line := line.trimAscii.toString
  unless line.startsWith "(* TEST:" do return {}
  unless line.endsWith "*)" do
    throw s!"{path}: malformed TEST directive: {line}"
  let body := ((line.drop "(* TEST:".length).dropEnd "*)".length).toString
  let mut config : Config := {}
  for tok in body.split Char.isWhitespace do
    let tok := tok.toString
    if tok.isEmpty then
      continue
    else if tok.startsWith "-" then
      config := { config with flags := config.flags.push tok }
    else if tok == "no-compile" then
      config := { config with noCompile := true }
    else if tok == "roundtrip" then
      config := { config with roundtrip := true }
    else
      throw s!"{path}: unknown TEST directive token '{tok}'"
  return config

def relativeLabel (cwd : FilePath) (path : FilePath) : String :=
  let cwdPrefix := cwd.toString ++ FilePath.pathSeparator.toString
  if path.toString.startsWith cwdPrefix then
    (path.toString.drop cwdPrefix.length).toString
  else
    path.toString

def loadTest (cwd : FilePath) (path : FilePath) : IO Test := do
  let contents ← IO.FS.readFile path
  let firstLine := (contents.takeWhile (· != '\n')).toString
  let config ← IO.ofExcept (parseDirective path firstLine)
  let expectedPath := path.withExtension "out"
  let expected := if ← expectedPath.pathExists then some expectedPath else none
  return { path, label := relativeLabel cwd path, config, expected }

partial def discoverFiles (path : FilePath) (explicit : Bool) : IO (Array FilePath) := do
  let metadata ← path.metadata
  match metadata.type with
  | .file =>
      if path.extension == some "ml" then
        pure #[path]
      else if explicit then
        throw <| IO.userError s!"test file must end in .ml: {path}"
      else
        pure #[]
  | .dir =>
      let mut files := #[]
      for entry in (← path.readDir) do
        files := files ++ (← discoverFiles entry.path (explicit := false))
      pure files
  | _ =>
      if explicit then
        throw <| IO.userError s!"test path must be a .ml file or directory: {path}"
      else
        pure #[]

partial def stripTrailingSep (s : String) : String :=
  if s.length > 1 && s.endsWith FilePath.pathSeparator.toString then
    stripTrailingSep (s.dropEnd 1).toString
  else s

def discoverTests (cwd : FilePath) (paths : Array FilePath) : IO (Array Test) := do
  let mut files := #[]
  for path in paths do
    let path := FilePath.mk (stripTrailingSep path.toString)
    let inputPath := if path.isAbsolute then path else cwd / path
    if !(← inputPath.pathExists) then
      throw <| IO.userError s!"test path does not exist: {inputPath}"
    files := files ++ (← discoverFiles inputPath (explicit := true))
  let sorted := files.qsort (fun a b => a.toString < b.toString)
  sorted.mapM (loadTest cwd)

def defaultPaths (cwd : FilePath) : IO (Array FilePath) := do
  let candidates := #[cwd / "Examples", cwd / "Tests"]
  let paths ← candidates.filterM (·.pathExists)
  if paths.isEmpty then
    throw <| IO.userError "no test paths given and neither Examples/ nor Tests/ exists"
  pure paths

end Testsuite
