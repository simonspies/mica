-- SUMMARY: Differential parser tests comparing mica's reading of a generated corpus against OCaml's.
import Std.Data.HashMap
import Testsuite.Process

/-!
# Differential parser tests

`ocamlc` is used as the oracle for its own parse tree, twice over. For each
generated fixture `S`:

1. mica parses `S` and re-prints it fully parenthesized as `P`
   (`mica --parse-only --parens`, see `Mica/Frontend/ParenPrinter.lean`).
2. `ocamlc -stop-after parsing -dsource` runs on both `S` and `P`.

That flag re-parenthesizes from the parse tree rather than echoing the input, so
redundant parentheses normalize away and the two outputs are byte-identical
exactly when mica read `S` the way OCaml does.

The printer used in step 1 never consults a precedence table. If it shared
`Printer.lean`'s table, a precedence error in the parser and the matching error
in the printer would cancel out and the comparison would pass.

A second pass repeats the comparison with mica's *normal* printer. The first
pass failing indicts the parser; only the second failing indicts the printer.

-/

open System (FilePath)

namespace Testsuite.ParserDiff

-- ---------------------------------------------------------------------------
-- Corpus

/-- One fixture: a unique name and the declaration it expands to. -/
structure Case where
  name : String
  decl : String
  deriving Inhabited

/-- Bound by every generated declaration, so no fixture depends on anything
outside itself. -/
private def params : String := "a b c d f g r i j x"

/-- The surface binary operators, as written.

`<-` is absent on purpose: OCaml's grammar accepts it only after an array or
field access, so a bare `a <- b` is a syntax error. It gets its own fixtures. -/
def binOps : List String :=
  [ "+", "-", "*", "/", "mod", "+.", "-.", "*.", "/."
  , "=", "<>", "<", "<=", ">", ">="
  , "&&", "||", "|>", "@@", ":=", "^", "@", "::", ";" ]

/-- `a op1 b op2 c` for every ordered pair — the precedence table as a matrix.
The diagonal covers associativity. -/
def pairCases : List String :=
  binOps.flatMap fun op1 => binOps.map fun op2 => s!"a {op1} b {op2} c"

/-- Prefix operators against every binary operator, then against application and
the postfix forms. In OCaml prefix `!` binds tighter than both application and
`.`/`.(`, while prefix `-` binds looser than application. -/
def prefixCases : List String :=
  (binOps.flatMap fun op =>
    [ s!"- a {op} b", s!"a {op} - b"
    , s!"! r {op} b", s!"a {op} ! r"
    , s!"assert a {op} b" ])
  -- `assert f a` is absent: OCaml's `assert` takes one simple expression, so it
  -- is a syntax error there and has no reading to compare against.
  ++ [ "f ! r", "! f a", "f (- a)", "f - a", "assert (f a)"
     , "! a.b", "! a.(i)", "- a.b", "- f a", "f a.b", "f a.(i)"
     , "a.b.c", "a.(i).(j)", "a.b.(i)", "a.(i).b"
     , "! ! r", "- - a", "! r.b.c", "assert a.b" ]

/-- Application against every binary operator. -/
def appCases : List String :=
  binOps.flatMap fun op => [s!"f a {op} b", s!"a {op} f b", s!"f a b {op} c"]

/-- Keyword expressions as an operand on each side. The two sides differ in
OCaml: on the right the keyword form absorbs everything after it, on the left
only its trailing branch does. -/
def keywordCases : List String :=
  binOps.flatMap fun op =>
    [ s!"a {op} if b then c else d"
    , s!"if b then c else d {op} a"
    , s!"a {op} match b with | _ -> c"
    , s!"a {op} fun x -> x"
    , s!"a {op} let x = b in x"
    , s!"let x = a in x {op} b" ]

/-- `<-` needs an array element or a record field on the left in both
languages. It is excluded from `binOps` for that reason. -/
def arraySetCases : List String :=
  (binOps.map fun op => s!"a.(i) <- b {op} c")
  ++ [ "a.(i) <- b", "a.(i) <- if b then c else d", "a.(i) <- fun x -> x"
     , "a.(i) <- a.(j) <- b", "a.(i) <- - b", "a.(i) <- ! r"
     , "r.u <- b", "r.u.v <- b", "r.u <- b + c", "a.(i).u <- b", "r.u <- a.(i)" ]

/-- The comma level, which OCaml puts between `||` and `:=`/`<-`, and where a
tuple needs no enclosing parentheses. This axis is separate from `binOps`
because a comma is not an operator that composes the way the others do. -/
def commaCases : List String :=
  (binOps.flatMap fun op => [s!"a, b {op} c", s!"a {op} b, c"])
  ++ [ "a, b", "a, b, c", "f a, b", "(a, b), c", "a, (b, c)"
     , "[a, b]", "[a; b]", "f (a, b)", "(a, b)", "[a, b; c]"
     , "a.(i), b", "- a, b", "! r, b", "a, b, c, d"
     , "if a then b, c else d", "fun x -> x, a", "let x = a, b in x" ]

/-- Record literals, updates, and the punned field `{ a }`, which is `{ a = a }`. -/
def recordCases : List String :=
  [ "{ a = b }", "{ a = b; c = d }", "{ a }", "{ a; c }", "{ a; c = d }"
  , "{ a = b, c }", "{ a = b; c }", "{ r with a }", "{ r with a = b }"
  , "{ a }.b", "f { a }", "{ a = f b }", "{ a } :: r" ]

/-- `begin e end` is `(e)`: same tree, no node of its own, and a simple
expression wherever one is expected. -/
def beginEndCases : List String :=
  [ "begin a end", "begin a + b end * c", "f begin a end", "begin a; b end"
  , "begin a end.b", "- begin a end", "begin f a end b", "begin a, b end"
  , "begin if a then b else c end", "! begin r end", "begin a end.(i)" ]

/-- Pattern-level precedence, exercised in a match arm: `::` against the comma
level, against constructor application, and against annotation. -/
def patternCases : List String :=
  [ "_", "y", "0", "'c'", "true", "[]", "()"
  , "y :: z", "y :: z :: w", "(y, z)", "y, z", "(y : int)"
  , "{ u = y }", "{ u = y; v = z }"
  , "A", "A y", "A (y, z)", "A y :: z", "(A y, B z)"
  , "A y :: B z :: w", "(y, z) :: w", "{ u = y } :: z"
  , "[] :: z", "A []", "A _", "A (B y)", "(y :: z, w)"
  , "y :: (z, w)", "A 0", "A 'c'"
  -- A constructor payload is itself a constructor application, not an atom.
  , "A B", "A B y", "A B C", "A B y :: z", "A (B y) :: z"
  -- Punned record fields: `{ u }` is `{ u = u }`.
  , "{ u }", "{ u; v }", "{ u = y; v }", "{ u } :: z" ]

/-- Declaration shapes that the body-level groups above cannot express: the
`let` header itself, and the arms of a `match` written out. `NAME` is replaced by
the fixture's generated name. -/
def declCases : List String :=
  [ "let NAME x = match x with y -> 0"
  , "let NAME x = match x with A -> 0 | B -> 1"
  , "let NAME x = match x with | A -> 0 | B -> 1"
  , "let NAME x = match x with A y -> y | B -> 0"
  , "let NAME f x : int -> int = f x"
  , "let NAME x : int = x"
  , "let NAME (f : int -> int) x = f x"
  , "let NAME x = fun y : int -> y"
  , "let NAME x = (fun y : (int -> int) -> y) x"
  , "let rec NAME x = NAME x" ]

/-- Type declarations: variants, records, and parameters. `NAME` is replaced by
the fixture's generated name. -/
def typeDeclCases : List String :=
  [ "type NAME = int"
  , "type NAME = int list"
  , "type NAME = A | B"
  , "type NAME = A | B of int"
  , "type NAME = | A | B of int"
  , "type NAME = A of int * int"
  , "type NAME = A of (int -> int)"
  , "type NAME = A of int list"
  , "type NAME = { u : int }"
  , "type NAME = { u : int; v : int list }"
  , "type NAME = { u : int -> int }"
  , "type NAME = { u : int * int }"
  , "type 'a NAME = A of 'a"
  , "type ('a, 'b) NAME = A of 'a * 'b"
  , "type 'a NAME = { u : 'a }"
  , "type 'a NAME = A of 'a list | B" ]

/-- Type-expression precedence: `*` against `->` against application. -/
def typeCases : List String :=
  [ "int * int -> int", "int -> int * int", "int -> int -> int"
  , "int * int * int", "int list list", "int list * int"
  , "int -> int list", "int list -> int", "(int -> int) list"
  , "int * int list", "'a list", "'a -> 'a", "'a * 'b -> 'c"
  , "int array", "int ref list", "(int -> int) -> int"
  , "int list list list", "'a * 'b * 'c -> 'd" ]

private def caseName (n : Nat) : String :=
  let s := toString n
  "t" ++ "".pushn '0' (4 - min 4 s.length) ++ s

/-- The full corpus, numbered so that a fixture's line number is its index. -/
def allCases : Array Case := Id.run do
  let mut out : Array Case := #[]
  let mut n : Nat := 0
  for group in [pairCases, prefixCases, appCases, keywordCases, arraySetCases,
                commaCases, beginEndCases, recordCases] do
    for body in group do
      out := out.push { name := caseName n, decl := s!"let {caseName n} {params} = {body}" }
      n := n + 1
  for ty in typeCases do
    out := out.push { name := caseName n, decl := s!"let {caseName n} (x : {ty}) = x" }
    n := n + 1
  for pat in patternCases do
    out := out.push { name := caseName n
                    , decl := s!"let {caseName n} x = match x with | {pat} -> 0 | _ -> 1" }
    n := n + 1
  for d in declCases ++ typeDeclCases do
    out := out.push { name := caseName n, decl := d.replace "NAME" (caseName n) }
    n := n + 1
  return out

-- ---------------------------------------------------------------------------
-- Running the two parsers

private def writeLines (path : FilePath) (lines : Array String) : IO Unit :=
  IO.FS.writeFile path ("\n".intercalate lines.toList ++ "\n")

/-- Run `ocamlc -stop-after parsing -dsource`, which writes the re-printed parse
tree to stderr. -/
def dsource (dir : FilePath) (file : String) : IO (Except String String) := do
  match ← runProcess "ocamlc" #["-stop-after", "parsing", "-dsource", file] (some dir) with
  | .timeout ms => return .error s!"ocamlc timed out after {ms}ms"
  | .terminated out =>
    if out.exitCode != 0 then return .error out.stderr else return .ok out.stderr

/-- Run mica's parser, printing the result in the given style. -/
def micaPrint (mica : FilePath) (dir : FilePath) (file : String) (parens : Bool)
    : IO (Except String String) := do
  let args := if parens then #["--parse-only", "--parens", file] else #["--parse-only", file]
  match ← runProcess mica.toString args (some dir) with
  | .timeout ms => return .error s!"mica timed out after {ms}ms"
  | .terminated out =>
    if out.exitCode != 0 then return .error (out.stdout ++ out.stderr)
    else return .ok out.stdout

/-- Pull the line number out of `File "f", line N, characters ...`. -/
def ocamlErrorLine (msg : String) : Option Nat := do
  let line ← (msg.splitOn "\n").find? (·.startsWith "File \"")
  let after ← (line.splitOn ", line ")[1]?
  (after.takeWhile Char.isDigit).toNat?

/-- Run `ocamlc` over the corpus, and on a syntax error drop the offending
fixture and retry. A fixture that OCaml rejects is a bug in the generator, not a
finding about mica, but it must not take down the rest of the run. -/
partial def ocamlWithRejections (dir : FilePath) (cases : Array Case)
    (lines : Array String) (invalid : Array String) (budget : Nat)
    : IO (Except String (String × Array String)) := do
  writeLines (dir / "corpus.ml") lines
  match ← dsource dir "corpus.ml" with
  | .ok out => return .ok (out, invalid)
  | .error msg =>
    if budget == 0 then
      return .error s!"gave up after too many invalid fixtures; last error: {msg}"
    match ocamlErrorLine msg with
    | none => return .error msg
    | some lineNo =>
      let idx := lineNo - 1
      if idx < cases.size then
        ocamlWithRejections dir cases
          (lines.set! idx s!"let {cases[idx]!.name} = 0") (invalid.push cases[idx]!.name) (budget - 1)
      else
        return .error msg

/-- Pull the line number out of `parse error: FILE:LINE:COL: message`. -/
def parseErrorLine (msg : String) : Option Nat := do
  let line ← (msg.splitOn "\n").find? (·.startsWith "parse error: ")
  let fields := (line.drop "parse error: ".length).toString.splitOn ":"
  let lineStr ← fields[1]?
  lineStr.trimAscii.toString.toNat?

/-- Run mica over the corpus, and on a parse error replace the offending
declaration with a placeholder and retry, so one rejected fixture does not hide
every fixture after it. Returns the printed program and the rejected names. -/
partial def micaWithRejections (mica : FilePath) (dir : FilePath) (parens : Bool)
    (cases : Array Case) (lines : Array String) (rejected : Array String) (budget : Nat)
    : IO (Except String (String × Array String)) := do
  writeLines (dir / "probe.ml") lines
  match ← micaPrint mica dir "probe.ml" parens with
  | .ok out => return .ok (out, rejected)
  | .error msg =>
    if budget == 0 then
      return .error s!"gave up after too many rejected fixtures; last error: {msg}"
    match parseErrorLine msg with
    | none => return .error msg
    | some lineNo =>
      let idx := lineNo - 1
      if idx < cases.size then
        let c := cases[idx]!
        micaWithRejections mica dir parens cases
          (lines.set! idx s!"let {c.name} = 0") (rejected.push c.name) (budget - 1)
      else
        return .error msg

-- ---------------------------------------------------------------------------
-- Comparison

/-- The `tNNNN` binder identifying a generated declaration, if this line starts
one. Handles both `let tNNNN ...` and `type ['a] tNNNN = ...`. A wrapped
declaration's continuation lines are indented, so they never match. -/
def declName (line : String) : Option String :=
  if !(line.startsWith "let " || line.startsWith "type ") then none
  else (line.splitOn " ").find? fun w =>
    w.length == 5 && w.startsWith "t" && (w.drop 1).toString.all Char.isDigit

/-- Split `-dsource` output into one chunk per generated declaration. -/
def groupByDecl (out : String) : Array (String × String) := Id.run do
  let mut groups : Array (String × String) := #[]
  let mut name := ""
  let mut cur : Array String := #[]
  for line in out.splitOn "\n" do
    match declName line with
    | some n =>
      if !name.isEmpty then groups := groups.push (name, " ".intercalate cur.toList)
      name := n
      cur := #[line.trimAscii.toString]
    | none =>
      if !name.isEmpty && !line.trimAscii.toString.isEmpty then
        cur := cur.push line.trimAscii.toString
  if !name.isEmpty then groups := groups.push (name, " ".intercalate cur.toList)
  return groups

/-- Drop the `let tNNNN <params> = ` prefix so a report shows only the body. -/
private def body (decl : String) : String :=
  match (decl.splitOn " = ") with
  | _ :: rest => " = ".intercalate rest
  | [] => decl

/-- On a syntax error at `lineNo` in mica's printed output, find the generated
declaration containing it and return that declaration's name together with the
text minus that declaration. A declaration mica cannot print as valid OCaml is a
finding in its own right, so it is reported rather than aborting the run.

Works for both printers: the paren printer emits one line per declaration, but
the normal printer wraps `let ... in` and `match` over several, so the offending
declaration is found by scanning back to the nearest header. -/
def dropDeclAt (printed : String) (lineNo : Nat) : Option (String × String) := Id.run do
  let lines := (printed.splitOn "\n").toArray
  let mut startIdx : Option Nat := none
  for i in [0:min lineNo lines.size] do
    if (declName lines[i]!).isSome then startIdx := some i
  let some s := startIdx | return none
  let some nm := declName lines[s]! | return none
  let mut e := s + 1
  while e < lines.size && (declName lines[e]!).isNone do
    e := e + 1
  return some (nm, "\n".intercalate ((lines.toList.take s) ++ (lines.toList.drop e)))

structure Divergence where
  name   : String
  source : String
  ocaml  : String
  mica   : String

/-- Compare the two groupings, skipping fixtures mica rejected outright. -/
def compare (cases : Array Case) (rejected : Array String)
    (ocamlGroups micaGroups : Array (String × String)) : Array Divergence := Id.run do
  let ocamlMap := ocamlGroups.foldl (init := ({} : Std.HashMap String String))
    fun m (k, v) => m.insert k v
  let micaMap := micaGroups.foldl (init := ({} : Std.HashMap String String))
    fun m (k, v) => m.insert k v
  let mut out := #[]
  for c in cases do
    if rejected.contains c.name then continue
    match ocamlMap[c.name]?, micaMap[c.name]? with
    | some o, some m =>
      if o != m then
        out := out.push { name := c.name, source := body c.decl, ocaml := body o, mica := body m }
    | _, _ => pure ()
  return out

/-- Fixtures OCaml accepts and mica rejects, matched by substring, each with the
reason it is currently rejected. These are language-scope questions rather than
precedence bugs, so they are annotated here rather than left as bare failures.
Matching is deliberately loose; the reason text is what carries the meaning.

Order matters: the first matching entry wins, so the broad patterns come last. -/
def knownGaps : List (String × String) :=
  [ ("r.u <-",             "field assignment: `<-` accepts only `a.(i)` on the left")
  , ("r.u.v <-",           "field assignment: `<-` accepts only `a.(i)` on the left")
  , ("a.(i).u <-",         "field assignment: `<-` accepts only `a.(i)` on the left")
  , ("type",               "type alias: `TypeDeclBody` has only variants and records")
  , (", ",                 "bare tuple: mica builds tuples only inside parentheses") ]

/-- Classify a rejected fixture. Takes the whole declaration, not just its body,
so that a `type` alias can be told apart from an expression fixture. -/
def gapReason (decl : String) : String :=
  match knownGaps.find? fun (pat, _) => (decl.splitOn pat).length > 1 with
  | some (_, reason) => reason
  | none             => "unclassified"

-- ---------------------------------------------------------------------------
-- Entry point

/-- Read mica's printed output back through `ocamlc`, dropping any declaration it
cannot render as valid OCaml and recording the name. That is a finding in its own
right, so it is collected rather than aborting the run. -/
partial def readBack (dir : FilePath) (label printed : String)
    (bad : Array String) (budget : Nat) : IO (String × Array String) := do
  writeLines (dir / "printed.ml") #[printed]
  match ← dsource dir "printed.ml" with
  | .ok out => pure (out, bad)
  | .error e =>
    let fail := IO.userError s!"[{label}] mica's output is not valid OCaml:\n{e}"
    if budget == 0 then throw fail
    let some lineNo := ocamlErrorLine e | throw fail
    let some (nm, rest) := dropDeclAt printed lineNo | throw fail
    readBack dir label rest (bad.push nm) (budget - 1)

/-- Where the expected state of the corpus is recorded. The file is the gate: a
refactor that changes nothing must leave it untouched, and a fix must shrink it
by exactly the cells it claims to fix. -/
def baselinePath : FilePath := "Tests" / "parser" / "parser-diff.baseline"

/-- One sorted line per finding, so the file diffs cleanly and a fixture added to
the corpus does not churn the existing entries. -/
def baselineLines (parserDs printerDs : Array Divergence) (gaps unprintable : Array String)
    : Array String :=
  let d := parserDs.map fun x => s!"DIVERGE {x.source}  ==>  ocaml: {x.ocaml}  |  mica: {x.mica}"
  let p := printerDs.map fun x => s!"PRINTER {x.source}  ==>  ocaml: {x.ocaml}  |  mica: {x.mica}"
  let g := gaps.map fun s => s!"GAP     {body s}  ==>  {gapReason s}"
  let u := unprintable.map fun s => s!"UNPRINT {s}"
  (d ++ p ++ g ++ u).qsort (· < ·)

/-- Run both comparison passes over the generated corpus. -/
def run (mica : FilePath) (promote : Bool) : IO UInt32 := do
  -- Fixtures are parsed inside a temp directory, so the executable path has to
  -- survive the change of working directory.
  let mica ← IO.FS.realPath mica
  let cases := allCases
  let report ← IO.FS.withTempDir fun dir => do
    let (ocamlOut, invalid) ← match ← ocamlWithRejections dir cases (cases.map (·.decl)) #[] 40 with
      | .error e => throw <| IO.userError e
      | .ok r => pure r
    if !invalid.isEmpty then
      IO.eprintln s!"parser-diff: {invalid.size} fixture(s) are not valid OCaml (generator bug):"
      for n in invalid do
        if let some c := cases.find? (·.name == n) then IO.eprintln s!"  {n}  {body c.decl}"
    let ocamlGroups := groupByDecl ocamlOut

    -- One rejection scan, reused by both passes: whether a fixture parses does
    -- not depend on how the result is printed. `probe.ml` is left holding the
    -- corpus with rejected fixtures replaced by placeholders.
    let (parenOut, rejected) ← match ← micaWithRejections mica dir true cases
        (cases.map (·.decl)) #[] 400 with
      | .error e => throw <| IO.userError e
      | .ok r => pure r
    let normalOut ← match ← micaPrint mica dir "probe.ml" false with
      | .error e => throw <| IO.userError s!"mica failed on the cleaned corpus: {e}"
      | .ok out => pure out

    let (parenRead, parenBad) ← readBack dir "parser" parenOut #[] 40
    let (normalRead, normalBad) ← readBack dir "parser+printer" normalOut #[] 40

    let skip := rejected ++ invalid ++ parenBad ++ normalBad
    let parserDs := compare cases skip ocamlGroups (groupByDecl parenRead)
    let printerDs := compare cases skip ocamlGroups (groupByDecl normalRead)
    let gaps := rejected.filterMap fun n => (cases.find? (·.name == n)).map (·.decl)
    let unprintable := (parenBad ++ normalBad).filterMap fun n =>
      (cases.find? (·.name == n)).map (·.decl)

    let checked := cases.size - skip.size
    IO.println s!"parser-diff: {checked - parserDs.size}/{checked} fixtures agree with OCaml, \
{parserDs.size} divergent, {gaps.size} rejected by mica"
    -- A cell that the parser gets wrong but that survives a print/reparse is one
    -- where `Printer.lean` makes the matching mistake: the two errors compose
    -- back to OCaml's reading, which is why these are invisible to any test that
    -- goes through mica's own printer.
    let masked := parserDs.filter fun d => !printerDs.any (·.name == d.name)
    IO.println s!"parser-diff: {printerDs.size} of those survive mica's own printer; \
{masked.size} are masked by a matching mistake in `Printer.lean`"
    if !unprintable.isEmpty then
      IO.println s!"parser-diff: {unprintable.size} declaration(s) mica cannot print as valid OCaml"
    pure (baselineLines parserDs printerDs gaps unprintable)

  let text := "\n".intercalate report.toList ++ "\n"
  if promote then
    IO.FS.createDirAll baselinePath.parent.get!
    IO.FS.writeFile baselinePath text
    IO.println s!"parser-diff: promoted {report.size} entries to {baselinePath}"
    return 0
  if !(← baselinePath.pathExists) then
    IO.eprintln s!"parser-diff: no baseline at {baselinePath}; \
run `lake run testsuite parser-diff --promote` to create it"
    return 1
  let expected ← IO.FS.readFile baselinePath
  if expected == text then
    IO.println s!"parser-diff: matches the baseline ({report.size} known entries)"
    return 0
  IO.eprintln "parser-diff: corpus state differs from the baseline"
  let expectedLines := (expected.splitOn "\n").filter (!·.isEmpty)
  for l in report.toList do
    if !expectedLines.contains l then IO.eprintln s!"  new:  {l}"
  for l in expectedLines do
    if !report.contains l then IO.eprintln s!"  gone: {l}"
  return 1

end Testsuite.ParserDiff
