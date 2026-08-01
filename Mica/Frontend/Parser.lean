-- SUMMARY: Parsing of frontend tokens into surface syntax trees, with integrated frontend errors.
import Mica.Frontend.AST
import Mica.Frontend.Lexer

/-!
This file parses lexer tokens into the frontend AST while preserving source
locations and producing parse diagnostics in frontend terms. It is the syntax
analysis stage between tokenization and elaboration.
-/

namespace Frontend

-- ---------------------------------------------------------------------------
-- Parser error types

inductive ParseErrorKind where
  | unexpectedToken (expected : String) (got : Token)
  | unexpectedEof
  | nonPositiveProjIndex
  | funNoArgs
  | nonFinalLowercaseSegment (segment : String)
  | expectedArrayElementAssignTarget
  deriving Repr, Inhabited

structure ParseError where
  loc  : Location
  kind : ParseErrorKind
  deriving Repr, Inhabited

def ParseError.toString (e : ParseError) : String :=
  let loc := s!"{e.loc.start.file}:{e.loc.start.line}:{e.loc.start.col}"
  match e.kind with
  | .unexpectedToken exp got => s!"{loc}: expected {exp}, got '{got}'"
  | .unexpectedEof => s!"{loc}: unexpected end of file"
  | .nonPositiveProjIndex => s!"{loc}: projection index must be at least 1 (projections are 1-based)"
  | .funNoArgs => s!"{loc}: function expressions require at least one argument"
  | .nonFinalLowercaseSegment seg => s!"{loc}: qualified path segment '{seg}' is lowercase, but only the final component of a module path may be lowercase"
  | .expectedArrayElementAssignTarget => s!"{loc}: `<-` expects an array element `a.(i)` on the left"

instance : ToString ParseError := ⟨ParseError.toString⟩

-- ---------------------------------------------------------------------------
-- Frontend error (combines lex + parse errors)

inductive FrontendError where
  | lexError   (e : LexError)
  | parseError (e : ParseError)

def FrontendError.toString : FrontendError → String
  | .lexError e   => LexError.toString e
  | .parseError e => ParseError.toString e

instance : ToString FrontendError := ⟨FrontendError.toString⟩

-- ---------------------------------------------------------------------------
-- Parser state and monad

structure ParserState where
  file   : String
  tokens : Array (Location × Token)
  pos    : Nat

/-- A parser reads from a token cursor and fails with a `ParseError`. The state
is threaded by the monad; nothing below passes a `ParserState` by hand. -/
abbrev Parser (α : Type) := StateT ParserState (Except ParseError) α

-- ---------------------------------------------------------------------------
-- Primitive combinators

/-- The located token `n` positions ahead of the cursor, `eof` past the end. -/
private def peekAt (n : Nat) : Parser (Location × Token) := fun st =>
  .ok (st.tokens.getD (st.pos + n) (default, .eof), st)

/-- The token `n` positions ahead of the cursor. -/
private def peek (n : Nat := 0) : Parser Token := (·.2) <$> peekAt n

/-- The source location of the token `n` positions ahead of the cursor. -/
private def loc (n : Nat := 0) : Parser Location := (·.1) <$> peekAt n

/-- Move the cursor past one token. -/
private def advance : Parser Unit := fun st => .ok ((), { st with pos := st.pos + 1 })

/-- Fail at `l`. -/
private def failAt (l : Location) (kind : ParseErrorKind) : Parser α :=
  throw { loc := l, kind }

/-- Fail at the token under the cursor. -/
private def fail (kind : ParseErrorKind) : Parser α := do
  failAt (← loc) kind

/-- Fail reporting that `expected` was wanted where the current token stands. -/
private def expected (what : String) : Parser α := do
  fail (.unexpectedToken what (← peek))

/-- Consume `tok`, or fail naming it. -/
private def expect (tok : Token) : Parser Unit := do
  if (← peek) == tok then advance else expected s!"'{tok}'"

/-- Consume the current token if it is `tok`; report whether it was. -/
private def consumeIf (tok : Token) : Parser Bool := do
  if (← peek) == tok then advance; return true else return false

private def expectIdent : Parser String := do
  match ← peek with
  | .ident name => advance; return name
  | _ => expected "identifier"

/-- Expect an identifier whose first character is uppercase (a constructor name). -/
private def expectConstructor : Parser String := do
  match ← peek with
  | .ident name =>
    if name.front.isUpper then advance; return name
    else fail (.unexpectedToken "constructor name (uppercase)" (.ident name))
  | _ => expected "constructor name"

/-- The span from `start` to the end of the last token consumed so far. -/
private def spanFrom (start : Location) : Parser Location := fun st =>
  let stop :=
    if st.pos == 0 then start
    else (st.tokens.getD (st.pos - 1) (default, .eof)).1
  .ok ({ start := start.start, stop := stop.stop }, st)

/-- Run `p`, pairing its result with the span it consumed. -/
private def spanned (p : Parser α) : Parser (Location × α) := do
  let start ← loc
  let a ← p
  return (← spanFrom start, a)

/-- Build a node out of the kind `p` produces and the span `p` consumed. -/
private def node (mk : Location → κ → α) (p : Parser κ) : Parser α := do
  let (l, k) ← spanned p
  return mk l k

private def exprOf : Parser ExprKind → Parser Expr := node fun loc kind => { loc, kind }
private def patOf  : Parser PatternKind → Parser Pattern := node fun loc kind => { loc, kind }
private def typOf  : Parser TypKind → Parser Typ := node fun loc kind => { loc, kind }

/-- The span covering two already-built nodes. -/
private def between (a b : Location) : Location := { start := a.start, stop := b.stop }

/-- Gather a (possibly qualified) path starting with an already-consumed `head`
identifier. If `head` is uppercase, look ahead for `.dot .ident` runs and append
them. If `head` is lowercase, the path is always a single segment (a lowercase
leading ident never starts a qualified path; `x.field` stays as postfix field
access). The lookahead requires the token after `.dot` to be an identifier; a
trailing `.dot` (e.g. before a numeric projection `.1`) is left untouched.

In a module path only the final component may be lowercase (it is the
value/type/constructor name); every earlier segment is a module and must be
uppercase. So a lowercase segment terminates the path, and a lowercase segment
followed by a further `.ident` (e.g. `Foo.bar.baz`) is rejected. -/
private partial def collectPathTail (head : String) (acc : List String) : Parser Path := do
  if !head.front.isUpper then return { head, tail := acc.reverse }
  match ← peek, ← peek 1 with
  | .dot, .ident next =>
    let segLoc ← loc 1
    advance; advance
    if next.front.isUpper then
      collectPathTail head (next :: acc)
    else
      -- A lowercase segment must be the final component of the path.
      match ← peek, ← peek 1 with
      | .dot, .ident _ => failAt segLoc (.nonFinalLowercaseSegment next)
      | _, _ => return { head, tail := (next :: acc).reverse }
  | _, _ => return { head, tail := acc.reverse }

-- ---------------------------------------------------------------------------
-- Infix operators

/-- The binary operator a token introduces. `<-` is absent: it shares `:=`'s
level but builds an `arraySet` rather than a `binop`, so the loop handles it
separately. -/
private def binOpOf : Token → Option BinOp
  | .semi       => some .semi
  | .colonEq    => some .assign
  | .pipepipe   => some .or
  | .ampamp     => some .and
  | .eq         => some .eq
  | .neq        => some .neq
  | .lt         => some .lt
  | .le         => some .le
  | .gt         => some .gt
  | .ge         => some .ge
  | .pipeGt     => some .pipeRight
  | .caret      => some .concat
  | .at         => some .append
  | .atat       => some .atAt
  | .coloncolon => some .cons
  | .plus       => some .add
  | .minus      => some .sub
  | .plusDot    => some .fadd
  | .minusDot   => some .fsub
  | .star       => some .mul
  | .slash      => some .div
  | .kw_mod     => some .mod
  | .starDot    => some .fmul
  | .slashDot   => some .fdiv
  | _           => none

-- ---------------------------------------------------------------------------
-- Type parsing

private def isPatStart : Token → Bool
  | .ident _ | .underscore | .lparen | .lbrace | .intLit _ | .kw_true | .kw_false => true
  | _ => false

private def isArgStart : Token → Bool
  | .intLit _ | .floatLit _ | .charLit _ | .stringLit _ | .ident _ | .lparen | .lbrace
  | .lbracket | .kw_true | .kw_false => true
  | _ => false

/-- A record literal starts with `ident =` (a lowercase field name followed by
`=`); anything else after `{` is the expression of a record update. -/
private def isRecordLiteral : Parser Bool := do
  match ← peek with
  | .ident name =>
    if !name.front.isUpper && name.front != '\'' then return (← peek 1) == .eq else return false
  | _ => return false

mutual
-- `[@name expr]` — single `@`, optional expression payload.
private partial def parseAttr (marker : Token) : Parser Attribute := do
  let start ← loc
  expect .lbracket
  expect marker
  let name ← expectIdent
  let payload ← if (← peek) == .rbracket then pure none else some <$> parseExpr
  expect .rbracket
  return { loc := ← spanFrom start, name := AttrName.ofString name, payload }

/-- Fold trailing `[@name payload]` attributes into a node. A `[` that opens
anything else (notably a declaration attribute `[@@...]`) is left alone. -/
private partial def parseAttrSuffix (attach : α → Attribute → α) (x : α) : Parser α := do
  if (← peek) == .lbracket && (← peek 1) == .at then
    let attr ← parseAttr .at
    parseAttrSuffix attach (attach x attr)
  else return x

private partial def parseTypeAttrSuffix (t : Typ) : Parser Typ :=
  parseAttrSuffix (fun t a => { t with attrs := t.attrs ++ [a] }) t

private partial def parseTypeAtom : Parser Typ := do
  let start ← loc
  match ← peek with
  | .ident name =>
    advance
    if name.front == '\'' then
      return { loc := ← spanFrom start, kind := .var (name.toRawSubstring.drop 1 |>.toString) }
    else
      let path ← collectPathTail name []
      return { loc := ← spanFrom start, kind := .con path [] }
  | .lparen =>
    advance
    if ← consumeIf .rparen then
      return { loc := ← spanFrom start, kind := .con (Path.single "unit") [] }
    let t1 ← parseType
    match ← peek with
    | .rparen =>
      advance
      parseTypeAppSuffix t1
    | .comma =>
      let rest ← parseTypeArgList
      expect .rparen
      match ← peek with
      | .ident name =>
        advance
        let path ← collectPathTail name []
        return { loc := ← spanFrom start, kind := .con path (t1 :: rest) }
      | _ => expected "type constructor after '(T1,T2,...)'"
    | _ => expected "')' or ',' in type"
  | _ => expected "type"

private partial def parseTypeAppSuffix (arg : Typ) : Parser Typ := do
  match ← peek with
  | .ident name =>
    if !name.front.isUpper && name.front != '\'' then
      advance
      let loc ← spanFrom arg.loc
      parseTypeAppSuffix { loc, kind := .con (Path.single name) [arg] }
    else return arg
  | _ => return arg

private partial def parseTypeApp : Parser Typ := do
  parseTypeAttrSuffix (← parseTypeAppSuffix (← parseTypeAtom))

private partial def parseTypeProdRest : Parser (List Typ) := do
  let t ← parseTypeApp
  if ← consumeIf .star then return t :: (← parseTypeProdRest) else return [t]

private partial def parseTypeProd : Parser Typ := do
  let start ← loc
  let comps ← parseTypeProdRest
  match comps with
  | [t] => return t
  | _   => return { loc := ← spanFrom start, kind := .tuple comps }

private partial def parseTypeArgList : Parser (List Typ) := do
  if ← consumeIf .comma then
    let t ← parseType
    return t :: (← parseTypeArgList)
  else return []

/-- Parse a type expression (including arrows). -/
private partial def parseType : Parser Typ := do
  let t ← parseTypeProd
  if ← consumeIf .arrow then
    let u ← parseType
    return { loc := between t.loc u.loc, kind := .arrow t u }
  else return t

/-- Parse a type expression, excluding arrows.
    Used for return type annotations where `->` is ambiguous with the function arrow. -/
private partial def parseTypeNoArrow : Parser Typ := parseTypeProd

-- ---------------------------------------------------------------------------
-- Pattern parsing

private partial def parsePattern : Parser Pattern := do
  let start ← loc
  match ← peek with
  | .underscore => advance; return { loc := ← spanFrom start, kind := .wildcard }
  | .ident name =>
    advance
    if name.front.isUpper then
      -- constructor pattern (possibly qualified, e.g. `Option.Some x`)
      let path ← collectPathTail name []
      match ← peek with
      | .ident _ | .underscore | .intLit _ | .charLit _ | .kw_true | .kw_false
      | .lparen | .lbrace =>
        let payload ← parsePattern
        return { loc := ← spanFrom start, kind := .ctor path (some payload) }
      | _ => return { loc := ← spanFrom start, kind := .ctor path none }
    else
      -- plain binder (no type annotation here; annotated form is `(x : T)`)
      return { loc := ← spanFrom start, kind := .binder (some name) none }
  | .intLit n  => advance; return { loc := ← spanFrom start, kind := .const (.int n) }
  | .charLit c => advance; return { loc := ← spanFrom start, kind := .const (.char c) }
  | .kw_true   => advance; return { loc := ← spanFrom start, kind := .const (.bool true) }
  | .kw_false  => advance; return { loc := ← spanFrom start, kind := .const (.bool false) }
  | .lparen => advance; parseParenPattern start "')' or ',' in pattern"
  | .lbrace =>
    advance
    let fields ← parseRecordPatFields
    expect .rbrace
    return { loc := ← spanFrom start, kind := .record fields }
  | .lbracket =>
    -- `[]` — empty-list pattern (no general list-literal patterns)
    advance
    if ← consumeIf .rbracket then return { loc := ← spanFrom start, kind := .nil }
    else expected "']' in pattern"
  | _ => expected "pattern"

/-- The body of a parenthesized pattern, with the `(` already consumed. `unclosed`
names the error for a stray token where `)` or `,` was due. -/
private partial def parseParenPattern (start : Location) (unclosed : String) : Parser Pattern := do
  -- `()` = unit constant
  if ← consumeIf .rparen then return { loc := ← spanFrom start, kind := .const .unit }
  let pat ← parsePatternInner
  match ← peek with
  | .comma =>
    -- tuple pattern
    let rest ← parseTuplePatRest
    expect .rparen
    return { loc := ← spanFrom start, kind := .tuple (pat :: rest) }
  | .rparen => advance; return pat
  | _ => expected unclosed

-- pattern inside parens: allows `(x : T)` annotated binder
private partial def parsePatternInner : Parser Pattern := do
  let start ← loc
  match ← peek with
  | .ident name =>
    advance
    let ty ← if ← consumeIf .colon then some <$> parseType else pure none
    return { loc := ← spanFrom start, kind := .binder (some name) ty }
  | .underscore =>
    advance
    if ← consumeIf .colon then
      let ty ← parseType
      return { loc := ← spanFrom start, kind := .binder none (some ty) }
    else return { loc := ← spanFrom start, kind := .wildcard }
  | _ => parsePattern

private partial def parseTuplePatRest : Parser (List Pattern) := do
  if ← consumeIf .comma then
    let p ← parsePattern
    return p :: (← parseTuplePatRest)
  else return []

private partial def parseRecordPatFields : Parser (List (FieldName × Pattern)) := do
  let name ← expectIdent
  expect .eq
  let pat ← parsePattern
  if ← consumeIf .semi then
    -- A trailing `;` leaves the `}` for the caller's `expect .rbrace`.
    if (← peek) == .rbrace then return [(name, pat)]
    else return (name, pat) :: (← parseRecordPatFields)
  else return [(name, pat)]

/-- Pattern with infix `::` (right-assoc): `p1 :: p2` is the prelude cons
    constructor applied to the pair pattern `(p1, p2)`. Constructor payloads
    bind tighter, so only match arms use this entry point. -/
private partial def parsePatternCons : Parser Pattern := do
  let lhs ← parsePattern
  if ← consumeIf .coloncolon then
    let rhs ← parsePatternCons
    return { loc := between lhs.loc rhs.loc, kind := .cons lhs rhs }
  else return lhs

-- ---------------------------------------------------------------------------
-- Shared binder helpers
-- These are top-level so both parseExpr (parseLet/parseFun) and parseDecl
-- (parseValDecl) can call them directly.

private partial def parsePatternBinder : Parser Pattern := do
  let start ← loc
  match ← peek with
  | .underscore => advance; return { loc := ← spanFrom start, kind := .wildcard }
  | .ident name => advance; return { loc := ← spanFrom start, kind := .binder (some name) none }
  | .lparen => advance; parseParenPattern start "')' in binder"
  | .lbrace =>
    advance
    let fields ← parseRecordPatFields
    expect .rbrace
    return { loc := ← spanFrom start, kind := .record fields }
  | _ => expected "binder"

private partial def parseFunArgs : Parser (List Pattern) := do
  if isPatStart (← peek) then
    let p ← parsePatternBinder
    return p :: (← parseFunArgs)
  else return []

private partial def parseOptRetTy : Parser (Option Typ) := do
  if ← consumeIf .colon then some <$> parseTypeNoArrow else pure none

-- ---------------------------------------------------------------------------
-- Expression parsing

/-- A whole expression, `;` included. -/
private partial def parseExpr : Parser Expr := parseExprAt (BinOp.level .semi)

/-- Precedence climbing over `BinOp.level` / `BinOp.assoc`: parse an operand,
then extend it with every following operator at level `min` or tighter. -/
private partial def parseExprAt (min : Nat) : Parser Expr := do
  parseInfix min (← parseOperand)

private partial def parseInfix (min : Nat) (lhs : Expr) : Parser Expr := do
  match ← peek with
  -- `a.(i) <- e`, at `:=`'s level and right-associative like it.
  | .leftArrow =>
    let lvl := BinOp.level .assign
    if lvl < min then return lhs
    advance
    let rhs ← parseExprAt lvl
    match lhs.kind with
    | .arrayGet arr idx =>
      parseInfix min { loc := between lhs.loc rhs.loc, kind := .arraySet arr idx rhs }
    | _ => failAt lhs.loc .expectedArrayElementAssignTarget
  | tok =>
    let some op := binOpOf tok | return lhs
    if BinOp.level op < min then return lhs
    advance
    let rhs ← parseExprAt (BinOp.operandLevels op).2
    parseInfix min { loc := between lhs.loc rhs.loc, kind := .binop op lhs rhs }

/-- The operand of the infix loop.

A keyword expression is an operand at every level, matching OCaml, where the
grammar admits `let`, `fun`, `if` and `match` after any operator even though
they sit below all of them. Its trailing branch then extends as far right as it
can, so `a + if b then c else d * e` reads as `a + (if b then c else (d * e))`.
The loop needs no case for that: the branch is parsed at a fixed level, leaving
only looser operators behind, which the loop already declines. -/
private partial def parseOperand : Parser Expr := do
  match ← peek with
  | .kw_let   => parseLet
  | .kw_fun   => parseFun
  | .kw_if    => parseIf
  | .kw_match => parseMatch
  | _         => parseUnary

-- prefix unary operators
private partial def parseUnary : Parser Expr := do
  let unop (op : UnOp) : Parser Expr := exprOf do
    advance
    return .unop op (← parseUnary)
  match ← peek with
  | .minus     => unop .neg
  | .kw_assert => unop .assert
  | .bang      => unop .deref
  | _          => parseApp

-- function application (left-assoc, juxtaposition), then any expression
-- attributes `[@name payload]` attached as a postfix to the whole application.
private partial def parseApp : Parser Expr := do
  let fn ← parsePostfix
  let app ← parseAppRest fn
  parseAttrSuffix (fun e a => { e with attrs := e.attrs ++ [a] }) app

private partial def parseAppRest (fn : Expr) : Parser Expr := do
  let args ← collectArgs
  if args.isEmpty then return fn
  else return { loc := ← spanFrom fn.loc, kind := .app fn args }

private partial def collectArgs : Parser (List Expr) := do
  -- `[` starts a list-literal argument unless it opens an attribute `[@...]`
  let t ← peek
  let isAttr := t == .lbracket && ((← peek 1) == .at || (← peek 1) == .atat)
  if isArgStart t && !isAttr then
    let arg ← parsePostfix
    return arg :: (← collectArgs)
  else return []

-- postfix: `.n` tuple projection, `.field` field access
private partial def parsePostfix : Parser Expr := do
  parsePostfixRest (← parseAtom)

private partial def parsePostfixRest (e : Expr) : Parser Expr := do
  if (← peek) != .dot then return e
  match ← peek 1 with
  | .lparen =>
    advance; advance
    let idx ← parseExpr
    expect .rparen
    parsePostfixRest { loc := ← spanFrom e.loc, kind := .arrayGet e idx }
  | .intLit n =>
    if n ≥ 1 then
      advance; advance
      parsePostfixRest { loc := ← spanFrom e.loc, kind := .unop (.proj n.toNat) e }
    else
      failAt (← loc 1) .nonPositiveProjIndex
  | .ident fname =>
    advance; advance
    parsePostfixRest { loc := ← spanFrom e.loc, kind := .unop (.field fname) e }
  | _ => return e  -- lone dot, leave it

-- atom: constants, variables, constructors, parens, records
private partial def parseAtom : Parser Expr := do
  let start ← loc
  let const (c : Const) : Parser Expr := do
    advance; return { loc := ← spanFrom start, kind := .const c }
  match ← peek with
  | .intLit n    => const (.int n)
  | .floatLit f  => const (.float f)
  | .charLit c   => const (.char c)
  | .stringLit s => const (.string s)
  | .kw_true     => const (.bool true)
  | .kw_false    => const (.bool false)
  | .ident name =>
    advance
    let path ← collectPathTail name []
    return { loc := ← spanFrom start
           , kind := if path.last.front.isUpper then .ctor path else .var path }
  | .lbrace => parseRecord
  | .lbracket =>
    -- list literal `[]` / `[e1; e2; ...]`; elaboration lowers it to constructors
    advance
    if ← consumeIf .rbracket then return { loc := ← spanFrom start, kind := .list [] }
    let elems ← parseListElems
    expect .rbracket
    return { loc := ← spanFrom start, kind := .list elems }
  | .lparen =>
    advance
    -- `()` = unit
    if ← consumeIf .rparen then return { loc := ← spanFrom start, kind := .const .unit }
    let e ← parseExpr
    match ← peek with
    | .comma =>
      -- tuple
      let rest ← parseTupleRest
      expect .rparen
      return { loc := ← spanFrom start, kind := .tuple (e :: rest) }
    | .colon =>
      -- type annotation `(e : T)`
      advance
      let ty ← parseType
      expect .rparen
      return { loc := ← spanFrom start, kind := .annot e ty }
    | .rparen => advance; return e
    | _ => expected "')' or ',' in expression"
  | _ => expected "expression"

private partial def parseTupleRest : Parser (List Expr) := do
  if ← consumeIf .comma then
    let e ← parseExpr
    return e :: (← parseTupleRest)
  else return []

-- `;`-separated list-literal elements, allowing a trailing `;`
private partial def parseListElems : Parser (List Expr) := do
  let e ← parseExprAt Prec.noSemi
  if ← consumeIf .semi then
    if (← peek) == .rbracket then return [e]
    else return e :: (← parseListElems)
  else return [e]

-- `{ f1 = e1; f2 = e2 }` or `{ e with f1 = e1; ... }`
-- Lookahead approach: peek to distinguish record literal from record update.
-- A record literal starts with `ident =` (lowercase field name followed by `=`).
-- Anything else is treated as an expression for record update.
private partial def parseRecord : Parser Expr := do
  let start ← loc
  expect .lbrace
  if ← isRecordLiteral then
    let fields ← parseRecordFields
    expect .rbrace
    return { loc := ← spanFrom start, kind := .record fields }
  else
    let e ← parseExpr
    expect .kw_with
    let fields ← parseRecordFields
    expect .rbrace
    return { loc := ← spanFrom start, kind := .recordUpdate e fields }

private partial def parseRecordFields : Parser (List (FieldName × Expr)) := do
  let name ← expectIdent
  expect .eq
  let e ← parseExprAt Prec.noSemi
  if ← consumeIf .semi then
    if (← peek) == .rbrace then return [(name, e)]  -- trailing semicolon
    else return (name, e) :: (← parseRecordFields)
  else return [(name, e)]

-- `let [rec] pat pat ... [: T] = e in body`
private partial def parseLet : Parser Expr := exprOf do
  expect .kw_let
  let isRec ← consumeIf .kw_rec
  let first ← parsePatternBinder
  let rest ← parseFunArgs
  let retTy ← parseOptRetTy
  expect .eq
  let bound ← parseExpr
  expect .kw_in
  let body ← parseExpr
  return .letIn isRec (first :: rest) retTy bound body

-- `fun pat pat ... [: T] -> body`
private partial def parseFun : Parser Expr := exprOf do
  let start ← loc
  expect .kw_fun
  let args ← parseFunArgs
  if args.isEmpty then failAt start .funNoArgs
  let retTy ← parseOptRetTy
  expect .arrow
  return .fun_ args retTy (← parseExpr)

-- `if c then t else e`
-- The branches stop at `;`, which is looser than `if` in OCaml, so
-- `if a then b else c; d` sequences the whole `if`. The condition is delimited
-- by `then` instead, so it takes a full expression.
private partial def parseIf : Parser Expr := exprOf do
  expect .kw_if
  let cond ← parseExpr
  expect .kw_then
  let thn ← parseExprAt Prec.noSemi
  expect .kw_else
  return .ite cond thn (← parseExprAt Prec.noSemi)

-- `match e with | P -> e | ...`
private partial def parseMatch : Parser Expr := exprOf do
  expect .kw_match
  let scrut ← parseExpr
  expect .kw_with
  return .match_ scrut (← parseMatchArms)

private partial def parseMatchArms : Parser (List MatchArm) := do
  if ← consumeIf .pipe then
    let pat ← parsePatternCons
    expect .arrow
    let body ← parseExpr
    return { pat, body } :: (← parseMatchArms)
  else return []

end

-- ---------------------------------------------------------------------------
-- Declaration parsing

private def parseOpenDecl : Parser DeclKind := do
  expect .kw_open
  let head ← expectIdent
  return .open_ (← collectPathTail head [])

private partial def parseTypeParamList : Parser (List TypeVariable) := do
  match ← peek with
  | .ident name =>
    if name.front == '\'' then
      advance
      let varName := name.toRawSubstring.drop 1 |>.toString
      if ← consumeIf .comma then return varName :: (← parseTypeParamList)
      else return [varName]
    else return []
  | _ => return []

/-- Optional type parameters: `'a`, `('a, 'b)`, etc. A `(` that does not open a
parameter list is left for the caller. -/
private def parseTypeParams : Parser (List TypeVariable) := do
  match ← peek with
  | .ident name =>
    if name.front == '\'' then
      advance
      return [name.toRawSubstring.drop 1 |>.toString]
    else return []
  | .lparen =>
    match ← peek 1 with
    | .ident name =>
      if name.front == '\'' then
        advance
        let params ← parseTypeParamList
        expect .rparen
        return params
      else return []
    | _ => return []
  | _ => return []

private partial def parseRecordBodyFields : Parser (List (FieldName × Typ)) := do
  let name ← expectIdent
  expect .colon
  let ty ← parseType
  if ← consumeIf .semi then
    if (← peek) == .rbrace then return [(name, ty)]  -- trailing semicolon
    else return (name, ty) :: (← parseRecordBodyFields)
  else return [(name, ty)]

private partial def parseCtors : Parser (List (Constructor × Option Typ)) := do
  let name ← expectConstructor
  let payload ← if ← consumeIf .kw_of then some <$> parseType else pure none
  if ← consumeIf .pipe then return (name, payload) :: (← parseCtors)
  else return [(name, payload)]

private def parseTypeDeclBody : Parser TypeDeclBody := do
  if ← consumeIf .lbrace then
    let fields ← parseRecordBodyFields
    expect .rbrace
    return .record fields
  else
    -- optional leading `|`
    let _ ← consumeIf .pipe
    return .variant (← parseCtors)

private def parseTypeDecl : Parser DeclKind := do
  expect .kw_type
  let params ← parseTypeParams
  let name ← expectIdent
  expect .eq
  return .type_ { params, name, body := ← parseTypeDeclBody }

private def parseValDecl : Parser DeclKind := do
  expect .kw_let
  let isRec ← consumeIf .kw_rec
  let first ← parsePatternBinder
  let rest ← parseFunArgs
  let retTy ← parseOptRetTy
  expect .eq
  return .val_ isRec (first :: rest) retTy (← parseExpr)

/-- Trailing `[@@name payload]` attributes on a declaration. -/
private partial def parseDeclAttrs : Parser (List Attribute) := do
  if (← peek) == .lbracket && (← peek 1) == .atat then
    let attr ← parseAttr .atat
    return attr :: (← parseDeclAttrs)
  else return []

/-- Parse a single top-level declaration.

Only `let` declarations take `[@@...]` attributes today; `type` and `open` reject
a following `[`. That is a language-scope question rather than a parsing one, so
it is left as-is here. -/
private def parseDecl : Parser Decl := do
  let start ← loc
  match ← peek with
  | .kw_let =>
    let kind ← parseValDecl
    let attrs ← parseDeclAttrs
    return { loc := ← spanFrom start, kind, attrs }
  | .kw_open => return { loc := ← spanFrom start, kind := ← parseOpenDecl, attrs := [] }
  | .kw_type => return { loc := ← spanFrom start, kind := ← parseTypeDecl, attrs := [] }
  | _ => expected "declaration (open, let, or type)"

-- ---------------------------------------------------------------------------
-- Top-level program parsing

/-- Parse a sequence of top-level declarations. -/
private partial def parseProgram : Parser Program := do
  match ← peek with
  | .eof => return []
  | .semisemi => advance; parseProgram
  | .kw_open | .kw_let | .kw_type =>
    let decl ← parseDecl
    -- skip optional `;;`
    let _ ← consumeIf .semisemi
    return decl :: (← parseProgram)
  | _ => expected "declaration"

/-- Lex and parse `source` (file named `file`). -/
def parseFile (file : String) (source : String) : Except FrontendError Program := do
  let tokens ← (tokenize file source).mapError .lexError
  let st : ParserState := { file, tokens, pos := 0 }
  let (prog, _) ← (parseProgram st).mapError .parseError
  .ok prog

end Frontend
