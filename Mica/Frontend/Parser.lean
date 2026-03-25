import Mica.Frontend.AST
import Mica.Frontend.Lexer

namespace Frontend

-- ---------------------------------------------------------------------------
-- Parser error types

inductive ParseErrorKind where
  | unexpectedToken (expected : String) (got : Token)
  | unexpectedEof
  | invalidRecordField
  | negativeProjIndex
  | letRecNoArgs
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
  | .invalidRecordField => s!"{loc}: expected field name (identifier) before '=' in record literal"
  | .negativeProjIndex => s!"{loc}: projection index must be non-negative"
  | .letRecNoArgs => s!"{loc}: let rec without arguments is not supported"

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

abbrev Parser (α : Type) := ParserState → Except ParseError (α × ParserState)

-- ---------------------------------------------------------------------------
-- Primitive combinators

private def peekTok (st : ParserState) : Token :=
  (st.tokens.getD st.pos (default, .eof)).2

private def peekLoc (st : ParserState) : Location :=
  (st.tokens.getD st.pos (default, .eof)).1

private def advance (st : ParserState) : ParserState :=
  { st with pos := st.pos + 1 }

private def expect (tok : Token) (st : ParserState) : Except ParseError ParserState :=
  let t := peekTok st
  if t == tok then .ok (advance st)
  else .error { loc := peekLoc st, kind := .unexpectedToken s!"'{tok}'" t }

private def expectIdent (st : ParserState) : Except ParseError (String × ParserState) :=
  match peekTok st with
  | .ident name => .ok (name, advance st)
  | t => .error { loc := peekLoc st, kind := .unexpectedToken "identifier" t }

/-- Expect an identifier whose first character is uppercase (a constructor name). -/
private def expectConstructor (st : ParserState) : Except ParseError (String × ParserState) :=
  match peekTok st with
  | .ident name =>
    if name.front.isUpper then .ok (name, advance st)
    else .error { loc := peekLoc st, kind := .unexpectedToken "constructor name (uppercase)" (.ident name) }
  | t => .error { loc := peekLoc st, kind := .unexpectedToken "constructor name" t }

/-- Span from `start` location to the end of the last consumed token. -/
private def spanTo (start : Location) (st : ParserState) : Location :=
  -- The last consumed token is at pos - 1
  let stopLoc :=
    if st.pos == 0 then start
    else (st.tokens.getD (st.pos - 1) (default, .eof)).1
  { start := start.start, stop := stopLoc.stop }

private def mkExpr (start : Location) (st : ParserState) (k : ExprKind) : Expr :=
  { loc := spanTo start st, kind := k }

private def mkPat (start : Location) (st : ParserState) (k : PatternKind) : Pattern :=
  { loc := spanTo start st, kind := k }

private def mkTyp (start : Location) (st : ParserState) (k : TypKind) : Typ :=
  { loc := spanTo start st, kind := k }

-- ---------------------------------------------------------------------------
-- Left-assoc binary expression helper

private partial def parseLAssocLoop
    (ops : List (Token × BinOp)) (sub : Parser Expr) (lhs : Expr) : Parser Expr :=
  fun st =>
    match ops.find? (·.1 == peekTok st) with
    | some (_, op) => do
      let st' := advance st
      let (rhs, st') ← sub st'
      let e : Expr := { loc := { start := lhs.loc.start, stop := rhs.loc.stop }, kind := .binop op lhs rhs }
      parseLAssocLoop ops sub e st'
    | none => .ok (lhs, st)

private partial def parseLAssoc (ops : List (Token × BinOp)) (sub : Parser Expr) : Parser Expr :=
  fun st => do
    let (lhs, st) ← sub st
    parseLAssocLoop ops sub lhs st

-- ---------------------------------------------------------------------------
-- Type parsing

mutual
partial def parseTypeAtom : Parser Typ := fun st =>
  let p := peekLoc st
  match peekTok st with
  | .ident name =>
    if name.front == '\'' then
      let varName := name.toRawSubstring.drop 1 |>.toString
      .ok (mkTyp p (advance st) (.var varName), advance st)
    else
      .ok (mkTyp p (advance st) (.con name []), advance st)
  | .lparen =>
    let st' := advance st
    if peekTok st' == .rparen then
      .ok (mkTyp p (advance st') (.con "unit" []), advance st')
    else do
      let (t1, st') ← parseType st'
      match peekTok st' with
      | .rparen =>
        let st'' := advance st'
        parseTypeAppSuffix t1 st''
      | .comma =>
        let (rest, st') ← parseTypeArgList st'
        let st' ← expect .rparen st'
        match peekTok st' with
        | .ident name =>
          let args := t1 :: rest
          let st'' := advance st'
          let loc : Location := { start := p.start, stop := (spanTo p st'').stop }
          .ok ({ loc, kind := .con name args }, st'')
        | t => .error { loc := peekLoc st', kind := .unexpectedToken "type constructor after '(T1,T2,...)'" t }
      | t => .error { loc := peekLoc st', kind := .unexpectedToken "')' or ',' in type" t }
  | t =>
    .error { loc := peekLoc st, kind := .unexpectedToken "type" t }

partial def parseTypeAppSuffix (arg : Typ) : Parser Typ := fun st =>
  match peekTok st with
  | .ident name =>
    if !name.front.isUpper && name.front != '\'' then
      let startLoc := arg.loc
      let st' := advance st
      let loc : Location := { start := startLoc.start, stop := (spanTo startLoc st').stop }
      parseTypeAppSuffix { loc, kind := .con name [arg] } st'
    else .ok (arg, st)
  | _ => .ok (arg, st)

partial def parseTypeApp : Parser Typ := fun st => do
  let (t, st) ← parseTypeAtom st
  parseTypeAppSuffix t st

partial def parseTypeProdRest : Parser (List Typ) := fun st => do
  let (t, st) ← parseTypeApp st
  match peekTok st with
  | .star =>
    let (rest, st) ← parseTypeProdRest (advance st)
    .ok (t :: rest, st)
  | _ => .ok ([t], st)

partial def parseTypeProd : Parser Typ := fun st => do
  let (t, st) ← parseTypeApp st
  match peekTok st with
  | .star =>
    let (rest, st) ← parseTypeProdRest (advance st)
    let components := t :: rest
    let loc : Location := { start := t.loc.start, stop := (spanTo t.loc st).stop }
    .ok ({ loc, kind := .tuple components }, st)
  | _ => .ok (t, st)

partial def parseTypeArgList : Parser (List Typ) := fun st =>
  match peekTok st with
  | .comma => do
    let (t, st) ← parseType (advance st)
    let (rest, st) ← parseTypeArgList st
    .ok (t :: rest, st)
  | _ => .ok ([], st)

/-- Parse a type expression (including arrows). -/
partial def parseType : Parser Typ := fun st => do
  let (t, st) ← parseTypeProd st
  match peekTok st with
  | .arrow =>
    let (u, st) ← parseType (advance st)
    let loc : Location := { start := t.loc.start, stop := u.loc.stop }
    .ok ({ loc, kind := .arrow t u }, st)
  | _ => .ok (t, st)
end

/-- Parse a type expression, excluding arrows.
    Used for return type annotations where `->` is ambiguous with the function arrow. -/
def parseTypeNoArrow : Parser Typ := parseTypeProd

-- ---------------------------------------------------------------------------
-- Pattern parsing

partial def parsePattern : Parser Pattern := fun st =>
  let p := peekLoc st
  match peekTok st with
  | .underscore =>
    .ok (mkPat p (advance st) .wildcard, advance st)
  | .ident name =>
    if name.front.isUpper then
      -- constructor pattern
      let st' := advance st
      match peekTok st' with
      | .ident _ | .underscore | .intLit _ | .charLit _ | .kw_true | .kw_false | .lparen => do
        let (payload, st'') ← parsePattern st'
        .ok (mkPat p st'' (.ctor name (some payload)), st'')
      | _ =>
        .ok (mkPat p st' (.ctor name none), st')
    else
      -- plain binder (no type annotation here; annotated form is `(x : T)`)
      .ok (mkPat p (advance st) (.binder (some name) none), advance st)
  | .intLit n =>
    .ok (mkPat p (advance st) (.const (.int n)), advance st)
  | .charLit c =>
    .ok (mkPat p (advance st) (.const (.char c)), advance st)
  | .kw_true =>
    .ok (mkPat p (advance st) (.const (.bool true)), advance st)
  | .kw_false =>
    .ok (mkPat p (advance st) (.const (.bool false)), advance st)
  | .lparen =>
    let st' := advance st
    -- `()` = unit constant
    if peekTok st' == .rparen then
      .ok (mkPat p (advance st') (.const .unit), advance st')
    else do
      let (pat, st') ← parsePatternInner st'
      match peekTok st' with
      | .comma =>
        -- tuple pattern
        let (rest, st') ← parseTuplePatRest st'
        let st' ← expect .rparen st'
        .ok (mkPat p st' (.tuple (pat :: rest)), st')
      | .rparen =>
        .ok (pat, advance st')
      | t =>
        .error { loc := peekLoc st', kind := .unexpectedToken "')' or ',' in pattern" t }
  | t =>
    .error { loc := peekLoc st, kind := .unexpectedToken "pattern" t }
where
  -- pattern inside parens: allows `(x : T)` annotated binder
  parsePatternInner : Parser Pattern := fun st =>
    let p := peekLoc st
    match peekTok st with
    | .ident name =>
      let st' := advance st
      match peekTok st' with
      | .colon => do
        let (ty, st') ← parseType (advance st')
        .ok (mkPat p st' (.binder (some name) (some ty)), st')
      | _ =>
        .ok (mkPat p st' (.binder (some name) none), st')
    | .underscore =>
      let st' := advance st
      match peekTok st' with
      | .colon => do
        let (ty, st') ← parseType (advance st')
        .ok (mkPat p st' (.binder none (some ty)), st')
      | _ =>
        .ok (mkPat p st' .wildcard, st')
    | _ => parsePattern st

  parseTuplePatRest : Parser (List Pattern) := fun st =>
    match peekTok st with
    | .comma => do
      let (p, st) ← parsePattern (advance st)
      let (rest, st) ← parseTuplePatRest st
      .ok (p :: rest, st)
    | _ => .ok ([], st)

-- ---------------------------------------------------------------------------
-- Shared binder helpers
-- These are top-level so both parseExpr (parseLet/parseFun) and parseDecl
-- (parseValDecl) can call them directly.

private def isPatStart : Token → Bool
  | .ident _ | .underscore | .lparen | .intLit _ | .kw_true | .kw_false => true
  | _ => false

private partial def parsePatternBinder : Parser Pattern := fun st =>
  let p := peekLoc st
  match peekTok st with
  | .underscore => .ok (mkPat p (advance st) .wildcard, advance st)
  | .ident name => .ok (mkPat p (advance st) (.binder (some name) none), advance st)
  | .lparen =>
    let st' := advance st
    -- `()` is unit
    if peekTok st' == .rparen then
      .ok (mkPat p (advance st') (.const .unit), advance st')
    else do
      let (pat, st') ← parsePattern.parsePatternInner st'
      match peekTok st' with
      | .comma =>
        let (rest, st') ← parsePattern.parseTuplePatRest st'
        let st' ← expect .rparen st'
        .ok (mkPat p st' (.tuple (pat :: rest)), st')
      | .rparen => .ok (pat, advance st')
      | t =>
        .error { loc := peekLoc st', kind := .unexpectedToken "')' in binder" t }
  | t =>
    .error { loc := peekLoc st, kind := .unexpectedToken "binder" t }

private partial def parseFunArgs : Parser (List Pattern) := fun st =>
  if isPatStart (peekTok st) then do
    let (p, st) ← parsePatternBinder st
    let (rest, st) ← parseFunArgs st
    .ok (p :: rest, st)
  else .ok ([], st)

private partial def parseOptRetTy : Parser (Option Typ) := fun st =>
  match peekTok st with
  | .colon => do
    let (ty, st) ← parseTypeNoArrow (advance st)
    .ok (some ty, st)
  | _ => .ok (none, st)

-- ---------------------------------------------------------------------------
-- Expression parsing

-- Forward declaration for mutual recursion via partial
partial def parseExpr : Parser Expr := fun st => do
  let (lhs, st) ← parseExprNoSemi st
  match peekTok st with
  | .semi => do
    let (rhs, st) ← parseExpr (advance st)
    let loc : Location := { start := lhs.loc.start, stop := rhs.loc.stop }
    .ok ({ loc, kind := .binop .semi lhs rhs }, st)
  | _ => .ok (lhs, st)

where
  -- Expression without top-level `;` — keywords and operators, but not `;`.
  parseExprNoSemi : Parser Expr := fun st =>
    match peekTok st with
    | .kw_let   => parseLet st
    | .kw_fun   => parseFun st
    | .kw_if    => parseIf st
    | .kw_match => parseMatch st
    | _         => parseAssign st

  -- `:=` right-assoc
  parseAssign : Parser Expr := fun st => do
    let (lhs, st) ← parseOr st
    match peekTok st with
    | .colonEq => do
      let (rhs, st) ← parseAssign (advance st)
      let loc : Location := { start := lhs.loc.start, stop := rhs.loc.stop }
      .ok ({ loc, kind := .binop .assign lhs rhs }, st)
    | _ => .ok (lhs, st)

  -- `||` right-assoc
  parseOr : Parser Expr := fun st => do
    let (lhs, st) ← parseAnd st
    match peekTok st with
    | .pipepipe => do
      let (rhs, st) ← parseOr (advance st)
      let loc : Location := { start := lhs.loc.start, stop := rhs.loc.stop }
      .ok ({ loc, kind := .binop .or lhs rhs }, st)
    | _ => .ok (lhs, st)

  -- `&&` right-assoc
  parseAnd : Parser Expr := fun st => do
    let (lhs, st) ← parsePipeGt st
    match peekTok st with
    | .ampamp => do
      let (rhs, st) ← parseAnd (advance st)
      let loc : Location := { start := lhs.loc.start, stop := rhs.loc.stop }
      .ok ({ loc, kind := .binop .and lhs rhs }, st)
    | _ => .ok (lhs, st)

  -- `|>` left-assoc
  parsePipeGt : Parser Expr := fun st => do
    let (lhs, st) ← parseAtAt st
    parsePipeGtRest lhs st

  parsePipeGtRest (lhs : Expr) : Parser Expr := fun st =>
    match peekTok st with
    | .pipeGt => do
      let (rhs, st) ← parseAtAt (advance st)
      let loc : Location := { start := lhs.loc.start, stop := rhs.loc.stop }
      parsePipeGtRest { loc, kind := .binop .pipeRight lhs rhs } st
    | _ => .ok (lhs, st)

  -- `@@` right-assoc
  parseAtAt : Parser Expr := fun st => do
    let (lhs, st) ← parseCmp st
    match peekTok st with
    | .atat => do
      -- RHS is full expr so `f @@ fun x -> e` works
      let (rhs, st) ← parseExpr (advance st)
      let loc : Location := { start := lhs.loc.start, stop := rhs.loc.stop }
      .ok ({ loc, kind := .binop .atAt lhs rhs }, st)
    | _ => .ok (lhs, st)

  -- comparison (left-assoc)
  parseCmp : Parser Expr :=
    parseLAssoc [(.eq, .eq), (.neq, .neq), (.lt, .lt), (.le, .le), (.gt, .gt), (.ge, .ge)] parseAdd

  -- `+` `-` left-assoc
  parseAdd : Parser Expr :=
    parseLAssoc [(.plus, .add), (.minus, .sub)] parseMul

  -- `*` `/` `mod` left-assoc
  parseMul : Parser Expr :=
    parseLAssoc [(.star, .mul), (.slash, .div), (.kw_mod, .mod)] parseUnary

  -- prefix unary operators
  parseUnary : Parser Expr := fun st =>
    let p := peekLoc st
    match peekTok st with
    | .minus => do
      let (e, st) ← parseUnary (advance st)
      .ok (mkExpr p st (.unop .neg e), st)
    | .kw_assert => do
      let (e, st) ← parseUnary (advance st)
      .ok (mkExpr p st (.unop .assert e), st)
    | .bang => do
      let (e, st) ← parseUnary (advance st)
      .ok (mkExpr p st (.unop .deref e), st)
    | _ => parseApp st

  -- function application (left-assoc, juxtaposition)
  parseApp : Parser Expr := fun st => do
    let (fn, st) ← parsePostfix st
    parseAppRest fn st

  parseAppRest (fn : Expr) : Parser Expr := fun st => do
    let (args, st) ← collectArgs st
    if args.isEmpty then .ok (fn, st)
    else
      let loc : Location := { start := fn.loc.start, stop := (spanTo fn.loc st).stop }
      .ok ({ loc, kind := .app fn args }, st)

  collectArgs : Parser (List Expr) := fun st =>
    if isArgStart (peekTok st) then do
      let (arg, st) ← parsePostfix st
      let (rest, st) ← collectArgs st
      .ok (arg :: rest, st)
    else .ok ([], st)

  isArgStart : Token → Bool
    | .intLit _ | .charLit _ | .ident _ | .lparen | .lbrace
    | .kw_true | .kw_false => true
    | _ => false

  -- postfix: `.n` tuple projection, `.field` field access
  parsePostfix : Parser Expr := fun st => do
    let (e, st) ← parseAtom st
    parsePostfixRest e st

  parsePostfixRest (e : Expr) : Parser Expr := fun st =>
    match peekTok st with
    | .dot =>
      let st' := advance st
      match peekTok st' with
      | .intLit n =>
        if n ≥ 0 then
          let st'' := advance st'
          let loc : Location := { start := e.loc.start, stop := (spanTo e.loc st'').stop }
          parsePostfixRest { loc, kind := .unop (.proj n.toNat) e } st''
        else
          .error { loc := peekLoc st', kind := .negativeProjIndex }
      | .ident fname =>
        let st'' := advance st'
        let loc : Location := { start := e.loc.start, stop := (spanTo e.loc st'').stop }
        parsePostfixRest { loc, kind := .unop (.field fname) e } st''
      | _ => .ok (e, st)  -- lone dot, leave it
    | _ => .ok (e, st)

  -- atom: constants, variables, constructors, parens, records
  parseAtom : Parser Expr := fun st =>
    let p := peekLoc st
    match peekTok st with
    | .intLit n  => .ok (mkExpr p (advance st) (.const (.int n)), advance st)
    | .charLit c => .ok (mkExpr p (advance st) (.const (.char c)), advance st)
    | .kw_true   => .ok (mkExpr p (advance st) (.const (.bool true)), advance st)
    | .kw_false  => .ok (mkExpr p (advance st) (.const (.bool false)), advance st)
    | .ident name =>
      if name.front.isUpper then
        .ok (mkExpr p (advance st) (.ctor name), advance st)
      else
        .ok (mkExpr p (advance st) (.var name), advance st)
    | .lbrace => parseRecord st
    | .lparen =>
      let st' := advance st
      -- `()` = unit
      if peekTok st' == .rparen then
        .ok (mkExpr p (advance st') (.const .unit), advance st')
      else do
        let (e, st') ← parseExpr st'
        match peekTok st' with
        | .comma =>
          -- tuple
          let (rest, st') ← parseTupleRest st'
          let st' ← expect .rparen st'
          let loc : Location := { start := p.start, stop := (spanTo p st').stop }
          .ok ({ loc, kind := .tuple (e :: rest) }, st')
        | .colon =>
          -- type annotation `(e : T)`
          let (ty, st') ← parseType (advance st')
          let st' ← expect .rparen st'
          let loc : Location := { start := p.start, stop := (spanTo p st').stop }
          .ok ({ loc, kind := .annot e ty }, st')
        | .rparen =>
          .ok (e, advance st')
        | t =>
          .error { loc := peekLoc st', kind := .unexpectedToken "')' or ',' in expression" t }
    | t =>
      .error { loc := peekLoc st, kind := .unexpectedToken "expression" t }

  parseTupleRest : Parser (List Expr) := fun st =>
    match peekTok st with
    | .comma => do
      let (e, st) ← parseExpr (advance st)
      let (rest, st) ← parseTupleRest st
      .ok (e :: rest, st)
    | _ => .ok ([], st)

  -- `{ f1 = e1; f2 = e2 }` or `{ e with f1 = e1; ... }`
  -- Lookahead approach: peek to distinguish record literal from record update.
  -- A record literal starts with `ident =` (lowercase field name followed by `=`).
  -- Anything else is treated as an expression for record update.
  parseRecord : Parser Expr := fun st => do
    let p := peekLoc st
    let st ← expect .lbrace st
    if isRecordLiteral st then do
      let (fields, st) ← parseRecordFields st
      let st ← expect .rbrace st
      .ok (mkExpr p st (.record fields), st)
    else do
      let (e, st) ← parseExpr st
      let st ← expect .kw_with st
      let (fields, st) ← parseRecordFields st
      let st ← expect .rbrace st
      .ok (mkExpr p st (.recordUpdate e fields), st)

  isRecordLiteral (st : ParserState) : Bool :=
    match peekTok st with
    | .ident name =>
      if !name.front.isUpper && name.front != '\'' then
        peekTok (advance st) == .eq
      else false
    | _ => false

  parseRecordFields : Parser (List (FieldName × Expr)) := fun st => do
    let (name, st) ← expectIdent st
    let st ← expect .eq st
    let (e, st) ← parseExpr.parseAssign st
    match peekTok st with
    | .semi =>
      let st' := advance st
      match peekTok st' with
      | .rbrace => .ok ([(name, e)], st')  -- trailing semicolon
      | _ => do
        let (rest, st') ← parseRecordFields st'
        .ok ((name, e) :: rest, st')
    | _ => .ok ([(name, e)], st)

  -- `let [rec] pat pat ... [: T] = e in body`
  parseLet : Parser Expr := fun st => do
    let p := peekLoc st
    let st ← expect .kw_let st
    let isRec := peekTok st == .kw_rec
    let st := if isRec then advance st else st
    let (first, st) ← parsePatternBinder st
    let (rest, st) ← parseFunArgs st
    let (_retTy, st) ← parseOptRetTy st
    let st ← expect .eq st
    let (bound, st) ← parseExpr st
    let st ← expect .kw_in st
    let (body, st) ← parseExpr st
    .ok (mkExpr p st (.letIn isRec (first :: rest) bound body), st)

  -- `fun pat pat ... [: T] -> body`
  parseFun : Parser Expr := fun st => do
    let p := peekLoc st
    let st ← expect .kw_fun st
    let (args, st) ← parseFunArgs st
    let (retTy, st) ← parseOptRetTy st
    let st ← expect .arrow st
    let (body, st) ← parseExpr st
    .ok (mkExpr p st (.fun_ args retTy body), st)

  -- `if c then t else e`
  -- Sub-expressions use parseExprNoSemi because `;` binds less tightly
  -- than if/then/else in OCaml.
  parseIf : Parser Expr := fun st => do
    let p := peekLoc st
    let st ← expect .kw_if st
    let (cond, st) ← parseExprNoSemi st
    let st ← expect .kw_then st
    let (thn, st) ← parseExprNoSemi st
    let st ← expect .kw_else st
    let (els, st) ← parseExprNoSemi st
    .ok (mkExpr p st (.ite cond thn els), st)

  -- `match e with | P -> e | ...`
  parseMatch : Parser Expr := fun st => do
    let p := peekLoc st
    let st ← expect .kw_match st
    let (scrut, st) ← parseExpr st
    let st ← expect .kw_with st
    let (arms, st) ← parseMatchArms st
    .ok (mkExpr p st (.match_ scrut arms), st)

  parseMatchArms : Parser (List MatchArm) := fun st =>
    match peekTok st with
    | .pipe => do
      let st' := advance st
      let (pat, st') ← parsePattern st'
      let st' ← expect .arrow st'
      let (body, st') ← parseExpr st'
      let (rest, st') ← parseMatchArms st'
      .ok ({ pat, body } :: rest, st')
    | _ => .ok ([], st)

-- ---------------------------------------------------------------------------
-- Declaration parsing

/-- Parse a single top-level declaration. -/
partial def parseDecl : Parser Decl := fun st =>
  let p := peekLoc st
  match peekTok st with
  | .kw_type => parseTypeDecl p st
  | .kw_let  => parseValDecl p st
  | t =>
    .error { loc := peekLoc st, kind := .unexpectedToken "declaration (let or type)" t }
where
  parseTypeDecl (p : Location) : Parser Decl := fun st => do
    let st ← expect .kw_type st
    -- optional type parameters: `'a`, `('a, 'b)`, etc.
    let (params, st) ← parseTypeParams st
    let (name, st) ← expectIdent st
    let st ← expect .eq st
    -- try to figure out if this is a variant or record
    let (body, st) ← parseTypeDeclBody st
    let decl : TypeDecl := { params, name, body }
    let attrs := #[]
    .ok ({ loc := spanTo p st, kind := .type_ decl, attrs := attrs.toList }, st)

  parseTypeParams : Parser (List TypeVariable) := fun st =>
    match peekTok st with
    | .ident name =>
      -- type variable: starts with `'`
      if name.front == '\'' then
        let varName := name.toRawSubstring.drop 1 |>.toString
        .ok ([varName], advance st)
      else .ok ([], st)
    | .lparen =>
      let st' := advance st
      -- check if next is a type variable
      match peekTok st' with
      | .ident name =>
        if name.front == '\'' then do
          let (params, st') ← parseTypeParamList st'
          let st' ← expect .rparen st'
          .ok (params, st')
        else .ok ([], st)  -- not type params, leave paren
      | _ => .ok ([], st)  -- not type params, leave paren
    | _ => .ok ([], st)

  parseTypeParamList : Parser (List TypeVariable) := fun st =>
    match peekTok st with
    | .ident name =>
      if name.front == '\'' then
        let varName := name.toRawSubstring.drop 1 |>.toString
        let st' := advance st
        match peekTok st' with
        | .comma => do
          let (rest, st') ← parseTypeParamList (advance st')
          .ok (varName :: rest, st')
        | _ => .ok ([varName], st')
      else .ok ([], st)
    | _ => .ok ([], st)

  parseTypeDeclBody : Parser TypeDeclBody := fun st =>
    match peekTok st with
    | .lbrace => parseRecordBody st
    | _ => parseVariantBody st

  parseRecordBody : Parser TypeDeclBody := fun st => do
    let st ← expect .lbrace st
    let (fields, st) ← parseRecordBodyFields st
    let st ← expect .rbrace st
    .ok (.record fields, st)

  parseRecordBodyFields : Parser (List (FieldName × Typ)) := fun st => do
    let (name, st) ← expectIdent st
    let st ← expect .colon st
    let (ty, st) ← parseType st
    match peekTok st with
    | .semi =>
      let st' := advance st
      match peekTok st' with
      | .rbrace => .ok ([(name, ty)], st')  -- trailing semicolon
      | _ => do
        let (rest, st') ← parseRecordBodyFields st'
        .ok ((name, ty) :: rest, st')
    | _ => .ok ([(name, ty)], st)

  parseVariantBody : Parser TypeDeclBody := fun st => do
    -- optional leading `|`
    let st := if peekTok st == .pipe then advance st else st
    let (ctors, st) ← parseCtors st
    .ok (.variant ctors, st)

  parseCtors : Parser (List (Constructor × Option Typ)) := fun st => do
    let (name, st) ← expectConstructor st
    let (payload, st) ← parseCtorPayload st
    match peekTok st with
    | .pipe => do
      let (rest, st) ← parseCtors (advance st)
      .ok ((name, payload) :: rest, st)
    | _ => .ok ([(name, payload)], st)

  parseCtorPayload : Parser (Option Typ) := fun st =>
    match peekTok st with
    | .kw_of => do
      let (ty, st) ← parseType (advance st)
      .ok (some ty, st)
    | _ => .ok (none, st)

  parseValDecl (p : Location) : Parser Decl := fun st => do
    let st ← expect .kw_let st
    let isRec := peekTok st == .kw_rec
    let st := if isRec then advance st else st
    let (first, st) ← parsePatternBinder st
    let (rest, st) ← parseFunArgs st
    let (retTy, st) ← parseOptRetTy st
    let st ← expect .eq st
    let (body, st) ← parseExpr st
    -- optional `[@@name expr]` attribute(s)
    let (attrs, st) ← parseAttrs st
    .ok ({ loc := spanTo p st, kind := .val_ isRec (first :: rest) retTy body, attrs }, st)

  -- `[@@name expr]` repeated
  parseAttrs : Parser (List Attribute) := fun st =>
    match peekTok st with
    | .lbracket =>
      match (advance st |> peekTok) with
      | .atat => do
        let st' := advance (advance st)  -- skip `[` and `@@`
        let (name, st') ← expectIdent st'
        let (payload, st') ← parseExpr st'
        let st' ← expect .rbracket st'
        let (rest, st') ← parseAttrs st'
        .ok ({ name, payload } :: rest, st')
      | _ => .ok ([], st)
    | _ => .ok ([], st)

-- ---------------------------------------------------------------------------
-- Top-level program parsing

/-- Parse a sequence of top-level declarations. -/
partial def parseProgram : Parser Program := fun st =>
  match peekTok st with
  | .eof => .ok ([], st)
  | .semisemi => parseProgram (advance st)
  | .kw_let | .kw_type => do
    let (decl, st) ← parseDecl st
    -- skip optional `;;`
    let st := if peekTok st == .semisemi then advance st else st
    let (rest, st) ← parseProgram st
    .ok (decl :: rest, st)
  | t =>
    .error { loc := peekLoc st, kind := .unexpectedToken "declaration" t }

/-- Lex and parse `source` (file named `file`). -/
def parseFile (file : String) (source : String) : Except FrontendError Program := do
  let tokens ← (tokenize file source).mapError .lexError
  let st : ParserState := { file, tokens, pos := 0 }
  let (prog, st) ← (parseProgram st).mapError .parseError
  if peekTok st != .eof then
    .error (.parseError { loc := peekLoc st, kind := .unexpectedToken "end of file" (peekTok st) })
  else
    .ok prog

end Frontend
