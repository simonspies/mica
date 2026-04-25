-- SUMMARY: Lexical analysis for the OCaml frontend, including tokens and lexer errors.
import Mica.Frontend.AST

/-!
This file tokenizes frontend source text into `Token`s with precise source
locations and frontend-specific lexer errors. It is the first stage in the
pipeline, turning raw text into parser input.
-/

namespace Frontend

-- ---------------------------------------------------------------------------
-- Lexer error types

inductive LexErrorKind where
  | unexpectedChar (c : Char)
  | unexpectedEof (context : String)  -- e.g. "after '", "in comment"
  | unterminatedComment
  | invalidIntLiteral (text : String)
  | invalidCharEscape (c : Char)
  | unterminatedCharLiteral
  deriving Repr

structure LexError where
  pos  : Position
  kind : LexErrorKind
  deriving Repr

def LexError.toString (e : LexError) : String :=
  let loc := s!"{e.pos.file}:{e.pos.line}:{e.pos.col}"
  match e.kind with
  | .unexpectedChar c => s!"{loc}: unexpected character '{c}'"
  | .unexpectedEof ctx => s!"{loc}: unexpected end of input {ctx}"
  | .unterminatedComment => s!"{loc}: unterminated comment"
  | .invalidIntLiteral t => s!"{loc}: invalid integer literal '{t}'"
  | .invalidCharEscape c => s!"{loc}: invalid character escape '\\{c}'"
  | .unterminatedCharLiteral => s!"{loc}: unterminated character literal"

instance : ToString LexError := ⟨LexError.toString⟩

-- ---------------------------------------------------------------------------
-- Token type

inductive Token where
  | intLit  (n : Int)
  | charLit (c : Char)
  | ident   (name : String)   -- identifier (lowercase, uppercase, or starting with ')
  -- keywords
  | kw_let | kw_rec | kw_in | kw_fun
  | kw_if | kw_then | kw_else
  | kw_match | kw_with
  | kw_type | kw_of
  | kw_assert
  | kw_true | kw_false
  | kw_mod | kw_and
  -- punctuation and operators
  | plus | minus | star | slash
  | eq | neq | lt | le | gt | ge   -- = <> < <= > >=
  | ampamp | pipepipe               -- && ||
  | pipeGt                          -- |>
  | atat | at                       -- @@ @
  | colonEq | colon                 -- := :
  | semi | semisemi                 -- ; ;;
  | arrow                           -- ->
  | dot | comma | bang              -- . , !
  | pipe | underscore               -- | _
  | lparen | rparen
  | lbracket | rbracket
  | lbrace | rbrace
  | eof
  deriving Repr, BEq, Inhabited

def Token.toString : Token → String
  | .intLit n  => s!"INT({n})"
  | .charLit c => s!"CHAR({c})"
  | .ident s   => s!"IDENT({s})"
  | .kw_let   => "let"   | .kw_rec  => "rec"   | .kw_in   => "in"
  | .kw_fun   => "fun"   | .kw_if   => "if"    | .kw_then => "then"
  | .kw_else  => "else"  | .kw_match => "match" | .kw_with => "with"
  | .kw_type  => "type"  | .kw_of   => "of"
  | .kw_assert => "assert"
  | .kw_true  => "true"  | .kw_false => "false"
  | .kw_mod   => "mod"   | .kw_and  => "and"
  | .plus     => "+"     | .minus   => "-"    | .star  => "*"  | .slash => "/"
  | .eq       => "="     | .neq     => "<>"   | .lt    => "<"
  | .le       => "<="    | .gt      => ">"    | .ge    => ">="
  | .ampamp   => "&&"    | .pipepipe => "||"
  | .pipeGt   => "|>"    | .atat    => "@@"   | .at    => "@"
  | .colonEq  => ":="    | .colon   => ":"
  | .semi     => ";"     | .semisemi => ";;"
  | .arrow    => "->"    | .dot     => "."    | .comma => ","  | .bang  => "!"
  | .pipe     => "|"     | .underscore => "_"
  | .lparen   => "("     | .rparen  => ")"
  | .lbracket => "["     | .rbracket => "]"
  | .lbrace   => "{"     | .rbrace  => "}"
  | .eof      => "EOF"

instance : ToString Token := ⟨Token.toString⟩

-- ---------------------------------------------------------------------------
-- Lexer state

private structure LexState where
  file   : String
  source : List Char
  line   : Nat   -- 1-indexed
  col    : Nat   -- 1-indexed

private def LexState.pos (st : LexState) : Position :=
  { file := st.file, line := st.line, col := st.col }

private def LexState.advance (st : LexState) (c : Char) : LexState :=
  if c == '\n' then { st with source := st.source.tail!, line := st.line + 1, col := 1 }
  else { st with source := st.source.tail!, col := st.col + 1 }

private def LexState.peek (st : LexState) : Option Char :=
  st.source.head?

private def LexState.peek2 (st : LexState) : Option Char :=
  match st.source with
  | _ :: c :: _ => some c
  | _ => none

-- ---------------------------------------------------------------------------
-- Helpers

private def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
private def isUpper (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'
private def isLower (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'
private def isAlpha (c : Char) : Bool := isUpper c || isLower c || c == '_'
-- Allow apostrophe as continuation character in identifiers (e.g., x', f'')
private def isAlphaNum (c : Char) : Bool := isAlpha c || isDigit c || c == '\''

private def keyword (s : String) : Token :=
  match s with
  | "let"    => .kw_let    | "rec"    => .kw_rec    | "in"     => .kw_in
  | "fun"    => .kw_fun    | "if"     => .kw_if     | "then"   => .kw_then
  | "else"   => .kw_else   | "match"  => .kw_match  | "with"   => .kw_with
  | "type"   => .kw_type   | "of"     => .kw_of
  | "assert" => .kw_assert
  | "true"   => .kw_true   | "false"  => .kw_false
  | "mod"    => .kw_mod    | "and"    => .kw_and
  | "_"      => .underscore
  | s        => .ident s

-- ---------------------------------------------------------------------------
-- Main lexer

/-- Tokenize `source` (a file named `file`).
    Returns a located token array ending with `eof`, or an error. -/
partial def tokenize (file : String) (source : String)
    : Except LexError (Array (Location × Token)) :=
  lex { file, source := source.toList, line := 1, col := 1 } #[]
where
  lex (st : LexState) (acc : Array (Location × Token))
      : Except LexError (Array (Location × Token)) :=
    match st.source with
    | [] =>
      let p := st.pos
      .ok (acc.push ({ start := p, stop := p }, .eof))
    | c :: _ =>
      -- skip whitespace
      if c == ' ' || c == '\n' || c == '\r' || c == '\t' then
        lex (st.advance c) acc
      -- comments: `(* ... *)`
      else if c == '(' then
        match st.peek2 with
        | some '*' =>
          let st1 := (st.advance '(').advance '*'
          lexComment st1 acc 1
        | _ =>
          let p := st.pos
          let st' := st.advance c
          lex st' (acc.push ({ start := p, stop := st'.pos }, .lparen))
      -- two-char operators first
      else
        let p := st.pos
        match c, st.peek2 with
        | '-', some '>' =>
          let st' := (st.advance '-').advance '>'
          lex st' (acc.push ({ start := p, stop := st'.pos }, .arrow))
        | '<', some '=' =>
          let st' := (st.advance '<').advance '='
          lex st' (acc.push ({ start := p, stop := st'.pos }, .le))
        | '<', some '>' =>
          let st' := (st.advance '<').advance '>'
          lex st' (acc.push ({ start := p, stop := st'.pos }, .neq))
        | '>', some '=' =>
          let st' := (st.advance '>').advance '='
          lex st' (acc.push ({ start := p, stop := st'.pos }, .ge))
        | '&', some '&' =>
          let st' := (st.advance '&').advance '&'
          lex st' (acc.push ({ start := p, stop := st'.pos }, .ampamp))
        | '|', some '|' =>
          let st' := (st.advance '|').advance '|'
          lex st' (acc.push ({ start := p, stop := st'.pos }, .pipepipe))
        | '|', some '>' =>
          let st' := (st.advance '|').advance '>'
          lex st' (acc.push ({ start := p, stop := st'.pos }, .pipeGt))
        | '@', some '@' =>
          let st' := (st.advance '@').advance '@'
          lex st' (acc.push ({ start := p, stop := st'.pos }, .atat))
        | ':', some '=' =>
          let st' := (st.advance ':').advance '='
          lex st' (acc.push ({ start := p, stop := st'.pos }, .colonEq))
        | ';', some ';' =>
          let st' := (st.advance ';').advance ';'
          lex st' (acc.push ({ start := p, stop := st'.pos }, .semisemi))
        -- apostrophe handling: 'c' char literal, 'a type var / identifier, x' continuation
        | '\'', _ =>
          lexApostrophe st acc
        | _, _ =>
          -- single-char tokens
          let single : Option Token :=
            match c with
            | '+' => some .plus     | '-' => some .minus   | '*' => some .star
            | '/' => some .slash    | '=' => some .eq      | '<' => some .lt
            | '>' => some .gt       | ':' => some .colon   | ';' => some .semi
            | '.' => some .dot      | ',' => some .comma   | '!' => some .bang
            | '|' => some .pipe     | '@' => some .at
            | ')' => some .rparen
            | '[' => some .lbracket | ']' => some .rbracket
            | '{' => some .lbrace   | '}' => some .rbrace
            | _ => none
          match single with
          | some tok =>
            let st' := st.advance c
            lex st' (acc.push ({ start := p, stop := st'.pos }, tok))
          | none =>
            -- integer literals
            if isDigit c then lexInt st acc
            -- identifiers / keywords
            else if isAlpha c then lexIdent st acc
            -- unrecognized
            else .error { pos := st.pos, kind := .unexpectedChar c }

  /-- Handle `'`: either a char literal `'c'` or `'\X'`, or an identifier starting with `'` (type var / primed name). -/
  lexApostrophe (st : LexState) (acc : Array (Location × Token))
      : Except LexError (Array (Location × Token)) :=
    let p := st.pos
    let st1 := st.advance '\''  -- consume the opening `'`
    match st1.source with
    | '\\' :: escChar :: '\'' :: _ =>
      let escapes : List (Char × Char) :=
        [('n', '\n'), ('t', '\t'), ('r', '\r'), ('\\', '\\'),
         ('\'', '\''), ('"', '"'), ('0', '\x00')]
      match escapes.find? (·.1 == escChar) with
      | some (_, ch) =>
        let st3 := ((st1.advance '\\').advance escChar).advance '\''
        lex st3 (acc.push ({ start := p, stop := st3.pos }, .charLit ch))
      | none => .error { pos := p, kind := .invalidCharEscape escChar }
    | ch :: '\'' :: _ =>
      -- single-char literal 'ch'
      let st2 := (st1.advance ch).advance '\''
      lex st2 (acc.push ({ start := p, stop := st2.pos }, .charLit ch))
    | [] =>
      .error { pos := p, kind := .unexpectedEof "after \"'\"" }
    | c2 :: _ =>
      -- identifier starting with `'`: type var `'a` or similar
      if isAlpha c2 then
        let (chars, st2) := collectWhile isAlphaNum st1
        let name := "'" ++ String.ofList chars
        lex st2 (acc.push ({ start := p, stop := st2.pos }, keyword name))
      else
        .error { pos := p, kind := .unexpectedChar '\'' }

  lexInt (st : LexState) (acc : Array (Location × Token))
      : Except LexError (Array (Location × Token)) :=
    let p := st.pos
    let (digits, st') := collectWhile isDigit st
    let text := String.ofList digits
    match text.toInt? with
    | some n => lex st' (acc.push ({ start := p, stop := st'.pos }, .intLit n))
    | none   => .error { pos := p, kind := .invalidIntLiteral text }

  lexIdent (st : LexState) (acc : Array (Location × Token))
      : Except LexError (Array (Location × Token)) :=
    let p := st.pos
    let (chars, st') := collectWhile isAlphaNum st
    let name := String.ofList chars
    let tok := keyword name
    lex st' (acc.push ({ start := p, stop := st'.pos }, tok))

  lexComment (st : LexState) (acc : Array (Location × Token)) (depth : Nat)
      : Except LexError (Array (Location × Token)) :=
    match st.source with
    | [] => .error { pos := st.pos, kind := .unterminatedComment }
    | '*' :: ')' :: _ =>
      let st' := (st.advance '*').advance ')'
      if depth == 1 then lex st' acc
      else lexComment st' acc (depth - 1)
    | '(' :: '*' :: _ =>
      let st' := (st.advance '(').advance '*'
      lexComment st' acc (depth + 1)
    | c :: _ => lexComment (st.advance c) acc depth

  /-- Consume characters while predicate holds; return collected chars and updated state. -/
  collectWhile (pred : Char → Bool) (st : LexState) : List Char × LexState :=
    match st.source with
    | c :: _ => if pred c then
        let (rest, st') := collectWhile pred (st.advance c)
        (c :: rest, st')
      else ([], st)
    | [] => ([], st)

end Frontend
