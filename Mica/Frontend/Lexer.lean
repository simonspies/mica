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
  | invalidFloatLiteral (text : String)
  | invalidCharEscape (c : Char)
  | unterminatedCharLiteral
  | invalidStringEscape (text : String)
  | unterminatedStringLiteral
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
  | .invalidFloatLiteral t => s!"{loc}: invalid float literal '{t}'"
  | .invalidCharEscape c => s!"{loc}: invalid character escape '\\{c}'"
  | .unterminatedCharLiteral => s!"{loc}: unterminated character literal"
  | .invalidStringEscape text => s!"{loc}: invalid string escape '\\{text}'"
  | .unterminatedStringLiteral => s!"{loc}: unterminated string literal"

instance : ToString LexError := ⟨LexError.toString⟩

-- ---------------------------------------------------------------------------
-- Token type

inductive Token where
  | intLit  (n : Int)
  | floatLit (value : Float)
  | charLit (c : Char)
  | stringLit (s : List UInt8)
  | ident   (name : String)   -- identifier (lowercase, uppercase, or starting with ')
  -- keywords
  | kw_let | kw_rec | kw_in | kw_fun
  | kw_if | kw_then | kw_else
  | kw_match | kw_with
  | kw_open
  | kw_type | kw_of
  | kw_assert
  | kw_true | kw_false
  | kw_mod | kw_and
  -- punctuation and operators
  | plus | minus | star | slash
  | plusDot | minusDot | starDot | slashDot
  | caret
  | eq | neq | lt | le | gt | ge   -- = <> < <= > >=
  | ampamp | pipepipe               -- && ||
  | pipeGt                          -- |>
  | atat | at                       -- @@ @
  | colonEq | coloncolon | colon    -- := :: :
  | semi | semisemi                 -- ; ;;
  | arrow                           -- ->
  | leftArrow                       -- <-
  | dot | comma | bang              -- . , !
  | pipe | underscore               -- | _
  | lparen | rparen
  | lbracket | rbracket
  | lbrace | rbrace
  | eof
  deriving Repr, BEq, Inhabited

def Token.toString : Token → String
  | .intLit n  => s!"INT({n})"
  | .floatLit f => s!"FLOAT({f})"
  | .charLit c => s!"CHAR({c})"
  | .stringLit _ => "STRING"
  | .ident s   => s!"IDENT({s})"
  | .kw_let   => "let"   | .kw_rec  => "rec"   | .kw_in   => "in"
  | .kw_fun   => "fun"   | .kw_if   => "if"    | .kw_then => "then"
  | .kw_else  => "else"  | .kw_match => "match" | .kw_with => "with"
  | .kw_open  => "open"
  | .kw_type  => "type"  | .kw_of   => "of"
  | .kw_assert => "assert"
  | .kw_true  => "true"  | .kw_false => "false"
  | .kw_mod   => "mod"   | .kw_and  => "and"
  | .plus     => "+"     | .minus   => "-"    | .star  => "*"  | .slash => "/"
  | .plusDot  => "+."    | .minusDot => "-."   | .starDot => "*." | .slashDot => "/."
  | .caret    => "^"
  | .eq       => "="     | .neq     => "<>"   | .lt    => "<"
  | .le       => "<="    | .gt      => ">"    | .ge    => ">="
  | .ampamp   => "&&"    | .pipepipe => "||"
  | .pipeGt   => "|>"    | .atat    => "@@"   | .at    => "@"
  | .colonEq  => ":="    | .coloncolon => "::" | .colon => ":"
  | .semi     => ";"     | .semisemi => ";;"
  | .arrow    => "->"    | .leftArrow => "<-"
  | .dot      => "."     | .comma   => ","   | .bang  => "!"
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
private def isHexDigit (c : Char) : Bool :=
  isDigit c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

private def hexVal (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then 10 + c.toNat - 'a'.toNat
  else if 'A' ≤ c && c ≤ 'F' then 10 + c.toNat - 'A'.toNat
  else 0

private def decVal (c : Char) : Nat := c.toNat - '0'.toNat

private def isOctDigit (c : Char) : Bool := '0' ≤ c && c ≤ '7'
private def octVal (c : Char) : Nat := c.toNat - '0'.toNat

/-- UTF-8 encoding of a Unicode scalar value, as a byte list. -/
private def utf8Bytes (n : Nat) : List UInt8 := (Char.ofNat n).toString.toUTF8.data.toList

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
  | "open"   => .kw_open
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
        | '<', some '-' =>
          let st' := (st.advance '<').advance '-'
          lex st' (acc.push ({ start := p, stop := st'.pos }, .leftArrow))
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
        | ':', some ':' =>
          let st' := (st.advance ':').advance ':'
          lex st' (acc.push ({ start := p, stop := st'.pos }, .coloncolon))
        | ';', some ';' =>
          let st' := (st.advance ';').advance ';'
          lex st' (acc.push ({ start := p, stop := st'.pos }, .semisemi))
        | '+', some '.' =>
          let st' := (st.advance '+').advance '.'
          lex st' (acc.push ({ start := p, stop := st'.pos }, .plusDot))
        | '-', some '.' =>
          let st' := (st.advance '-').advance '.'
          lex st' (acc.push ({ start := p, stop := st'.pos }, .minusDot))
        | '*', some '.' =>
          let st' := (st.advance '*').advance '.'
          lex st' (acc.push ({ start := p, stop := st'.pos }, .starDot))
        | '/', some '.' =>
          let st' := (st.advance '/').advance '.'
          lex st' (acc.push ({ start := p, stop := st'.pos }, .slashDot))
        -- apostrophe handling: 'c' char literal, 'a type var / identifier, x' continuation
        | '\'', _ =>
          lexApostrophe st acc
        | '"', _ =>
          lexString st acc
        | _, _ =>
          -- single-char tokens
          let single : Option Token :=
            match c with
            | '+' => some .plus     | '-' => some .minus   | '*' => some .star
            | '/' => some .slash    | '=' => some .eq      | '<' => some .lt
            | '^' => some .caret
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
            -- integer and float literals
            if isDigit c then lexNumber st acc
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

  lexNumber (st : LexState) (acc : Array (Location × Token))
      : Except LexError (Array (Location × Token)) :=
    let p := st.pos
    let (digits, stDigits) := collectWhile isDigit st
    let (fracDigits, stFrac, sawFrac) :=
      match stDigits.source with
      | '.' :: _ =>
        -- A `.` after the integer part starts a float, even with no fractional
        -- digits: OCaml allows a trailing dot (`1.`, `1.e2`). After a numeric
        -- mantissa a `.` only ever introduces a float in this grammar.
        let (frac, stAfterFrac) := collectWhile isDigit (stDigits.advance '.')
        (frac, stAfterFrac, true)
      | _ => ([], stDigits, false)
    let parseExp (st0 : LexState) : Except LexError (Option (Bool × Nat) × LexState) :=
      match st0.source with
      | 'e' :: _ | 'E' :: _ =>
        let st1 := st0.advance st0.source.head!
        let (neg, st2) :=
          match st1.source with
          | '+' :: _ => (false, st1.advance '+')
          | '-' :: _ => (true, st1.advance '-')
          | _ => (false, st1)
        let (expDigits, st3) := collectWhile isDigit st2
        if expDigits.isEmpty then
          .error { pos := st0.pos, kind := .invalidFloatLiteral (String.ofList (digits ++ fracDigits)) }
        else
          match (String.ofList expDigits).toNat? with
          | some e => .ok (some (neg, e), st3)
          | none => .error { pos := st0.pos, kind := .invalidFloatLiteral (String.ofList expDigits) }
      | _ => .ok (none, st0)
    match parseExp stFrac with
    | .error e => .error e
    | .ok (expOpt, st') =>
      if sawFrac || expOpt.isSome then
        let mantText := String.ofList (digits ++ fracDigits)
        match mantText.toNat? with
        | none => .error { pos := p, kind := .invalidFloatLiteral mantText }
        | some mant =>
          let signedExp : Int :=
            match expOpt with
            | none => 0
            | some (neg, e) => if neg then -Int.ofNat e else Int.ofNat e
          let shift := signedExp - Int.ofNat fracDigits.length
          let f :=
            if shift < 0 then Float.ofScientific mant true ((-shift).toNat)
            else Float.ofScientific mant false shift.toNat
          lex st' (acc.push ({ start := p, stop := st'.pos }, .floatLit f))
      else
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

  lexString (st : LexState) (acc : Array (Location × Token))
      : Except LexError (Array (Location × Token)) :=
    let p := st.pos
    let st1 := st.advance '"'
    match stringBytes st1 [] with
    | .ok (bytes, st') =>
      let st'' := st'.advance '"'
      lex st'' (acc.push ({ start := p, stop := st''.pos }, .stringLit bytes))
    | .error e => .error e

  stringBytes (st : LexState) (acc : List UInt8)
      : Except LexError (List UInt8 × LexState) :=
    match st.source with
    | [] => .error { pos := st.pos, kind := .unterminatedStringLiteral }
    | '"' :: _ => .ok (acc.reverse, st)
    | '\n' :: _ => .error { pos := st.pos, kind := .unterminatedStringLiteral }
    | '\\' :: esc :: _ =>
      -- `st1` is positioned at the escape character (just past the backslash).
      let st1 := st.advance '\\'
      let simple : Option UInt8 :=
        match esc with
        | 'n' => some 10  | 't' => some 9   | 'r' => some 13  | 'b' => some 8
        | '\\' => some 92 | '"' => some 34  | '\'' => some 39 | ' ' => some 32
        | _ => none
      match simple with
      | some b => stringBytes (st1.advance esc) (b :: acc)
      | none =>
        match esc with
        -- Line continuation: `\` newline spaces-or-tabs is ignored.
        | '\n' => stringLineCont (st1.advance '\n') acc
        | '\r' =>
          let st2 := st1.advance '\r'
          match st2.source with
          | '\n' :: _ => stringLineCont (st2.advance '\n') acc
          | _ => stringLineCont st2 acc
        -- `\xHH`: two hexadecimal digits.
        | 'x' =>
          let st2 := st1.advance 'x'
          match st2.source with
          | h1 :: h2 :: _ =>
            if isHexDigit h1 && isHexDigit h2 then
              stringBytes ((st2.advance h1).advance h2) (UInt8.ofNat (hexVal h1 * 16 + hexVal h2) :: acc)
            else .error { pos := st.pos, kind := .invalidStringEscape "x" }
          | _ => .error { pos := st.pos, kind := .invalidStringEscape "x" }
        -- `\oOOO`: three octal digits.
        | 'o' =>
          let st2 := st1.advance 'o'
          match st2.source with
          | a :: b :: c :: _ =>
            if isOctDigit a && isOctDigit b && isOctDigit c then
              let n := octVal a * 64 + octVal b * 8 + octVal c
              if n ≤ 255 then
                stringBytes (((st2.advance a).advance b).advance c) (UInt8.ofNat n :: acc)
              else .error { pos := st.pos, kind := .invalidStringEscape (String.ofList ['o', a, b, c]) }
            else .error { pos := st.pos, kind := .invalidStringEscape "o" }
          | _ => .error { pos := st.pos, kind := .invalidStringEscape "o" }
        -- `\u{X…}`: Unicode scalar value, substituted by its UTF-8 encoding.
        | 'u' =>
          let st2 := st1.advance 'u'
          match st2.source with
          | '{' :: _ =>
            let (hexes, st3) := collectWhile isHexDigit (st2.advance '{')
            match st3.source with
            | '}' :: _ =>
              if hexes.isEmpty then .error { pos := st.pos, kind := .invalidStringEscape "u" }
              else
                let n := hexes.foldl (fun a c => a * 16 + hexVal c) 0
                if n ≤ 0xD7FF || (0xE000 ≤ n && n ≤ 0x10FFFF) then
                  stringBytes (st3.advance '}') ((utf8Bytes n).reverse ++ acc)
                else .error { pos := st.pos, kind := .invalidStringEscape "u" }
            | _ => .error { pos := st.pos, kind := .invalidStringEscape "u" }
          | _ => .error { pos := st.pos, kind := .invalidStringEscape "u" }
        -- `\DDD`: three decimal digits.
        | d1 =>
          if isDigit d1 then
            match st1.source with
            | a :: b :: c :: _ =>
              if isDigit a && isDigit b && isDigit c then
                let n := decVal a * 100 + decVal b * 10 + decVal c
                if n ≤ 255 then
                  stringBytes (((st1.advance a).advance b).advance c) (UInt8.ofNat n :: acc)
                else .error { pos := st.pos, kind := .invalidStringEscape (String.ofList [a, b, c]) }
              else .error { pos := st.pos, kind := .invalidStringEscape (String.singleton d1) }
            | _ => .error { pos := st.pos, kind := .invalidStringEscape (String.singleton d1) }
          else .error { pos := st.pos, kind := .invalidStringEscape (String.singleton esc) }
    | c :: _ =>
      stringBytes (st.advance c) (c.toString.toUTF8.data.toList.reverse ++ acc)

  /-- Skip the spaces and tabs following an escaped newline, then resume. -/
  stringLineCont (st : LexState) (acc : List UInt8)
      : Except LexError (List UInt8 × LexState) :=
    match st.source with
    | c :: _ =>
      if c == ' ' || c == '\t' then stringLineCont (st.advance c) acc
      else stringBytes st acc
    | [] => stringBytes st acc

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
