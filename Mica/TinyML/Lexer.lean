namespace TinyML

inductive Token where
  | intLit (n : Int)
  | ident (name : String)
  | plus
  | minus
  | star
  | slash
  | lparen
  | rparen
  | eq
  | lt | le | gt | ge   -- < <= > >=
  | ampamp              -- &&
  | pipepipe            -- ||
  | dot                 -- .
  | colon               -- :
  | colonEq             -- :=
  | bang                -- !
  | comma
  | arrow               -- ->
  | at                  -- @
  | atat                -- @@
  | pipe_gt             -- |>
  | semi                -- ;
  | semisemi            -- ;;
  | kw_assert
  | kw_true | kw_false
  | kw_not | kw_fst | kw_snd | kw_ref
  | kw_inl | kw_inr
  | kw_spec
  | lbracket | rbracket  -- [ ]
  | underscore          -- _
  | kw_let
  | kw_rec
  | kw_in
  | kw_fun
  | kw_if
  | kw_then
  | kw_else
  | eof
  deriving Repr, BEq, Inhabited

def Token.toString : Token → String
  | .intLit n => s!"INT({n})"
  | .ident s => s!"IDENT({s})"
  | .plus => "PLUS"
  | .minus => "MINUS"
  | .star => "STAR"
  | .slash => "SLASH"
  | .lparen => "LPAREN"
  | .rparen => "RPAREN"
  | .eq => "EQ"
  | .lt => "LT" | .le => "LE" | .gt => "GT" | .ge => "GE"
  | .ampamp => "AMPAMP" | .pipepipe => "PIPEPIPE"
  | .dot => "DOT" | .colon => "COLON"
  | .colonEq => "COLONEQ" | .bang => "BANG" | .comma => "COMMA"
  | .arrow => "ARROW" | .at => "AT" | .atat => "ATAT" | .pipe_gt => "PIPE_GT"
  | .semi => "SEMI" | .semisemi => "SEMISEMI"
  | .kw_assert => "ASSERT" | .kw_true => "TRUE" | .kw_false => "FALSE"
  | .kw_not => "NOT" | .kw_fst => "FST" | .kw_snd => "SND" | .kw_ref => "REF"
  | .kw_inl => "INL" | .kw_inr => "INR"
  | .kw_spec => "SPEC"
  | .lbracket => "LBRACKET" | .rbracket => "RBRACKET"
  | .underscore => "UNDERSCORE"
  | .kw_let => "LET" | .kw_rec => "REC" | .kw_in => "IN"
  | .kw_fun => "FUN" | .kw_if => "IF" | .kw_then => "THEN" | .kw_else => "ELSE"
  | .eof => "EOF"

instance : ToString Token := ⟨Token.toString⟩

private def isDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

private def isAlpha (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'

private def isAlphaNum (c : Char) : Bool :=
  isAlpha c || isDigit c

private def keyword : String → Token
  | "let" => .kw_let
  | "rec" => .kw_rec
  | "in" => .kw_in
  | "fun" => .kw_fun
  | "if" => .kw_if
  | "then" => .kw_then
  | "else" => .kw_else
  | "assert" => .kw_assert
  | "true" => .kw_true | "false" => .kw_false
  | "not" => .kw_not | "fst" => .kw_fst | "snd" => .kw_snd
  | "ref" => .kw_ref
  | "inl" => .kw_inl | "inr" => .kw_inr
  | "spec" => .kw_spec
  | "_" => .underscore
  | s => .ident s

partial def tokenize (input : String) : Except String (List Token) :=
  lex input.toList []
where
  lex : List Char → List Token → Except String (List Token)
  | [], acc => .ok (acc.reverse ++ [.eof])
  | ' ' :: cs, acc | '\n' :: cs, acc | '\r' :: cs, acc | '\t' :: cs, acc =>
    lex cs acc
  | '+' :: cs, acc => lex cs (.plus :: acc)
  | '-' :: '>' :: cs, acc => lex cs (.arrow :: acc)
  | '-' :: cs, acc => lex cs (.minus :: acc)
  | '@' :: '@' :: cs, acc => lex cs (.atat :: acc)
  | '@' :: cs, acc => lex cs (.at :: acc)
  | '|' :: '>' :: cs, acc => lex cs (.pipe_gt :: acc)
  | '|' :: '|' :: cs, acc => lex cs (.pipepipe :: acc)
  | '&' :: '&' :: cs, acc => lex cs (.ampamp :: acc)
  | '<' :: '=' :: cs, acc => lex cs (.le :: acc)
  | '>' :: '=' :: cs, acc => lex cs (.ge :: acc)
  | '<' :: cs, acc => lex cs (.lt :: acc)
  | '>' :: cs, acc => lex cs (.gt :: acc)
  | ':' :: '=' :: cs, acc => lex cs (.colonEq :: acc)
  | ':' :: cs, acc => lex cs (.colon :: acc)
  | '.' :: cs, acc => lex cs (.dot :: acc)
  | '!' :: cs, acc => lex cs (.bang :: acc)
  | ',' :: cs, acc => lex cs (.comma :: acc)
  | '[' :: cs, acc => lex cs (.lbracket :: acc)
  | ']' :: cs, acc => lex cs (.rbracket :: acc)
  | '*' :: cs, acc => lex cs (.star :: acc)
  | '/' :: cs, acc => lex cs (.slash :: acc)
  | '(' :: cs, acc =>
    match cs with
    | '*' :: cs' => lexComment cs' acc 1
    | _ => lex cs (.lparen :: acc)
  | ')' :: cs, acc => lex cs (.rparen :: acc)
  | '=' :: cs, acc => lex cs (.eq :: acc)
  | ';' :: ';' :: cs, acc => lex cs (.semisemi :: acc)
  | ';' :: cs, acc => lex cs (.semi :: acc)
  | cs@(c :: _), acc =>
    if isDigit c then
      lexInt cs acc
    else if isAlpha c then
      lexIdent cs acc
    else
      .error s!"unexpected character: '{c}'"
  lexInt : List Char → List Token → Except String (List Token)
  | cs, acc =>
    let digits := cs.takeWhile isDigit
    let rest := cs.dropWhile isDigit
    match (String.ofList digits).toInt? with
    | some n => lex rest (.intLit n :: acc)
    | none => .error "invalid integer literal"
  lexIdent : List Char → List Token → Except String (List Token)
  | cs, acc =>
    let chars := cs.takeWhile isAlphaNum
    let rest := cs.dropWhile isAlphaNum
    lex rest (keyword (String.ofList chars) :: acc)
  lexComment : List Char → List Token → Nat → Except String (List Token)
  | [], _, _ => .error "unterminated comment"
  | '*' :: ')' :: cs, acc, 1 => lex cs acc
  | '*' :: ')' :: cs, acc, n + 1 => lexComment cs acc n
  | '(' :: '*' :: cs, acc, n => lexComment cs acc (n + 1)
  | _ :: cs, acc, n => lexComment cs acc n

end TinyML
