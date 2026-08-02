-- SUMMARY: Pretty-printing of frontend syntax back into OCaml-like concrete syntax.
import Mica.Frontend.AST

/-!
This file renders frontend AST nodes back to OCaml-like concrete syntax with
precedence-aware formatting for expressions, types, and declarations. It is
used for user-facing output and debugging of frontend transformations.
-/

namespace Frontend

-- ---------------------------------------------------------------------------
-- Helpers

private def joinWith (sep : String) (parts : List String) : String :=
  sep.intercalate parts

private def parens (s : String) : String := "(" ++ s ++ ")"

private def parenIf (cond : Bool) (s : String) : String :=
  if cond then parens s else s

-- ---------------------------------------------------------------------------
-- Const printing

private def hexDigit (n : Nat) : Char :=
  match n with
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3'
  | 4 => '4' | 5 => '5' | 6 => '6' | 7 => '7'
  | 8 => '8' | 9 => '9' | 10 => 'A' | 11 => 'B'
  | 12 => 'C' | 13 => 'D' | 14 => 'E' | _ => 'F'

private def byteEsc (b : UInt8) : String :=
  let n := b.toNat
  if n == 10 then "\\n"
  else if n == 9 then "\\t"
  else if n == 13 then "\\r"
  else if n == 34 then "\\\""
  else if n == 92 then "\\\\"
  else if 32 ≤ n && n < 127 then String.singleton (Char.ofNat n)
  else "\\x" ++ String.ofList [hexDigit (n / 16), hexDigit (n % 16)]

partial def Const.print : Const → String
  | .int n   => toString n
  | .float f => toString f
  | .bool b  => if b then "true" else "false"
  | .string s => "\"" ++ joinWith "" (s.map byteEsc) ++ "\""
  | .unit    => "()"
  | .char c  =>
    let s := match c with
      | '\n' => "\\n" | '\t' => "\\t" | '\r' => "\\r"
      | '\'' => "\\'" | '\\' => "\\\\"
      | c    => c.toString
    s!"'{s}'"

-- ---------------------------------------------------------------------------
-- Operators

partial def UnOp.print : UnOp → String
  | .neg    => "-"
  | .deref  => "!"
  | .assert => "assert"
  | .proj n     => s!".{n}"
  | .field name => s!".{name}"

-- Does this prefix unop need a space before its argument? A symbolic one does
-- not in general, but it glues to a leading operator character into a single
-- longer operator (`!!`, `--`), so that case takes a space too.
private def UnOp.needsSpace (op : UnOp) (arg : String) : Bool :=
  match op with
  | .neg | .deref => !arg.isEmpty && isOperatorChar arg.front
  | _ => true
where
  isOperatorChar (c : Char) : Bool := "!$%&*+-./:<=>?@^|~".contains c

partial def BinOp.print : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "mod"
  | .fadd => "+." | .fsub => "-." | .fmul => "*." | .fdiv => "/."
  | .eq => "=" | .neq => "<>" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .and => "&&" | .or => "||"
  | .semi => ";" | .pipeRight => "|>" | .atAt => "@@" | .assign => ":="
  | .concat => "^" | .append => "@" | .cons => "::"

-- Precedence comes from `BinOp.level` / `BinOp.assoc` in `AST.lean`, the same
-- table the parser climbs. A copy here is what let printer and parser disagree.

-- ---------------------------------------------------------------------------
-- Type printing

-- ---------------------------------------------------------------------------
-- Pattern printing

mutual

partial def Typ.print (t : Typ) : String :=
  let base := match t.kind with
    | .var name => s!"'{name}"
    | .con path [] => path.toString
    | .con path [arg] => s!"{Typ.printAppArg arg} {path.toString}"
    | .con path args => s!"({joinWith ", " (args.map Typ.print)}) {path.toString}"
    | .arrow dom cod =>
      let domStr := match dom.kind with
        | .arrow _ _ => parens (Typ.print dom)
        | _ => Typ.print dom
      s!"{domStr} -> {Typ.print cod}"
    | .tuple components => joinWith " * " (components.map Typ.print)
  -- A type attribute binds to the preceding application, so a compound base
  -- has to be parenthesized to round-trip with the parser.
  let baseStr := if t.attrs.isEmpty then base else parenIf (Typ.needsParens t) base
  baseStr ++ joinWith "" (t.attrs.map Typ.printAttr)

/-- Type constructor arguments that are themselves applications need parens. -/
private partial def Typ.printAppArg (t : Typ) : String :=
  match t.kind with
  | .arrow _ _ => parens (Typ.print t)
  | .tuple (_ :: _ :: _) => parens (Typ.print t)
  | _ => Typ.print t

/-- A type in a position that a `->` would run past: a `fun`'s return
annotation, which the arrow of the `fun` itself ends, and a constructor payload.
A `*` needs no parentheses in either. -/
private partial def Typ.printNoArrow (t : Typ) : String :=
  match t.kind with
  | .arrow _ _ => parens (Typ.print t)
  | _ => Typ.print t

private partial def Typ.needsParens (t : Typ) : Bool :=
  match t.kind with
  | .arrow _ _ | .tuple (_ :: _ :: _) => true
  | _ => false

/-- Type attribute `[@name]` or `[@name payload]` (single `@`). -/
private partial def Typ.printAttr (attr : Attribute) : String :=
  match attr.payload with
  | none         => s!" [@{attr.name}]"
  | some payload => s!" [@{attr.name} {Expr.printPrec payload 0}]"

/-- A pattern at `outerPrec`, over the same three levels the parser uses:
`Prec.patCons` for `::`, `Prec.patApp` for a constructor payload, and above
that the atoms, which delimit themselves. -/
partial def Pattern.printPrec (p : Pattern) (outerPrec : Nat) : String :=
  match p.kind with
  | .wildcard => "_"
  | .binder (some name) none => name
  | .binder (some name) (some ty) => s!"({name} : {Typ.print ty})"
  | .binder none none => "_"
  | .binder none (some ty) => s!"(_ : {Typ.print ty})"
  | .const c => Const.print c
  | .nil => "[]"
  | .cons head tail =>
    -- `::` is right-associative, so a `::` on the left needs parens.
    parenIf (outerPrec > Prec.patCons)
      (Pattern.printPrec head (Prec.patCons + 1) ++ " :: " ++
       Pattern.printPrec tail Prec.patCons)
  | .ctor path none => path.toString
  | .ctor path (some pat) =>
    parenIf (outerPrec > Prec.patApp)
      (path.toString ++ " " ++ Pattern.printPrec pat (Prec.patApp + 1))
  | .tuple pats => parens (joinWith ", " (pats.map (Pattern.printPrec · Prec.patCons)))
  | .record fields =>
    "{ " ++ joinWith "; " (fields.map fun (name, pat) =>
      name ++ " = " ++ Pattern.printPrec pat Prec.patCons) ++ " }"

partial def Pattern.print (p : Pattern) : String := Pattern.printPrec p Prec.patCons

-- ---------------------------------------------------------------------------
-- Expression printing

private partial def Expr.isAtom (e : Expr) : Bool :=
  match e.kind with
  | .const _ | .var _ | .ctor _ | .tuple _ | .list _ | .record _ | .annot _ _ | .arrayGet _ _ => true
  | _ => false

private partial def Expr.isKeywordExpr (e : Expr) : Bool :=
  match e.kind with
  | .letIn _ _ _ _ _ | .fun_ _ _ _ | .ite _ _ _ | .match_ _ _ => true
  | _ => false

private partial def Expr.printPrec (e : Expr) (outerPrec : Nat) : String :=
  if !e.attrs.isEmpty then
    -- Expression attributes `e [@name payload]` attach at application precedence,
    -- so parenthesize any compound base to round-trip with the parser.
    let bare := Expr.printPrec { e with attrs := [] } 0
    let baseStr := parenIf (!Expr.isAtom e) bare
    baseStr ++ joinWith "" (e.attrs.map printAttr)
  else match e.kind with
  | .const c => Const.print c
  | .var path => path.toString
  | .ctor path => path.toString
  | .annot inner ty => s!"({Expr.printPrec inner 0} : {Typ.print ty})"
  | .tuple es => parens (joinWith ", " (es.map fun x => Expr.printPrec x 0))
  | .list es => "[" ++ joinWith "; " (es.map fun x => Expr.printPrec x 2) ++ "]"
  | .record fields => "{ " ++ fmtFields fields ++ " }"
  | .recordUpdate base fields =>
    "{ " ++ Expr.printPrec base 0 ++ " with " ++ fmtFields fields ++ " }"
  | .unop op inner => printUnop op inner outerPrec
  | .arrayGet arr idx => printArrayGet arr idx outerPrec
  | .arraySet arr idx val => printArraySet arr idx val outerPrec
  | .binop op lhs rhs => printBinop op lhs rhs outerPrec
  | .app fn args =>
    parenIf (outerPrec > Prec.app)
      (joinWith " " ((fn :: args).map (operand · Prec.access)))
  | .ite cond thn els =>
    "if " ++ Expr.printPrec cond 0 ++ " then " ++ Expr.printPrec thn 0 ++
    " else " ++ Expr.printPrec els 0
  | .letIn isRec binders retTy bound body =>
    let recStr := if isRec then "rec " else ""
    let retStr := match retTy with | none => "" | some ty => " : " ++ Typ.print ty
    "let " ++ recStr ++ joinWith " " (binders.map Pattern.print) ++ retStr ++
    " = " ++ Expr.printPrec bound 0 ++ " in\n" ++ Expr.printPrec body 0
  | .fun_ args retTy body =>
    let retStr := match retTy with | none => "" | some ty => " : " ++ Typ.printNoArrow ty
    "fun " ++ joinWith " " (args.map Pattern.print) ++ retStr ++
    " -> " ++ Expr.printPrec body 0
  | .match_ scrutinee arms =>
    let armsStr := arms.map fun arm =>
      "| " ++ Pattern.print arm.pat ++ " -> " ++ Expr.printPrec arm.body 0
    "match " ++ Expr.printPrec scrutinee 0 ++ " with\n" ++ joinWith "\n" armsStr
where
  -- Expression attribute `[@name]` or `[@name payload]` (single `@`).
  printAttr (attr : Attribute) : String :=
    match attr.payload with
    | none         => s!" [@{attr.name}]"
    | some payload => s!" [@{attr.name} {Expr.printPrec payload 0}]"
  -- A field value ends at the `;` or `}` that follows it, so a `fun`, `let`,
  -- `if` or `match` has to be parenthesized to parse back.
  fmtFields (fields : List (FieldName × Expr)) : String :=
    joinWith "; " (fields.map fun (f, v) =>
      f ++ " = " ++ parenIf (Expr.isKeywordExpr v) (Expr.printPrec v 0))
  -- The three unary levels: postfix access, prefix `!` above it, and prefix `-`
  -- and `assert` down at application level.
  printUnop (op : UnOp) (inner : Expr) (outerPrec : Nat) : String :=
    let prefixOp (p : Nat) (operandPrec : Nat) : String :=
      let arg := operand inner operandPrec
      let space := if UnOp.needsSpace op arg then " " else ""
      parenIf (outerPrec > p) (UnOp.print op ++ space ++ arg)
    match op with
    | .proj n =>
      parenIf (outerPrec > Prec.access) (operand inner Prec.access ++ s!".{n}")
    | .field name =>
      parenIf (outerPrec > Prec.access) (operand inner Prec.access ++ "." ++ name)
    | .deref  => prefixOp Prec.prefixOp Prec.prefixOp
    | .neg    => prefixOp Prec.app Prec.app
    | .assert => prefixOp Prec.app Prec.access
  -- A subexpression at level `prec`. Every compound form parenthesizes itself
  -- against `prec`; the one exception is a keyword expression, which extends as
  -- far right as it can and so needs parens wherever anything could follow it.
  operand (e : Expr) (prec : Nat) : String :=
    parenIf (Expr.isKeywordExpr e) (Expr.printPrec e prec)
  printArrayGet (arr idx : Expr) (outerPrec : Nat) : String :=
    parenIf (outerPrec > Prec.access)
      (operand arr Prec.access ++ ".(" ++ Expr.printPrec idx 0 ++ ")")
  printArraySet (arr idx val : Expr) (outerPrec : Nat) : String :=
    -- `<-` sits at `:=`'s level and is right-associative like it.
    let p := BinOp.level .assign
    parenIf (outerPrec > p)
      (printArrayGet arr idx Prec.access ++ " <- " ++ operand val p)

  printBinop (op : BinOp) (lhs rhs : Expr) (outerPrec : Nat) : String :=
    let p := BinOp.level op
    let (lhsPrec, rhsPrec) := BinOp.operandLevels op
    let sep := if op == .semi then ";\n" else s!" {BinOp.print op} "
    parenIf (outerPrec > p) (operand lhs lhsPrec ++ sep ++ operand rhs rhsPrec)

end

partial def Expr.print (e : Expr) : String := Expr.printPrec e 0

-- ---------------------------------------------------------------------------
-- Declaration printing

partial def Decl.print (d : Decl) : String :=
  let attrsStr := d.attrs.map fun attr =>
    match attr.payload with
    | none => "\n[@@" ++ toString attr.name ++ "]"
    | some payload => "\n[@@" ++ toString attr.name ++ " " ++ Expr.print payload ++ "]"
  let attrsSuffix := joinWith "" attrsStr
  match d.kind with
  | .open_ path => "open " ++ path.toString ++ attrsSuffix
  | .type_ td => printTypeDecl td ++ attrsSuffix
  | .val_ isRec binders retTy body =>
    let recStr := if isRec then "rec " else ""
    let retStr := match retTy with | none => "" | some ty => " : " ++ Typ.print ty
    "let " ++ recStr ++ joinWith " " (binders.map Pattern.print) ++
    retStr ++ " = " ++ Expr.print body ++ attrsSuffix
where
  printTypeDecl (td : TypeDecl) : String :=
    let paramsStr := match td.params with
      | [] => ""
      | [p] => s!"'{p} "
      | ps => parens (joinWith ", " (ps.map fun p => s!"'{p}")) ++ " "
    let bodyStr := match td.body with
      | .variant ctors =>
        joinWith "\n" (ctors.map fun (name, payload) =>
          match payload with
          | none => "| " ++ name
          -- `A of int -> int` is a syntax error in OCaml; `A of int * int` is
          -- not, and there means several arguments rather than one tuple.
          | some ty => "| " ++ name ++ " of " ++ Typ.printNoArrow ty)
      | .record fields =>
        "{ " ++ joinWith "; " (fields.map fun (name, ty) => name ++ " : " ++ Typ.print ty) ++ " }"
    "type " ++ paramsStr ++ td.name ++ " = " ++ bodyStr

-- ---------------------------------------------------------------------------
-- Program printing

partial def Program.print (prog : Program) : String :=
  joinWith "\n;;\n" (prog.map Decl.print)

end Frontend
