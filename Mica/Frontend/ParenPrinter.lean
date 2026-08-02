-- SUMMARY: Precedence-free printing of frontend syntax, parenthesizing every compound node.
import Mica.Frontend.AST
import Mica.Frontend.Printer

/-!
This file prints the frontend AST with explicit parentheses around every compound
node, never consulting a precedence table.

It exists for the differential parser tests. Those compare mica's reading of a
source file against OCaml's by re-printing the parsed program and handing both
texts to `ocamlc -stop-after parsing -dsource`, which re-parenthesizes from the
parse tree and so normalizes redundant parentheses away. For that comparison to
mean anything, the printer used must not consult `BinOp.prec`: if it did, a
precedence error in the parser and the matching error in `Printer.lean` would
cancel out and the test would pass. Parenthesizing unconditionally has no
precedence logic to get wrong, and it fails safe — a bug here makes `ocamlc` read
something different, so the test fails rather than silently passing.

The output is deliberately unreadable; `Printer.lean` remains the printer for
user-facing output.

Two constructs are outside what this can express faithfully, and the differential
corpus therefore avoids them:

* Constructor application prints in application form, which OCaml parses as a
  `Pexp_apply` of a `Pexp_construct` rather than a saturated `Pexp_construct`.
* Tuple projection `e.1` has no OCaml counterpart at all.
-/

namespace Frontend

private def wrap (s : String) : String := "(" ++ s ++ ")"

private def sepBy (sep : String) (parts : List String) : String :=
  sep.intercalate parts

/-- Constants print bare. Negative literals are wrapped because OCaml's lexer
folds a leading `-` into the literal, which would change where the node sits. -/
private def Const.printParen (c : Const) : String :=
  match c with
  | .int n => if n < 0 then wrap (toString n) else toString n
  | c      => Const.print c

mutual

/-- Print a type, parenthesizing every compound node. -/
partial def Typ.printParen (t : Typ) : String :=
  let base := match t.kind with
    | .var name        => s!"'{name}"
    | .con path []     => path.toString
    | .con path [arg]  => wrap (Typ.printParen arg ++ " " ++ path.toString)
    | .con path args   =>
      wrap ("(" ++ sepBy ", " (args.map Typ.printParen) ++ ") " ++ path.toString)
    | .arrow dom cod   => wrap (Typ.printParen dom ++ " -> " ++ Typ.printParen cod)
    | .tuple comps     => wrap (sepBy " * " (comps.map Typ.printParen))
  base ++ sepBy "" (t.attrs.map Attribute.printParen)

/-- Print a pattern, parenthesizing every compound node. -/
partial def Pattern.printParen (p : Pattern) : String :=
  match p.kind with
  | .wildcard                     => "_"
  | .binder none none             => "_"
  | .binder (some name) none      => name
  | .binder none (some ty)        => wrap ("_ : " ++ Typ.printParen ty)
  | .binder (some name) (some ty) => wrap (name ++ " : " ++ Typ.printParen ty)
  | .const c                      => Const.printParen c
  | .nil                          => "[]"
  | .cons head tail               =>
    wrap (Pattern.printParen head ++ " :: " ++ Pattern.printParen tail)
  | .ctor path none               => path.toString
  | .ctor path (some payload)     =>
    wrap (path.toString ++ " " ++ Pattern.printParen payload)
  | .tuple pats                   => wrap (sepBy ", " (pats.map Pattern.printParen))
  | .record fields                =>
    "{ " ++ sepBy "; " (fields.map fun (n, q) => n ++ " = " ++ Pattern.printParen q) ++ " }"

/-- An attribute `[@name]` or `[@name payload]`. -/
partial def Attribute.printParen (a : Attribute) : String :=
  match a.payload with
  | none         => s!" [@{a.name}]"
  | some payload => s!" [@{a.name} {Expr.printParen payload}]"

/-- Print an expression, parenthesizing every compound node.

A space always follows a prefix operator: OCaml's lexer builds longer prefix
symbols out of adjacent operator characters, so `!` immediately followed by `=`
would lex as `!=`. -/
partial def Expr.printParen (e : Expr) : String :=
  let base := match e.kind with
    | .const c    => Const.printParen c
    | .var path   => path.toString
    | .ctor path  => path.toString
    | .annot inner ty =>
      wrap (Expr.printParen inner ++ " : " ++ Typ.printParen ty)
    | .tuple es   => wrap (sepBy ", " (es.map Expr.printParen))
    | .list es    => "[" ++ sepBy "; " (es.map Expr.printParen) ++ "]"
    | .record fields => "{ " ++ Expr.printParenFields fields ++ " }"
    | .recordUpdate b fields =>
      wrap ("{ " ++ Expr.printParen b ++ " with " ++ Expr.printParenFields fields ++ " }")
    | .app fn args =>
      wrap (sepBy " " (Expr.printParen fn :: args.map Expr.printParen))
    | .arrayGet arr idx =>
      wrap (Expr.printParen arr ++ ".(" ++ Expr.printParen idx ++ ")")
    | .arraySet arr idx val =>
      wrap (Expr.printParen arr ++ ".(" ++ Expr.printParen idx ++ ") <- "
            ++ Expr.printParen val)
    | .unop op inner => Expr.printParenUnop op inner
    | .binop .semi lhs rhs =>
      wrap (Expr.printParen lhs ++ "; " ++ Expr.printParen rhs)
    | .binop op lhs rhs =>
      wrap (Expr.printParen lhs ++ " " ++ BinOp.print op ++ " " ++ Expr.printParen rhs)
    | .ite cond thn els =>
      wrap ("if " ++ Expr.printParen cond ++ " then " ++ Expr.printParen thn
            ++ " else " ++ Expr.printParen els)
    | .letIn isRec binders retTy bound body =>
      let recStr := if isRec then "rec " else ""
      wrap ("let " ++ recStr ++ sepBy " " (binders.map Pattern.printParen)
            ++ Expr.printParenRetTy retTy ++ " = " ++ Expr.printParen bound
            ++ " in " ++ Expr.printParen body)
    | .fun_ args retTy body =>
      wrap ("fun " ++ sepBy " " (args.map Pattern.printParen)
            ++ Expr.printParenRetTy retTy ++ " -> " ++ Expr.printParen body)
    | .match_ scrutinee arms =>
      let armsStr := arms.map fun arm =>
        "| " ++ Pattern.printParen arm.pat ++ " -> " ++ Expr.printParen arm.body
      wrap ("match " ++ Expr.printParen scrutinee ++ " with " ++ sepBy " " armsStr)
  base ++ sepBy "" (e.attrs.map Attribute.printParen)

private partial def Expr.printParenUnop (op : UnOp) (inner : Expr) : String :=
  match op with
  | .proj n     => wrap (Expr.printParen inner ++ s!".{n}")
  | .field name => wrap (Expr.printParen inner ++ "." ++ name)
  | .neg        => wrap ("- " ++ Expr.printParen inner)
  | .deref      => wrap ("! " ++ Expr.printParen inner)
  | .assert     => wrap ("assert " ++ Expr.printParen inner)

private partial def Expr.printParenFields (fields : List (FieldName × Expr)) : String :=
  sepBy "; " (fields.map fun (f, v) => f ++ " = " ++ Expr.printParen v)

private partial def Expr.printParenRetTy : Option Typ → String
  | none    => ""
  | some ty => " : " ++ Typ.printParen ty

end

/-- Print a declaration. The leading binder of a `let` stays unparenthesized:
OCaml's function-definition form requires a bare identifier there. -/
partial def Decl.printParen (d : Decl) : String :=
  let attrsSuffix := sepBy "" (d.attrs.map fun a =>
    match a.payload with
    | none         => " [@@" ++ toString a.name ++ "]"
    | some payload => " [@@" ++ toString a.name ++ " " ++ Expr.printParen payload ++ "]")
  match d.kind with
  | .open_ path => "open " ++ path.toString ++ attrsSuffix
  | .val_ isRec binders retTy body =>
    let recStr := if isRec then "rec " else ""
    "let " ++ recStr ++ sepBy " " (binders.map Pattern.printParen)
      ++ Expr.printParenRetTy retTy ++ " = " ++ Expr.printParen body ++ attrsSuffix
  | .type_ td =>
    let paramsStr := match td.params with
      | []  => ""
      | [p] => s!"'{p} "
      | ps  => "(" ++ sepBy ", " (ps.map fun p => s!"'{p}") ++ ") "
    let bodyStr := match td.body with
      | .variant ctors =>
        sepBy " " (ctors.map fun (name, payload) =>
          match payload with
          | none    => "| " ++ name
          | some ty => "| " ++ name ++ " of " ++ Typ.printParen ty)
      | .record fields =>
        "{ " ++ sepBy "; " (fields.map fun (n, ty) => n ++ " : " ++ Typ.printParen ty) ++ " }"
    "type " ++ paramsStr ++ td.name ++ " = " ++ bodyStr ++ attrsSuffix

/-- Print a program, one declaration per line. -/
partial def Program.printParen (prog : Program) : String :=
  sepBy "\n" (prog.map Decl.printParen)

end Frontend
