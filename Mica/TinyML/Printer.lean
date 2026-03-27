import Mica.TinyML.Expr

namespace TinyML

def BinOp.toString : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "mod"
  | .eq => "=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .and => "&&" | .or => "||"

def UnOp.toString : UnOp → String
  | .neg => "-" | .not => "not"
  | .proj n => s!".{n}"

def Binder.print : Binder → String
  | .none => "_"
  | .named name _ => name

private def argsStr (args : List Binder) : String :=
  " ".intercalate (args.map Binder.print)

-- Collect fix args from the current node, plus any continuation if the body
-- is another fix with the same named self binder.
private partial def collectFixArgs (f : String) (args : List Binder) (body : Expr)
    : List Binder × Expr :=
  match body with
  | .fix (.named f' _) args' _ inner =>
    if f == f' then
      let (moreArgs, finalBody) := collectFixArgs f args' inner
      (args ++ moreArgs, finalBody)
    else (args, body)
  | _ => (args, body)

-- Collect anonymous fix args from the current node, plus any continuation if
-- the body is another anonymous fix.
private partial def collectAnonArgs (args : List Binder) (body : Expr)
    : List Binder × Expr :=
  match body with
  | .fix .none args' _ inner =>
    let (moreArgs, finalBody) := collectAnonArgs args' inner
    (args ++ moreArgs, finalBody)
  | _ => (args, body)

mutual

partial def printExpr : Expr → String
  | .letIn .none bound body => s!"{printOr bound};\n{printExpr body}"
  | .letIn name bound body => printLetIn name bound body
  | .ifThenElse cond thn els =>
    s!"if {printExpr cond} then {printExpr thn} else {printExpr els}"
  | .match_ scrut branches =>
    let arms := (List.range branches.length).zip branches |>.map fun ⟨i, b⟩ => s!"| {i} -> {printExpr b}"
    s!"match {printExpr scrut} with {" ".intercalate arms}"
  | .store l r => s!"{printOr l} := {printOr r}"
  | e => printOr e

-- Print a let binding, recognising recursive and eta-contracted forms.
partial def printLetIn (name : Binder) (bound body : Expr) : String :=
  match bound with
  | .fix (.named f _) args _ inner =>
    let (allArgs, innerBody) := collectFixArgs f args inner
    let nameMatchesF := match name with | .named n _ => n == f | .none => false
    if nameMatchesF then
      s!"let rec {f} {argsStr allArgs} = {printExpr innerBody} in\n{printExpr body}"
    else
      s!"let {name.print} = (let rec {f} {argsStr allArgs} = {printExpr innerBody} in {f}) in\n{printExpr body}"
  | .fix .none args _ inner =>
    let (allArgs, innerBody) := collectAnonArgs args inner
    s!"let {name.print} {argsStr allArgs} = {printExpr innerBody} in\n{printExpr body}"
  | _ =>
    s!"let {name.print} = {printExpr bound} in\n{printExpr body}"

partial def printOr : Expr → String
  | .binop .or lhs rhs => s!"{printAnd lhs} || {printOr rhs}"
  | e => printAnd e

partial def printAnd : Expr → String
  | .binop .and lhs rhs => s!"{printCmp lhs} && {printAnd rhs}"
  | e => printCmp e

partial def printCmp : Expr → String
  | .binop .eq  lhs rhs => s!"{printAdd lhs} = {printAdd rhs}"
  | .binop .lt  lhs rhs => s!"{printAdd lhs} < {printAdd rhs}"
  | .binop .le  lhs rhs => s!"{printAdd lhs} <= {printAdd rhs}"
  | .binop .gt  lhs rhs => s!"{printAdd lhs} > {printAdd rhs}"
  | .binop .ge  lhs rhs => s!"{printAdd lhs} >= {printAdd rhs}"
  | e => printAdd e

partial def printAdd : Expr → String
  | .binop .add lhs rhs => s!"{printAdd lhs} + {printMul rhs}"
  | .binop .sub lhs rhs => s!"{printAdd lhs} - {printMul rhs}"
  | e => printMul e

partial def printMul : Expr → String
  | .binop .mul lhs rhs => s!"{printMul lhs} * {printApp rhs}"
  | .binop .div lhs rhs => s!"{printMul lhs} / {printApp rhs}"
  | .binop .mod lhs rhs => s!"{printMul lhs} mod {printApp rhs}"
  | e => printApp e

-- Function-application-level unary operators.
partial def printApp : Expr → String
  | .app fn args       => s!"{printApp fn} {" ".intercalate (args.map printUnary)}"
  | .unop .not e       => s!"not {printAtom e}"
  | .ref e             => s!"ref {printAtom e}"
  | .inj tag arity e   => s!"(inj {tag}/{arity} {printAtom e})"
  | .assert e          => s!"assert {printAtom e}"
  | e => printUnary e

-- Prefix unary operators.
partial def printUnary : Expr → String
  | .unop .neg e => s!"-{printAtom e}"
  | .deref e     => s!"!{printAtom e}"
  | .unop (.proj n) e => s!"{printAtom e}.{n}"
  | e => printAtom e

partial def printAtom : Expr → String
  | .const c            => printConst c
  | .var name           => name
  | .fix self args _ body  => printFix self args body
  | .tuple es           => s!"({", ".intercalate (es.map printOr)})"
  | e                   => s!"({printExpr e})"

partial def printConst : Const → String
  | .int n  => if n < 0 then s!"({n})" else s!"{n}"
  | .bool b => if b then "true" else "false"
  | .unit   => "()"

-- Note: type annotations on `fix` nodes (args types, retTy) are not currently
-- printed. The printer would need to emit `(x : T)` and `: T` syntax for those.
partial def printFix (self : Binder) (args : List Binder) (body : Expr) : String :=
  match self with
  | .none =>
    let (allArgs, inner) := collectAnonArgs args body
    s!"fun {argsStr allArgs} -> {printExpr inner}"
  | .named f _ =>
    let (allArgs, inner) := collectFixArgs f args body
    s!"(let rec {f} {argsStr allArgs} = {printExpr inner} in {f})"

end

def Expr.print (e : Expr) : String := printExpr e

def Decl.print (d : Decl Expr) : String :=
  let decl := match d.body with
    | .fix (.named f _) args _ inner =>
      let (allArgs, innerBody) := collectFixArgs f args inner
      let nameMatchesF := match d.name with | .named n _ => n == f | .none => false
      if nameMatchesF then
        s!"let rec {f} {argsStr allArgs} = {printExpr innerBody}"
      else
        s!"let {d.name.print} = (let rec {f} {argsStr allArgs} = {printExpr innerBody} in {f})"
    | .fix .none args _ inner =>
      let (allArgs, innerBody) := collectAnonArgs args inner
      s!"let {d.name.print} {argsStr allArgs} = {printExpr innerBody}"
    | body => s!"let {d.name.print} = {printExpr body}"
  match d.spec with
  | .none => decl
  | .some e => s!"{decl} [@@spec {printExpr e}]"

def Program.print (p : Program) : String :=
  "\n;;\n".intercalate (p.map Decl.print)

end TinyML
