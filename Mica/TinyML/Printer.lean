import Mica.TinyML.Expr

namespace TinyML

def BinOp.toString : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/"
  | .eq => "=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .and => "&&" | .or => "||"
  | .pair => ","

def UnOp.toString : UnOp → String
  | .neg => "-" | .not => "not"
  | .fst => "fst" | .snd => "snd"
  | .inl => "Either.Left" | .inr => "Either.Right"
  | .proj n => s!".{n}"

def Binder.print : Binder → String
  | .none => "_"
  | .named name => name

-- Collect successive fix arguments with the same named self binder.
private partial def collectFixArgs (f : String) : Binder → Expr → List Binder × Expr
  | arg, .fix (.named f') arg' _ _ inner =>
    if f == f' then
      let (args, body) := collectFixArgs f arg' inner
      (arg :: args, body)
    else ([arg], .fix (.named f') arg' none none inner)
  | arg, e => ([arg], e)

-- Collect successive anonymous fix arguments.
private partial def collectAnonArgs : Binder → Expr → List Binder × Expr
  | arg, .fix .none arg' _ _ inner =>
    let (args, body) := collectAnonArgs arg' inner
    (arg :: args, body)
  | arg, e => ([arg], e)

private def argsStr (args : List Binder) : String :=
  " ".intercalate (args.map Binder.print)

mutual

partial def printExpr : Expr → String
  | .letIn .none bound body => s!"{printOr bound};\n{printExpr body}"
  | .letIn name bound body => printLetIn name bound body
  | .ifThenElse cond thn els =>
    s!"if {printExpr cond} then {printExpr thn} else {printExpr els}"
  | .store l r => s!"{printOr l} := {printOr r}"
  | e => printOr e

-- Print a let binding, recognising recursive and eta-contracted forms.
partial def printLetIn (name : Binder) (bound body : Expr) : String :=
  match bound with
  | .fix (.named f) arg _ _ inner =>
    let (args, innerBody) := collectFixArgs f arg inner
    if name == .named f then
      s!"let rec {f} {argsStr args} = {printExpr innerBody} in\n{printExpr body}"
    else
      s!"let {name.print} = (let rec {f} {argsStr args} = {printExpr innerBody} in {f}) in\n{printExpr body}"
  | .fix .none arg _ _ inner =>
    let (args, innerBody) := collectAnonArgs arg inner
    s!"let {name.print} {argsStr args} = {printExpr innerBody} in\n{printExpr body}"
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
  | e => printApp e

-- Function-application-level unary operators.
partial def printApp : Expr → String
  | .app fn arg        => s!"{printApp fn} {printUnary arg}"
  | .unop .not e       => s!"not {printAtom e}"
  | .ref e             => s!"ref {printAtom e}"
  | .unop .inl e       => s!"Either.Left {printAtom e}"
  | .unop .inr e       => s!"Either.Right {printAtom e}"
  | .assert e          => s!"assert {printAtom e}"
  | e => printUnary e

-- Prefix unary operators.
partial def printUnary : Expr → String
  | .unop .neg e => s!"-{printAtom e}"
  | .deref e     => s!"!{printAtom e}"
  | .unop (.proj n) e => s!"{printAtom e}.{n}"
  | e => printAtom e

partial def printAtom : Expr → String
  | .val v              => printVal v
  | .var name           => name
  | .fix self arg _ _ body  => printFix self arg body
  | .tuple es           => s!"({", ".intercalate (es.map printOr)})"
  | e                   => s!"({printExpr e})"

partial def printVal : Val → String
  | .int n         => if n < 0 then s!"({n})" else s!"{n}"
  | .bool b        => if b then "true" else "false"
  | .unit          => "()"
  | .pair a b      => s!"({printVal a}, {printVal b})"
  | .tuple vs      => s!"({", ".intercalate (vs.map printVal)})"
  | .inl v         => s!"Either.Left {printValAtom v}"
  | .inr v         => s!"Either.Right {printValAtom v}"
  | .loc l         => s!"(assert false (* loc:{l} *))"
  | .fix self arg _ _ body => printFix self arg body

-- Atom-level Val printer (adds parens for compound values).
partial def printValAtom : Val → String
  | .int n    => if n < 0 then s!"({n})" else s!"{n}"
  | .bool b   => if b then "true" else "false"
  | .unit     => "()"
  | v         => s!"({printVal v})"

-- CR claude: type annotations on `fix` nodes (argTy, retTy) are currently not
-- printed. The printer needs to be extended to emit `(x : T)` and `: T` syntax
-- for annotated binders and return types.
partial def printFix (self arg : Binder) (body : Expr) : String :=
  match self with
  | .none =>
    let (args, inner) := collectAnonArgs arg body
    s!"fun {argsStr args} -> {printExpr inner}"
  | .named f =>
    let (args, inner) := collectFixArgs f arg body
    s!"(let rec {f} {argsStr args} = {printExpr inner} in {f})"

end

def Expr.print (e : Expr) : String := printExpr e

def Decl.print (d : Decl Expr) : String :=
  let decl := match d.body with
    | .fix (.named f) arg _ _ inner =>
      if d.name == .named f then
        let (args, innerBody) := collectFixArgs f arg inner
        s!"let rec {f} {argsStr args} = {printExpr innerBody}"
      else
        let (args, innerBody) := collectFixArgs f arg inner
        s!"let {d.name.print} = (let rec {f} {argsStr args} = {printExpr innerBody} in {f})"
    | .fix .none arg _ _ inner =>
      let (args, innerBody) := collectAnonArgs arg inner
      s!"let {d.name.print} {argsStr args} = {printExpr innerBody}"
    | body => s!"let {d.name.print} = {printExpr body}"
  match d.spec with
  | .none => decl
  | .some e => s!"{decl} [@@spec {printExpr e}]"

def Program.print (p : Program) : String :=
  "\n;;\n".intercalate (p.map Decl.print)

end TinyML
