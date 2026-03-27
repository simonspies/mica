import Mica.Frontend.Spec
import Mica.TinyML.Expr

/-!
# Spec Parser

Translates `TinyML.Expr` (from elaborated `[@@spec ...]` attributes) into the
untyped `Spec` AST. This is purely structural recognition — no sort checking.
-/

namespace Spec

private abbrev M := Except String

private def parseBinOp : TinyML.BinOp → BinOp
  | .add => .add | .sub => .sub | .mul => .mul | .div => .div | .mod => .mod
  | .eq => .eq | .lt => .lt | .le => .le | .gt => .gt | .ge => .ge
  | .and => .and | .or => .or

private def parseTerm : TinyML.Expr → M Term
  | .var x => .ok (.var x)
  | .val (.int n) => .ok (.int n)
  | .val (.bool b) => .ok (.bool b)
  | .val .unit => .ok .unit
  | .binop op l r => do
    .ok (.binop (parseBinOp op) (← parseTerm l) (← parseTerm r))
  | .unop .neg e => do .ok (.unop .neg (← parseTerm e))
  | .unop .not e => do .ok (.unop .not (← parseTerm e))
  | .unop (.proj n) e => do .ok (.unop (.proj n) (← parseTerm e))
  | .tuple es => do .ok (.tuple (← es.mapM parseTerm))
  | .inj tag arity payload => do .ok (.unop (.inj tag arity) (← parseTerm payload))
  | .app (.var "inj") [.val (.int tag), .val (.int arity), payload] => do
    .ok (.unop (.inj tag.toNat arity.toNat) (← parseTerm payload))
  | .app (.var "tagof") [e] => do .ok (.unop .tagof (← parseTerm e))
  | .app (.var "arityof") [e] => do .ok (.unop .arityof (← parseTerm e))
  | .app (.var "payloadof") [e] => do .ok (.unop .payloadof (← parseTerm e))
  | .ifThenElse c t e => do
    .ok (.ite (← parseTerm c) (← parseTerm t) (← parseTerm e))
  | e => .error s!"unexpected term in spec: {repr e}"

private def parsePred : TinyML.Expr → M Pred
  | .app (.var "isint") [e] => do .ok (.isint (← parseTerm e))
  | .app (.var "isbool") [e] => do .ok (.isbool (← parseTerm e))
  | .app (.var "isinj") [.val (.int tag), .val (.int arity), e] => do
    .ok (.isinj tag.toNat arity.toNat (← parseTerm e))
  | e => .error s!"expected type predicate (isint, isbool, isinj), got {repr e}"

private def parseAssert (inner : TinyML.Expr → M α)
    (bareAssert : TinyML.Expr → M (Assert α)) : TinyML.Expr → M (Assert α)
  | .app (.var "ret") [e] => do .ok (.ret (← inner e))
  | .app (.app (.var "bind") [e1]) [.fix .none [.named x _] _ e2] => do
    let pred ← parsePred e1
    let rest ← parseAssert inner bareAssert e2
    .ok (.bind pred x rest)
  | .letIn (.named x _) bound body => do
    let t ← parseTerm bound
    let rest ← parseAssert inner bareAssert body
    .ok (.let_ x t rest)
  | .letIn .none (.assert cond) body => do
    let c ← parseTerm cond
    let rest ← parseAssert inner bareAssert body
    .ok (.assert c rest)
  | .assert cond => bareAssert cond
  | .ifThenElse cond thn els => do
    let c ← parseTerm cond
    .ok (.ite c (← parseAssert inner bareAssert thn) (← parseAssert inner bareAssert els))
  | e => .error s!"expected assertion, got {repr e}"

private def parsePost : TinyML.Expr → M Post :=
  parseAssert
    (fun | .val .unit => .ok ()
         | e => .error s!"expected (), got {repr e}")
    (fun cond => do .ok (.assert (← parseTerm cond) (.ret ())))

private def parsePre : TinyML.Expr → M Pre :=
  parseAssert
    (fun | .fix .none [.named x _] _ body => do
           let post ← parsePost body
           .ok (x, post)
         | e => .error s!"expected fun v -> ..., got {repr e}")
    (fun _ => .error "bare assert is only allowed in postconditions")

private def peelBinders : TinyML.Expr → M Body
  | .fix .none args _ body => do
    let names ← getNames args
    if names.isEmpty then .error "spec must bind at least one argument"
    else do
      let pre ← parsePre body
      .ok (names, pre)
  | e => .error s!"expected fun x -> ..., got {repr e}"
where
  getNames : List TinyML.Binder → M (List String)
    | [] => .ok []
    | .named x _ :: rest => do let xs ← getNames rest; .ok (x :: xs)
    | .none :: _ => .error "unnamed binder in spec is not allowed"

def parse (e : TinyML.Expr) : M Body :=
  peelBinders e

end Spec
