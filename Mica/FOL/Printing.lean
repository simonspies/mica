import Mica.FOL.Formulas

/-! ## Printing for FOL Types

Two serialization targets:
- `toSMTLIB` — SMT-LIB2 s-expression syntax (used by the solver backend).
- `toStringHum` — human-readable infix notation (used for display).
-/


-- ---------------------------------------------------------------------------
-- SMT-LIB2 serialization
-- ---------------------------------------------------------------------------

def Srt.toSMTLIB : Srt → String
  | .int     => "Int"
  | .bool    => "Bool"
  | .value   => "Value"
  | .vallist => "ValueList"

def UnOp.toSMTLIB : UnOp τ₁ τ₂ → String
  | .ofInt   => "of_int"
  | .ofBool  => "of_bool"
  | .toInt   => "to_int"
  | .toBool  => "to_bool"
  | .neg     => "-"
  | .not     => "not"
  | .ofValList => "of_tuple"
  | .toValList => "to_tuple"
  | .vhead   => "vhd"
  | .vtail   => "vtl"
  | .visnil  => "is-vnil"
  | .mkInj tag arity => s!"of_inj {tag} {arity}"
  | .tagOf   => "tag_of"
  | .arityOf => "arity_of"
  | .payloadOf => "payload_of"
  | .uninterpreted name _ _ => name

def BinOp.toSMTLIB : BinOp τ₁ τ₂ τ₃ → String
  | .add   => "+"
  | .sub   => "-"
  | .mul   => "*"
  | .div   => "div"
  | .mod   => "mod"
  | .less  => "<"
  | .gt    => ">"
  | .ge    => ">="
  | .eq    => "="
  | .vcons => "vcons"
  | .uninterpreted name _ _ _ => name

def UnPred.toSMTLIB : UnPred τ → String
  | .isInt   => "is-of_int"
  | .isBool  => "is-of_bool"
  | .isTuple => "is-of_tuple"
  | .isInj _ _ => ""  -- handled specially in Formula.toSMTLIB

def BinPred.toSMTLIB : BinPred τ₁ τ₂ → String
  | .lt => "<"
  | .le => "<="

def Term.toSMTLIB : Term τ → String
  | .var _ name   => name
  | .const (.i n)   => if n ≥ 0 then s!"{n}" else s!"(- {-n})"
  | .const (.b b)   => if b then "true" else "false"
  | .const .unit    => "(of_other unit_val)"
  | .const .vnil    => "vnil"
  | .const (.uninterpreted name _) => name
  | .unop op a    => s!"({op.toSMTLIB} {a.toSMTLIB})"
  | .binop op a b => s!"({op.toSMTLIB} {a.toSMTLIB} {b.toSMTLIB})"
  | .ite c t e    => s!"(ite {c.toSMTLIB} {t.toSMTLIB} {e.toSMTLIB})"

def Formula.toSMTLIB : Formula → String
  | .true_          => "true"
  | .false_         => "false"
  | .eq _τ a b      => s!"(= {a.toSMTLIB} {b.toSMTLIB})"
  | .unpred p v     => match p with
    | .isInj tag arity => s!"(and (is-of_inj {v.toSMTLIB}) (= (tag_of {v.toSMTLIB}) {tag}) (= (arity_of {v.toSMTLIB}) {arity}))"
    | _ => s!"({p.toSMTLIB} {v.toSMTLIB})"
  | .binpred p a b  => s!"({p.toSMTLIB} {a.toSMTLIB} {b.toSMTLIB})"
  | .not φ          => s!"(not {φ.toSMTLIB})"
  | .and φ ψ        => s!"(and {φ.toSMTLIB} {ψ.toSMTLIB})"
  | .or φ ψ         => s!"(or {φ.toSMTLIB} {ψ.toSMTLIB})"
  | .implies φ ψ    => s!"(=> {φ.toSMTLIB} {ψ.toSMTLIB})"
  | .forall_ x τ φ  => s!"(forall (({x} {τ.toSMTLIB})) {φ.toSMTLIB})"
  | .exists_ x τ φ  => s!"(exists (({x} {τ.toSMTLIB})) {φ.toSMTLIB})"


-- ---------------------------------------------------------------------------
-- Human-readable infix printing with minimal parentheses
-- ---------------------------------------------------------------------------

-- Precedence levels, ordered lowest to highest (constructor order drives Ord).
private inductive Prec where
  | bottom   -- if/then/else, ∀, ∃  (lowest)
  | implies  -- =>                  (right-assoc)
  | or_      -- ||                  (left-assoc)
  | and_     -- &&                  (left-assoc)
  | not_     -- not                 (prefix)
  | cmp      -- =, <, <=
  | add      -- +, -                (left-assoc)
  | mul      -- *, /                (left-assoc)
  | top      --  atoms              (highest)
  deriving Ord

private def Prec.lt (a b : Prec) : Bool := compare a b == .lt

private def parens (wrap : Bool) (s : String) : String :=
  if wrap then s!"({s})" else s

private def termStr (p : Prec) : {τ : Srt} → Term τ → String
  | _, .var _ x        => x
  | _, .const (.i n)   => if n < 0 then s!"({n})" else s!"{n}"
  | _, .const (.b b)   => if b then "true" else "false"
  | _, .const .unit    => "()"
  | _, .const .vnil    => "[]"
  | _, .const (.uninterpreted name _) => name
  | _, .unop op a  => match op with
    | .ofInt   => termStr p a     -- transparent coercion
    | .ofBool  => termStr p a     -- transparent coercion
    | .toInt   => s!"toInt({termStr .bottom a})"
    | .toBool  => s!"toBool({termStr .bottom a})"
    | .neg     => parens (Prec.lt .mul p) s!"-{termStr .top a}"
    | .not     => parens (Prec.lt .not_ p) s!"!{termStr .top a}"
    | .ofValList => s!"tuple({termStr .bottom a})"
    | .toValList => s!"untuple({termStr .bottom a})"
    | .vhead   => s!"hd({termStr .bottom a})"
    | .vtail   => s!"tl({termStr .bottom a})"
    | .visnil  => s!"isnil({termStr .bottom a})"
    | .mkInj tag arity => s!"inj({tag}/{arity}, {termStr .bottom a})"
    | .tagOf   => s!"tag({termStr .bottom a})"
    | .arityOf => s!"arity({termStr .bottom a})"
    | .payloadOf => s!"payload({termStr .bottom a})"
    | .uninterpreted name _ _ => s!"{name}({termStr .bottom a})"
  | _, .binop op a b => match op with
    | .add   => parens (Prec.lt .add p) s!"{termStr .add a} + {termStr .mul b}"
    | .sub   => parens (Prec.lt .add p) s!"{termStr .add a} - {termStr .mul b}"
    | .mul   => parens (Prec.lt .mul p) s!"{termStr .mul a} * {termStr .top b}"
    | .div   => parens (Prec.lt .mul p) s!"{termStr .mul a} / {termStr .top b}"
    | .mod   => parens (Prec.lt .mul p) s!"{termStr .mul a} % {termStr .top b}"
    | .less  => parens (Prec.lt .cmp p) s!"{termStr .add a} < {termStr .add b}"
    | .gt    => parens (Prec.lt .cmp p) s!"{termStr .add a} > {termStr .add b}"
    | .ge    => parens (Prec.lt .cmp p) s!"{termStr .add a} >= {termStr .add b}"
    | .eq    => parens (Prec.lt .cmp p) s!"{termStr .add a} = {termStr .add b}"
    | .vcons => parens (Prec.lt .top p) s!"{termStr .top a} :: {termStr .top b}"
    | .uninterpreted name _ _ _ => s!"{name}({termStr .bottom a}, {termStr .bottom b})"
  | _, .ite c t e  => parens (Prec.lt .bottom p) s!"if {termStr .bottom c} then {termStr .bottom t} else {termStr .bottom e}"

def Term.toStringHum {τ : Srt} (t : Term τ) : String := termStr .bottom t

private def formulaStr (p : Prec) : Formula → String
  | .true_           => "true"
  | .false_          => "false"
  | .unpred pred v   => match pred with
    | .isInt   => s!"isInt({termStr .bottom v})"
    | .isBool  => s!"isBool({termStr .bottom v})"
    | .isTuple => s!"isTuple({termStr .bottom v})"
    | .isInj tag arity => s!"isInj({tag}/{arity}, {termStr .bottom v})"
  | .binpred pred a b => match pred with
    | .lt => parens (Prec.lt .cmp p) s!"{termStr .add a} < {termStr .add b}"
    | .le => parens (Prec.lt .cmp p) s!"{termStr .add a} <= {termStr .add b}"
  | .eq _ a b        => parens (Prec.lt .cmp     p) s!"{termStr .add a} = {termStr .add b}"
  | .not φ           => parens (Prec.lt .not_    p) s!"not {formulaStr .cmp φ}"
  | .and φ ψ         => parens (Prec.lt .and_    p) s!"{formulaStr .and_ φ} && {formulaStr .not_ ψ}"
  | .or  φ ψ         => parens (Prec.lt .or_     p) s!"{formulaStr .or_ φ} || {formulaStr .and_ ψ}"
  | .implies φ ψ     => parens (Prec.lt .implies p) s!"{formulaStr .or_ φ} => {formulaStr .implies ψ}"
  | .forall_ x τ φ   => parens (Prec.lt .bottom  p) s!"∀ {x} : {repr τ}, {formulaStr .bottom φ}"
  | .exists_ x τ φ   => parens (Prec.lt .bottom  p) s!"∃ {x} : {repr τ}, {formulaStr .bottom φ}"

def Formula.toStringHum (φ : Formula) : String := formulaStr .bottom φ

def Pred.toStringHum {α : Type} (showA : α → String) : Pred α → String
  | (x, a) => s!"λ {x} ->\n{showA a}"

def MultiPred.toStringHum {α : Type} (showA : α → String) : MultiPred α → String
  | ([], body)   => showA body
  | (args, body) => s!"λ {" ".intercalate args} ->\n{showA body}"
