-- SUMMARY: Serialization of first-order syntax to SMT-LIB and human-readable notation.
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
  | .char    => "(_ BitVec 8)"
  | .string  => "(Seq (_ BitVec 8))"
  | .float   => "(_ FloatingPoint 11 53)"
  | .value   => "Value"
  | .vallist => "ValueList"

def UnOp.toSMTLIB : UnOp τ₁ τ₂ → String
  | .ofInt   => "of_int"
  | .ofBool  => "of_bool"
  | .ofChar => "of_char"
  | .ofString => "of_string"
  | .ofFloat => "of_float"
  | .toInt   => "to_int"
  | .toBool  => "to_bool"
  | .toChar => "to_char"
  | .toString => "to_string"
  | .toFloat => "to_float"
  | .charToInt => "bv2nat"
  | .intToChar => "(_ int2bv 8)"
  | .seqLen => "seq.len"
  | .fpAbs => "fp.abs"
  | .fpNeg => "fp.neg"
  | .fpSqrt => "fp.sqrt roundNearestTiesToEven"
  | .fpIsNaN => "fp.isNaN"
  | .fpIsInfinite => "fp.isInfinite"
  | .fpIsNegative => "fp.isNegative"
  | .fpOfInt => "(_ to_fp 11 53) roundNearestTiesToEven"
  | .neg     => "-"
  | .not     => "not"
  | .ofValList => "of_tuple"
  | .toValList => "to_tuple"
  | .arrayLengthOf => "array_length"
  | .vhead   => "vhd"
  | .vtail   => "vtl"
  | .visnil  => "is-vnil"
  | .ofInj tag arity => s!"of_inj {tag} {arity}"
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
  | .seqConcat => "seq.++"
  | .seqPrefixOf => "seq.prefixof"
  | .seqSuffixOf => "seq.suffixof"
  | .fpAdd => "fp.add roundNearestTiesToEven"
  | .fpSub => "fp.sub roundNearestTiesToEven"
  | .fpMul => "fp.mul roundNearestTiesToEven"
  | .fpDiv => "fp.div roundNearestTiesToEven"
  | .fpEq  => "fp.eq"
  | .fpLt  => "fp.lt"
  | .fpLe  => "fp.leq"
  | .vcons => "vcons"
  | .uninterpreted name _ _ _ => name

def TerOp.toSMTLIB : TerOp τ₁ τ₂ τ₃ τ₄ → String
  | .uninterpreted name _ _ _ _ => name

def UnPred.toSMTLIB : UnPred τ → String
  | .isInt   => "is-of_int"
  | .isBool  => "is-of_bool"
  | .isChar  => "is-of_char"
  | .isStr   => "is-of_string"
  | .isFloat => "is-of_float"
  | .isLoc   => "is-of_loc"
  | .isTuple => "is-of_tuple"
  | .isOfInj => "is-of_inj"
  | .uninterpreted name _ => name

def BinPred.toSMTLIB : BinPred τ₁ τ₂ → String
  | .lt => "<"
  | .le => "<="
  | .uninterpreted name _ _ => name

private def hexDigit (n : Nat) : Char :=
  match n with
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3'
  | 4 => '4' | 5 => '5' | 6 => '6' | 7 => '7'
  | 8 => '8' | 9 => '9' | 10 => 'A' | 11 => 'B'
  | 12 => 'C' | 13 => 'D' | 14 => 'E' | _ => 'F'

private def byteHex (b : UInt8) : String :=
  let n := b.toNat
  String.ofList [hexDigit (n / 16), hexDigit (n % 16)]

private def byteToSMTLIB (b : UInt8) : String :=
  s!"(seq.unit #x{byteHex b})"

/-- The 16 big-endian hex digits of a `UInt64`, for an `#x…` bitvector literal. -/
private def uint64Hex (b : UInt64) : String :=
  let n := b.toNat
  String.ofList ((List.range 16).reverse.map (fun i => hexDigit ((n / (16 ^ i)) % 16)))

private def stringConstToSMTLIB : List UInt8 → String
  | [] => "(as seq.empty (Seq (_ BitVec 8)))"
  | s => s!"(seq.++ {" ".intercalate (s.map byteToSMTLIB)})"

private def byteToHum (b : UInt8) : String :=
  let n := b.toNat
  if n == 10 then "\\n"
  else if n == 9 then "\\t"
  else if n == 13 then "\\r"
  else if n == 34 then "\\\""
  else if n == 92 then "\\\\"
  else if 32 ≤ n && n < 127 then
    String.singleton (Char.ofNat n)
  else s!"\\x{byteHex b}"

def Term.toSMTLIB : Term τ → String
  | .var _ name   => name
  | .const (.i n)   => if n ≥ 0 then s!"{n}" else s!"(- {-n})"
  | .const (.b b)   => if b then "true" else "false"
  | .const (.char c) => s!"#x{byteHex c}"
  | .const (.str s) => stringConstToSMTLIB s
  | .const (.fp bits) => s!"((_ to_fp 11 53) #x{uint64Hex bits})"
  | .const .fpNaN    => "(_ NaN 11 53)"
  | .const .fpPosInf => "(_ +oo 11 53)"
  | .const .fpNegInf => "(_ -oo 11 53)"
  | .const .unit    => "(of_other unit_val)"
  | .const .vnil    => "vnil"
  | .const (.uninterpreted name _) => name
  | .unop op a    => s!"({op.toSMTLIB} {a.toSMTLIB})"
  | .binop op a b => s!"({op.toSMTLIB} {a.toSMTLIB} {b.toSMTLIB})"
  | .terop op a b c => s!"({op.toSMTLIB} {a.toSMTLIB} {b.toSMTLIB} {c.toSMTLIB})"
  | .ite c t e    => s!"(ite {c.toSMTLIB} {t.toSMTLIB} {e.toSMTLIB})"

def Pattern.toSMTLIB : Pattern → String
  | .term t => t.toSMTLIB
  | .unpred p t => s!"({p.toSMTLIB} {t.toSMTLIB})"
  | .binpred p t₁ t₂ => s!"({p.toSMTLIB} {t₁.toSMTLIB} {t₂.toSMTLIB})"

def Formula.toSMTLIB : Formula → String
  | .true_          => "true"
  | .false_         => "false"
  | .eq _τ a b      => s!"(= {a.toSMTLIB} {b.toSMTLIB})"
  | .unpred p v     => s!"({p.toSMTLIB} {v.toSMTLIB})"
  | .binpred p a b  => s!"({p.toSMTLIB} {a.toSMTLIB} {b.toSMTLIB})"
  | .not φ          => s!"(not {φ.toSMTLIB})"
  | .and φ ψ        => s!"(and {φ.toSMTLIB} {ψ.toSMTLIB})"
  | .or φ ψ         => s!"(or {φ.toSMTLIB} {ψ.toSMTLIB})"
  | .implies φ ψ    => s!"(=> {φ.toSMTLIB} {ψ.toSMTLIB})"
  | .forall_ x τ ps φ =>
    let body := match ps with
      | [] => φ.toSMTLIB
      | ps => s!"(! {φ.toSMTLIB} :pattern ({" ".intercalate (ps.map Pattern.toSMTLIB)}))"
    s!"(forall (({x} {τ.toSMTLIB})) {body})"
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
  | _, .const (.char c) => s!"'{byteToHum c}'"
  | _, .const (.str s) => s!"\"{s.map byteToHum |>.foldl (· ++ ·) ""}\""
  | _, .const (.fp bits) => toString (Float.ofBits bits)
  | _, .const .fpNaN    => "nan"
  | _, .const .fpPosInf => "inf"
  | _, .const .fpNegInf => "-inf"
  | _, .const .unit    => "()"
  | _, .const .vnil    => "[]"
  | _, .const (.uninterpreted name _) => name
  | _, .unop op a  => match op with
    | .ofInt   => termStr p a     -- transparent coercion
    | .ofBool  => termStr p a     -- transparent coercion
    | .ofChar => termStr p a      -- transparent coercion
    | .ofString => termStr p a    -- transparent coercion
    | .ofFloat => termStr p a     -- transparent coercion
    | .toInt   => s!"toInt({termStr .bottom a})"
    | .toBool  => s!"toBool({termStr .bottom a})"
    | .toChar => s!"toChar({termStr .bottom a})"
    | .toString => s!"toString({termStr .bottom a})"
    | .toFloat => s!"toFloat({termStr .bottom a})"
    | .charToInt => s!"charCode({termStr .bottom a})"
    | .intToChar => s!"charChr({termStr .bottom a})"
    | .seqLen => s!"len({termStr .bottom a})"
    | .fpAbs => s!"fabs({termStr .bottom a})"
    | .fpNeg => parens (Prec.lt .mul p) s!"-.{termStr .top a}"
    | .fpSqrt => s!"sqrt({termStr .bottom a})"
    | .fpIsNaN => s!"isNaN({termStr .bottom a})"
    | .fpIsInfinite => s!"isInfinite({termStr .bottom a})"
    | .fpIsNegative => s!"isNegative({termStr .bottom a})"
    | .fpOfInt => s!"float({termStr .bottom a})"
    | .neg     => parens (Prec.lt .mul p) s!"-{termStr .top a}"
    | .not     => parens (Prec.lt .not_ p) s!"!{termStr .top a}"
    | .ofValList => s!"tuple({termStr .bottom a})"
    | .toValList => s!"untuple({termStr .bottom a})"
    | .arrayLengthOf => s!"arrayLength({termStr .bottom a})"
    | .vhead   => s!"hd({termStr .bottom a})"
    | .vtail   => s!"tl({termStr .bottom a})"
    | .visnil  => s!"isnil({termStr .bottom a})"
    | .ofInj tag arity => s!"ofInj({tag}/{arity}, {termStr .bottom a})"
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
    | .seqConcat => parens (Prec.lt .add p) s!"{termStr .add a} ++ {termStr .mul b}"
    | .seqPrefixOf => s!"prefixOf({termStr .bottom a}, {termStr .bottom b})"
    | .seqSuffixOf => s!"suffixOf({termStr .bottom a}, {termStr .bottom b})"
    | .fpAdd => parens (Prec.lt .add p) s!"{termStr .add a} +. {termStr .mul b}"
    | .fpSub => parens (Prec.lt .add p) s!"{termStr .add a} -. {termStr .mul b}"
    | .fpMul => parens (Prec.lt .mul p) s!"{termStr .mul a} *. {termStr .top b}"
    | .fpDiv => parens (Prec.lt .mul p) s!"{termStr .mul a} /. {termStr .top b}"
    | .fpEq  => parens (Prec.lt .cmp p) s!"{termStr .add a} =. {termStr .add b}"
    | .fpLt  => parens (Prec.lt .cmp p) s!"{termStr .add a} <. {termStr .add b}"
    | .fpLe  => parens (Prec.lt .cmp p) s!"{termStr .add a} <=. {termStr .add b}"
    | .vcons => parens (Prec.lt .top p) s!"{termStr .top a} :: {termStr .top b}"
    | .uninterpreted name _ _ _ => s!"{name}({termStr .bottom a}, {termStr .bottom b})"
  | _, .terop op a b c => match op with
    | .uninterpreted name _ _ _ _ =>
      s!"{name}({termStr .bottom a}, {termStr .bottom b}, {termStr .bottom c})"
  | _, .ite c t e  => parens (Prec.lt .bottom p) s!"if {termStr .bottom c} then {termStr .bottom t} else {termStr .bottom e}"

def Term.toStringHum {τ : Srt} (t : Term τ) : String := termStr .bottom t

private def formulaStr (p : Prec) : Formula → String
  | .true_           => "true"
  | .false_          => "false"
  | .unpred pred v   => match pred with
    | .isInt   => s!"isInt({termStr .bottom v})"
    | .isBool  => s!"isBool({termStr .bottom v})"
    | .isChar  => s!"isChar({termStr .bottom v})"
    | .isStr   => s!"isStr({termStr .bottom v})"
    | .isFloat => s!"isFloat({termStr .bottom v})"
    | .isLoc   => s!"isLoc({termStr .bottom v})"
    | .isTuple => s!"isTuple({termStr .bottom v})"
    | .isOfInj => s!"isOfInj({termStr .bottom v})"
    | .uninterpreted name _ => s!"{name}({termStr .bottom v})"
  | .binpred pred a b => match pred with
    | .lt => parens (Prec.lt .cmp p) s!"{termStr .add a} < {termStr .add b}"
    | .le => parens (Prec.lt .cmp p) s!"{termStr .add a} <= {termStr .add b}"
    | .uninterpreted name _ _ => s!"{name}({termStr .bottom a}, {termStr .bottom b})"
  | .eq _ a b        => parens (Prec.lt .cmp     p) s!"{termStr .add a} = {termStr .add b}"
  | .not φ           => parens (Prec.lt .not_    p) s!"not {formulaStr .cmp φ}"
  | .and φ ψ         => parens (Prec.lt .and_    p) s!"{formulaStr .and_ φ} && {formulaStr .not_ ψ}"
  | .or  φ ψ         => parens (Prec.lt .or_     p) s!"{formulaStr .or_ φ} || {formulaStr .and_ ψ}"
  | .implies φ ψ     => parens (Prec.lt .implies p) s!"{formulaStr .or_ φ} => {formulaStr .implies ψ}"
  | .forall_ x τ _ φ => parens (Prec.lt .bottom  p) s!"∀ {x} : {repr τ}, {formulaStr .bottom φ}"
  | .exists_ x τ φ   => parens (Prec.lt .bottom  p) s!"∃ {x} : {repr τ}, {formulaStr .bottom φ}"

def Formula.toStringHum (φ : Formula) : String := formulaStr .bottom φ

def Pred.toStringHum {α : Type} (showA : α → String) : Pred α → String
  | (x, a) => s!"λ {x} ->\n{showA a}"

def MultiPred.toStringHum {α : Type} (showA : α → String) : MultiPred α → String
  | ([], body)   => showA body
  | (args, body) => s!"λ {" ".intercalate args} ->\n{showA body}"
