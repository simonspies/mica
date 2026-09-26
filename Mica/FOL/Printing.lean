-- SUMMARY: Human-readable notation for first-order syntax.
import Mica.FOL.Formulas
import Mica.Base.Hex

-- ---------------------------------------------------------------------------
-- Human-readable infix printing with minimal parentheses
-- ---------------------------------------------------------------------------

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

def Srt.toStringHum : Srt → String
  | .int     => "int"
  | .bool    => "bool"
  | .bv width => s!"bv{width}"
  | .char    => "char"
  | .string  => "string"
  | .float   => "float"
  | .value   => "value"
  | .vallist => "value list"
  | .vec     => "vec"

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
  | _, .const (.bv (width := width) bits) => s!"{bits.toNat}#{width}"
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
    | .ofInt32 => termStr p a     -- transparent coercion
    | .ofInt64 => termStr p a     -- transparent coercion
    | .ofChar => termStr p a      -- transparent coercion
    | .ofString => termStr p a    -- transparent coercion
    | .ofFloat => termStr p a     -- transparent coercion
    | .toInt   => s!"toInt({termStr .bottom a})"
    | .toBool  => s!"toBool({termStr .bottom a})"
    | .toInt32 => s!"toInt32({termStr .bottom a})"
    | .toInt64 => s!"toInt64({termStr .bottom a})"
    | .toChar => s!"toChar({termStr .bottom a})"
    | .toString => s!"toString({termStr .bottom a})"
    | .toFloat => s!"toFloat({termStr .bottom a})"
    | .charToInt => s!"charCode({termStr .bottom a})"
    | .intToChar => s!"charChr({termStr .bottom a})"
    | .intToBv width => s!"bv{width}({termStr .bottom a})"
    | .bvToNat _ => s!"bvNat({termStr .bottom a})"
    | .bvNeg _ => s!"bvneg({termStr .bottom a})"
    | .bvNot _ => s!"bvnot({termStr .bottom a})"
    | .bvSignExtend _ _ _ => s!"signExtend({termStr .bottom a})"
    | .bvExtractLsb _ _ _ => s!"extractLsb({termStr .bottom a})"
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
    | .arrayLen => s!"arrayLength({termStr .bottom a})"
    | .vhead   => s!"hd({termStr .bottom a})"
    | .vtail   => s!"tl({termStr .bottom a})"
    | .visnil  => s!"isnil({termStr .bottom a})"
    | .ofInj tag arity => s!"ofInj({tag}/{arity}, {termStr .bottom a})"
    | .tagOf   => s!"tag({termStr .bottom a})"
    | .arityOf => s!"arity({termStr .bottom a})"
    | .payloadOf => s!"payload({termStr .bottom a})"
    | .vecLen  => s!"length({termStr .bottom a})"
    | .ofVec   => termStr p a     -- transparent coercion
    | .toVec   => s!"toVec({termStr .bottom a})"
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
    | .bvAdd _ => s!"bvadd({termStr .bottom a}, {termStr .bottom b})"
    | .bvSub _ => s!"bvsub({termStr .bottom a}, {termStr .bottom b})"
    | .bvMul _ => s!"bvmul({termStr .bottom a}, {termStr .bottom b})"
    | .bvSDiv _ => s!"bvsdiv({termStr .bottom a}, {termStr .bottom b})"
    | .bvUDiv _ => s!"bvudiv({termStr .bottom a}, {termStr .bottom b})"
    | .bvSRem _ => s!"bvsrem({termStr .bottom a}, {termStr .bottom b})"
    | .bvURem _ => s!"bvurem({termStr .bottom a}, {termStr .bottom b})"
    | .bvAnd _ => s!"bvand({termStr .bottom a}, {termStr .bottom b})"
    | .bvOr _ => s!"bvor({termStr .bottom a}, {termStr .bottom b})"
    | .bvXor _ => s!"bvxor({termStr .bottom a}, {termStr .bottom b})"
    | .bvSLt _ => s!"bvslt({termStr .bottom a}, {termStr .bottom b})"
    | .bvULt _ => s!"bvult({termStr .bottom a}, {termStr .bottom b})"
    | .bvShl _ => s!"bvshl({termStr .bottom a}, {termStr .bottom b})"
    | .bvAShr _ => s!"bvashr({termStr .bottom a}, {termStr .bottom b})"
    | .bvLShr _ => s!"bvlshr({termStr .bottom a}, {termStr .bottom b})"
    | .seqConcat => parens (Prec.lt .add p) s!"{termStr .add a} ++ {termStr .mul b}"
    | .seqNth => s!"nth({termStr .bottom a}, {termStr .bottom b})"
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
    | .vecGet  => s!"get({termStr .bottom a}, {termStr .bottom b})"
    | .vecMake => s!"make({termStr .bottom a}, {termStr .bottom b})"
    | .uninterpreted name _ _ _ => s!"{name}({termStr .bottom a}, {termStr .bottom b})"
  | _, .terop op a b c => match op with
    | .seqExtract => s!"extract({termStr .bottom a}, {termStr .bottom b}, {termStr .bottom c})"
    | .vecSet => s!"set({termStr .bottom a}, {termStr .bottom b}, {termStr .bottom c})"
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
    | .isInt32 => s!"isInt32({termStr .bottom v})"
    | .isInt64 => s!"isInt64({termStr .bottom v})"
    | .isChar  => s!"isChar({termStr .bottom v})"
    | .isStr   => s!"isStr({termStr .bottom v})"
    | .isFloat => s!"isFloat({termStr .bottom v})"
    | .isLoc   => s!"isLoc({termStr .bottom v})"
    | .isTuple => s!"isTuple({termStr .bottom v})"
    | .isOfInj => s!"isOfInj({termStr .bottom v})"
    | .isVec   => s!"isVec({termStr .bottom v})"
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
  | .forall_ x τ _ φ => parens (Prec.lt .bottom  p) s!"∀ {x} : {τ.toStringHum}, {formulaStr .bottom φ}"
  | .exists_ x τ φ   => parens (Prec.lt .bottom  p) s!"∃ {x} : {τ.toStringHum}, {formulaStr .bottom φ}"

def Formula.toStringHum (φ : Formula) : String := formulaStr .bottom φ
