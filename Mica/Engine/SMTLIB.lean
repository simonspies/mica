-- SUMMARY: Serialization of first-order syntax to SMT-LIB.
import Mica.FOL.Formulas
import Mica.Base.Hex

-- ---------------------------------------------------------------------------
-- SMT-LIB2 serialization
-- ---------------------------------------------------------------------------

/-- The sorts and symbols that the printing below uses, with the axioms that
constrain them. Every solver session starts with these declarations. -/
def SMTLIB.declarations : String := "(declare-sort Other 0)
(declare-sort Loc 0)
(declare-sort Vec 0)
(declare-datatypes ((Value 0) (ValueList 0)) (
  ((of_int (to_int Int))
   (of_bool (to_bool Bool))
   (of_int32 (to_int32 (_ BitVec 32)))
   (of_int64 (to_int64 (_ BitVec 64)))
   (of_char (to_char (_ BitVec 8)))
   (of_string (to_string (Seq (_ BitVec 8))))
   (of_float (to_float (_ FloatingPoint 11 53)))
   (of_loc (to_loc Loc))
   (of_other (to_other Other))
   (of_tuple (to_tuple ValueList))
   (of_vec (to_vec Vec))
   (of_inj (tag_of Int) (arity_of Int) (payload_of Value)))
  ((vnil)
   (vcons (vhd Value) (vtl ValueList)))
))
(declare-const unit_val Other)

;; Constraints for the under specified values (e.g., vtail of unit is vtail)
(assert (forall ((v Value)) (! (=> (not ((_ is of_inj) v))
  (and (= (tag_of v) 0) (= (arity_of v) 0) (= (payload_of v) (of_other unit_val))))
  :pattern ((tag_of v)))))
(assert (forall ((v Value)) (! (=> (not ((_ is of_tuple) v)) (= (to_tuple v) vnil))
  :pattern ((to_tuple v)))))
(assert (= (vhd vnil) (of_other unit_val)))
(assert (= (vtl vnil) vnil))

;; A `Value` constructor would need to expose both length and location
(declare-fun array_length (Value) Int)

;; Vector theory. Vectors are exposed as arrays to Z3, and via
;; the uninterpreted functions vec_get, ... to Mica
(declare-fun vec_to_array (Vec) (Array Int Value))
(declare-fun vec_of_array ((Array Int Value) Int) Vec)
(declare-fun vec_length (Vec) Int)
(assert (forall ((w Vec)) (! (<= 0 (vec_length w)) :pattern ((vec_length w)))))

(assert (forall ((w Vec))
  (! (= (vec_of_array (vec_to_array w) (vec_length w)) w)
     :pattern ((vec_to_array w)))))
(assert (forall ((a (Array Int Value)) (n Int))
  (! (=> (<= 0 n) (= (vec_length (vec_of_array a n)) n))
     :pattern ((vec_of_array a n)))))
(assert (forall ((a (Array Int Value)) (n Int) (i Int))
  (! (=> (and (<= 0 i) (< i n))
         (= (select (vec_to_array (vec_of_array a n)) i) (select a i)))
     :pattern ((select (vec_to_array (vec_of_array a n)) i)))))

(declare-fun vec_get (Vec Int) Value)
(declare-fun vec_set (Vec Int Value) Vec)
(declare-fun vec_make (Int Value) Vec)
(assert (forall ((w Vec) (i Int))
  (! (=> (and (<= 0 i) (< i (vec_length w)))
         (= (vec_get w i) (select (vec_to_array w) i)))
     :pattern ((vec_get w i)))))
(assert (forall ((w Vec) (i Int) (x Value))
  (! (=> (and (<= 0 i) (< i (vec_length w)))
         (= (vec_set w i x)
            (vec_of_array (store (vec_to_array w) i x) (vec_length w))))
     :pattern ((vec_set w i x)))))
(assert (forall ((n Int) (x Value))
  (! (=> (<= 0 n)
         (= (vec_make n x) (vec_of_array ((as const (Array Int Value)) x) n)))
     :pattern ((vec_make n x)))))
"

/-- `x'` is not a simple SMT-LIB symbol, so it prints as `|x'|`. A simple symbol
prints unchanged. -/
def symbolToSMTLIB (name : String) : String :=
  let simple (c : Char) := c.isAlphanum || "~!@$%^&*_-+=<>.?/".contains c
  if name.all simple then name else s!"|{name}|"

def RoundingMode.toSMTLIB : RoundingMode → String
  | .nearestTiesToEven => "roundNearestTiesToEven"

def Srt.toSMTLIB : Srt → String
  | .int     => "Int"
  | .bool    => "Bool"
  | .bv width => s!"(_ BitVec {width})"
  | .char    => "(_ BitVec 8)"
  | .string  => "(Seq (_ BitVec 8))"
  | .float   => "(_ FloatingPoint 11 53)"
  | .value   => "Value"
  | .vallist => "ValueList"
  | .vec     => "Vec"

def UnOp.toSMTLIB : UnOp τ₁ τ₂ → String
  | .ofInt   => "of_int"
  | .ofBool  => "of_bool"
  | .ofInt32 => "of_int32"
  | .ofInt64 => "of_int64"
  | .ofChar => "of_char"
  | .ofString => "of_string"
  | .ofFloat => "of_float"
  | .toInt   => "to_int"
  | .toBool  => "to_bool"
  | .toInt32 => "to_int32"
  | .toInt64 => "to_int64"
  | .toChar => "to_char"
  | .toString => "to_string"
  | .toFloat => "to_float"
  | .charToInt => "bv2nat"
  | .intToChar => "(_ int2bv 8)"
  | .intToBv width => s!"(_ int2bv {width})"
  | .bvToNat _ => "bv2nat"
  | .bvNeg _ => "bvneg"
  | .bvNot _ => "bvnot"
  | .bvSignExtend width result _ => s!"(_ sign_extend {result - width})"
  | .bvExtractLsb _ result _ => s!"(_ extract {result - 1} 0)"
  | .seqLen => "seq.len"
  | .fpAbs => "fp.abs"
  | .fpNeg => "fp.neg"
  | .fpSqrt => s!"fp.sqrt {RoundingMode.nearestTiesToEven.toSMTLIB}"
  | .fpIsNaN => "fp.isNaN"
  | .fpIsInfinite => "fp.isInfinite"
  | .fpIsNegative => "fp.isNegative"
  | .fpOfInt => s!"(_ to_fp 11 53) {RoundingMode.nearestTiesToEven.toSMTLIB}"
  | .neg     => "-"
  | .not     => "not"
  | .ofValList => "of_tuple"
  | .toValList => "to_tuple"
  | .arrayLen => "array_length"
  | .vhead   => "vhd"
  | .vtail   => "vtl"
  | .visnil  => "is-vnil"
  | .ofInj tag arity => s!"of_inj {tag} {arity}"
  | .tagOf   => "tag_of"
  | .arityOf => "arity_of"
  | .payloadOf => "payload_of"
  | .vecLen  => "vec_length"
  | .ofVec   => "of_vec"
  | .toVec   => "to_vec"
  | .uninterpreted name _ _ => symbolToSMTLIB name

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
  | .bvAdd _ => "bvadd"
  | .bvSub _ => "bvsub"
  | .bvMul _ => "bvmul"
  | .bvSDiv _ => "bvsdiv"
  | .bvUDiv _ => "bvudiv"
  | .bvSRem _ => "bvsrem"
  | .bvURem _ => "bvurem"
  | .bvAnd _ => "bvand"
  | .bvOr _ => "bvor"
  | .bvXor _ => "bvxor"
  | .bvSLt _ => "bvslt"
  | .bvULt _ => "bvult"
  | .bvShl _ => "bvshl"
  | .bvAShr _ => "bvashr"
  | .bvLShr _ => "bvlshr"
  | .seqConcat => "seq.++"
  | .seqNth => "seq.nth"
  | .seqPrefixOf => "seq.prefixof"
  | .seqSuffixOf => "seq.suffixof"
  | .fpAdd => s!"fp.add {RoundingMode.nearestTiesToEven.toSMTLIB}"
  | .fpSub => s!"fp.sub {RoundingMode.nearestTiesToEven.toSMTLIB}"
  | .fpMul => s!"fp.mul {RoundingMode.nearestTiesToEven.toSMTLIB}"
  | .fpDiv => s!"fp.div {RoundingMode.nearestTiesToEven.toSMTLIB}"
  | .fpEq  => "fp.eq"
  | .fpLt  => "fp.lt"
  | .fpLe  => "fp.leq"
  | .vcons => "vcons"
  | .vecGet  => "vec_get"
  | .vecMake => "vec_make"
  | .uninterpreted name _ _ _ => symbolToSMTLIB name

def TerOp.toSMTLIB : TerOp τ₁ τ₂ τ₃ τ₄ → String
  | .seqExtract => "seq.extract"
  | .vecSet => "vec_set"
  | .uninterpreted name _ _ _ _ => symbolToSMTLIB name

def UnPred.toSMTLIB : UnPred τ → String
  | .isInt   => "is-of_int"
  | .isBool  => "is-of_bool"
  | .isInt32 => "is-of_int32"
  | .isInt64 => "is-of_int64"
  | .isChar  => "is-of_char"
  | .isStr   => "is-of_string"
  | .isFloat => "is-of_float"
  | .isLoc   => "is-of_loc"
  | .isTuple => "is-of_tuple"
  | .isOfInj => "is-of_inj"
  | .isVec   => "is-of_vec"
  | .uninterpreted name _ => symbolToSMTLIB name

def BinPred.toSMTLIB : BinPred τ₁ τ₂ → String
  | .lt => "<"
  | .le => "<="
  | .uninterpreted name _ _ => symbolToSMTLIB name

private def byteToSMTLIB (b : UInt8) : String :=
  s!"(seq.unit #x{byteHex b})"

private def stringConstToSMTLIB : List UInt8 → String
  | [] => "(as seq.empty (Seq (_ BitVec 8)))"
  | s => s!"(seq.++ {" ".intercalate (s.map byteToSMTLIB)})"

def Term.toSMTLIB : Term τ → String
  | .var _ name   => symbolToSMTLIB name
  | .const (.i n)   => if n ≥ 0 then s!"{n}" else s!"(- {-n})"
  | .const (.b b)   => if b then "true" else "false"
  | .const (.bv (width := width) bits) => s!"(_ bv{bits.toNat} {width})"
  | .const (.char c) => s!"#x{byteHex c}"
  | .const (.str s) => stringConstToSMTLIB s
  | .const (.fp bits) => s!"((_ to_fp 11 53) #x{uint64Hex bits})"
  | .const .fpNaN    => "(_ NaN 11 53)"
  | .const .fpPosInf => "(_ +oo 11 53)"
  | .const .fpNegInf => "(_ -oo 11 53)"
  | .const .unit    => "(of_other unit_val)"
  | .const .vnil    => "vnil"
  | .const (.uninterpreted name _) => symbolToSMTLIB name
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
    s!"(forall (({symbolToSMTLIB x} {τ.toSMTLIB})) {body})"
  | .exists_ x τ φ  => s!"(exists (({symbolToSMTLIB x} {τ.toSMTLIB})) {φ.toSMTLIB})"
