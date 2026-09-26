-- SUMMARY: IEEE binary64 operations on the bit patterns of floats.

/-! ## Core IEEE binary64 operations

Each float operation decodes its operands with `Float.ofBits`, computes with
Lean's `Float`, and (for float-valued results) re-encodes with `Float.toBits`. -/

/-- The rounding mode of an operation whose exact result is not a float. Lean's
`Float` rounds to nearest with ties to even and has no other mode, so
`RoundingMode` has only one constructor. -/
inductive RoundingMode where
  | nearestTiesToEven

namespace FloatBits

def add (_ : RoundingMode) (a b : UInt64) : UInt64 := (Float.ofBits a + Float.ofBits b).toBits
def sub (_ : RoundingMode) (a b : UInt64) : UInt64 := (Float.ofBits a - Float.ofBits b).toBits
def mul (_ : RoundingMode) (a b : UInt64) : UInt64 := (Float.ofBits a * Float.ofBits b).toBits
def div (_ : RoundingMode) (a b : UInt64) : UInt64 := (Float.ofBits a / Float.ofBits b).toBits
def abs (a : UInt64) : UInt64 := (Float.ofBits a).abs.toBits
def neg (a : UInt64) : UInt64 := (-(Float.ofBits a)).toBits
def sqrt (_ : RoundingMode) (a : UInt64) : UInt64 := (Float.ofBits a).sqrt.toBits

def isNaN (a : UInt64) : Bool := (Float.ofBits a).isNaN
def isInf (a : UInt64) : Bool := (Float.ofBits a).isInf
def ofInt (_ : RoundingMode) (n : Int) : UInt64 := (Float.ofInt n).toBits
def eq (a b : UInt64) : Bool := Float.ofBits a == Float.ofBits b
def lt (a b : UInt64) : Bool := decide (Float.ofBits a < Float.ofBits b)
def le (a b : UInt64) : Bool := decide (Float.ofBits a ≤ Float.ofBits b)

/-- Sign-bit test, corresponding to SMT-LIB `fp.isNegative`: for a non-NaN value
    this is bit 63; NaN is reported `false`, matching Z3. -/
def isNegative (a : UInt64) : Bool := !isNaN a && (a >>> 63 == 1)

def nan : UInt64 := 0x7FF8000000000000
def posInf : UInt64 := 0x7FF0000000000000
def negInf : UInt64 := 0xFFF0000000000000

end FloatBits
