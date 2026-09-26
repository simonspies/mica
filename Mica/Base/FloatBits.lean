-- SUMMARY: IEEE binary64 operations on the bit patterns of floats.

/-! ## Core IEEE binary64 operations

Each float operation decodes its operands with `Float.ofBits`, computes with
Lean's `Float`, and (for float-valued results) re-encodes with `Float.toBits`.
The arithmetic ops use the rounding mode round-nearest-ties-to-even, matching
the `roundNearestTiesToEven` printed for the Z3 ops. -/
namespace FloatBits

def add (a b : UInt64) : UInt64 := (Float.ofBits a + Float.ofBits b).toBits
def sub (a b : UInt64) : UInt64 := (Float.ofBits a - Float.ofBits b).toBits
def mul (a b : UInt64) : UInt64 := (Float.ofBits a * Float.ofBits b).toBits
def div (a b : UInt64) : UInt64 := (Float.ofBits a / Float.ofBits b).toBits
def abs (a : UInt64) : UInt64 := (Float.ofBits a).abs.toBits
def neg (a : UInt64) : UInt64 := (-(Float.ofBits a)).toBits
def sqrt (a : UInt64) : UInt64 := (Float.ofBits a).sqrt.toBits

def isNaN (a : UInt64) : Bool := (Float.ofBits a).isNaN
def isInf (a : UInt64) : Bool := (Float.ofBits a).isInf
def ofInt (n : Int) : UInt64 := (Float.ofInt n).toBits
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
