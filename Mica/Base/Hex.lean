-- SUMMARY: Upper-case hexadecimal digits of bytes and 64-bit words.

def hexDigit (n : Nat) : Char :=
  match n with
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3'
  | 4 => '4' | 5 => '5' | 6 => '6' | 7 => '7'
  | 8 => '8' | 9 => '9' | 10 => 'A' | 11 => 'B'
  | 12 => 'C' | 13 => 'D' | 14 => 'E' | _ => 'F'

def byteHex (b : UInt8) : String :=
  let n := b.toNat
  String.ofList [hexDigit (n / 16), hexDigit (n % 16)]

/-- The 16 big-endian hex digits of a `UInt64`, for an `#x…` bitvector literal. -/
def uint64Hex (b : UInt64) : String :=
  let n := b.toNat
  String.ofList ((List.range 16).reverse.map (fun i => hexDigit ((n / (16 ^ i)) % 16)))
