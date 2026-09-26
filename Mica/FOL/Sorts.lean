-- SUMMARY: Sorts of the first-order logic and the Lean type each one denotes.
import Mica.TinyML.RuntimeExpr

-- ---------------------------------------------------------------------------
-- Sorts
-- ---------------------------------------------------------------------------

inductive Srt where
  | int
  | bool
  | bv (width : Nat)
  | char
  | string
  | float
  | value
  | vallist
  | vec
  deriving DecidableEq, Repr

@[reducible] def Srt.denote : Srt → Type
  | .int => Int
  | .bool => Bool
  | .bv width => BitVec width
  | .char => UInt8
  | .string => List UInt8
  | .float => UInt64
  | .value => Runtime.Val
  | .vallist => List Runtime.Val
  | .vec => List Runtime.Val

instance : DecidableEq (Srt.denote τ) := by
  cases τ <;> simp [Srt.denote] <;> infer_instance

instance : Inhabited (Srt.denote τ) := by
  cases τ <;> simp [Srt.denote] <;> infer_instance
