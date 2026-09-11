(* TEST: roundtrip *)
open Mica

let int32_neg_involutive (x : int32) : int32 =
  Int32.neg (Int32.neg x)
[@@spec fun x -> ret (fun result -> assert (Int32.equal result x))]

let int32_add_inverse (x : int32) : int32 =
  Int32.add x (Int32.neg x)
[@@spec fun x -> ret (fun result -> assert (Int32.equal result Int32.zero))]

let int32_add_commutative (x : int32) (y : int32) : int32 =
  Int32.add x y
[@@spec fun x y ->
  ret (fun result -> assert (Int32.equal result (Int32.add y x)))]

let int32_sub_self (x : int32) : int32 =
  Int32.sub x x
[@@spec fun x -> ret (fun result -> assert (Int32.equal result Int32.zero))]

let int32_mul_commutative (x : int32) (y : int32) : int32 =
  Int32.mul x y
[@@spec fun x y ->
  ret (fun result -> assert (Int32.equal result (Int32.mul y x)))]

let int32_div_self (x : int32) : int32 =
  Int32.div x x
[@@spec fun x ->
  assert (not (Int32.equal x Int32.zero));
  ret (fun result -> assert (Int32.equal result Int32.one))]

let int32_unsigned_div_self (x : int32) : int32 =
  Int32.unsigned_div x x
[@@spec fun x ->
  assert (not (Int32.equal x Int32.zero));
  ret (fun result -> assert (Int32.equal result Int32.one))]

let int32_rem_self (x : int32) : int32 =
  Int32.rem x x
[@@spec fun x ->
  assert (not (Int32.equal x Int32.zero));
  ret (fun result -> assert (Int32.equal result Int32.zero))]

let int32_unsigned_rem_self (x : int32) : int32 =
  Int32.unsigned_rem x x
[@@spec fun x ->
  assert (not (Int32.equal x Int32.zero));
  ret (fun result -> assert (Int32.equal result Int32.zero))]

let int32_lognot_involutive (x : int32) : int32 =
  Int32.lognot (Int32.lognot x)
[@@spec fun x -> ret (fun result -> assert (Int32.equal result x))]

let int32_logand_self (x : int32) : int32 =
  Int32.logand x x
[@@spec fun x -> ret (fun result -> assert (Int32.equal result x))]

let int32_logor_zero (x : int32) : int32 =
  Int32.logor x Int32.zero
[@@spec fun x -> ret (fun result -> assert (Int32.equal result x))]

let int32_logxor_self (x : int32) : int32 =
  Int32.logxor x x
[@@spec fun x -> ret (fun result -> assert (Int32.equal result Int32.zero))]

let int32_min_commutative (x : int32) (y : int32) : int32 =
  Int32.min x y
[@@spec fun x y ->
  ret (fun result -> assert (Int32.equal result (Int32.min y x)))]

let int32_max_commutative (x : int32) (y : int32) : int32 =
  Int32.max x y
[@@spec fun x y ->
  ret (fun result -> assert (Int32.equal result (Int32.max y x)))]

let int32_compare_reflexive (x : int32) : int =
  Int32.compare x x
[@@spec fun x -> ret (fun result -> assert (result = 0))]

let int32_unsigned_compare_reflexive (x : int32) : int =
  Int32.unsigned_compare x x
[@@spec fun x -> ret (fun result -> assert (result = 0))]

let int32_equal_reflexive (x : int32) : bool =
  Int32.equal x x
[@@spec fun x -> ret (fun result -> assert result)]

let int32_shift_left_zero (x : int32) : int32 =
  Int32.shift_left x 0
[@@spec fun x -> ret (fun result -> assert (Int32.equal result x))]

let int32_shift_right_zero (x : int32) : int32 =
  Int32.shift_right x 0
[@@spec fun x -> ret (fun result -> assert (Int32.equal result x))]

let int32_shift_right_logical_zero (x : int32) : int32 =
  Int32.shift_right_logical x 0
[@@spec fun x -> ret (fun result -> assert (Int32.equal result x))]

let int64_neg_involutive (x : int64) : int64 =
  Int64.neg (Int64.neg x)
[@@spec fun x -> ret (fun result -> assert (Int64.equal result x))]

let int64_add_inverse (x : int64) : int64 =
  Int64.add x (Int64.neg x)
[@@spec fun x -> ret (fun result -> assert (Int64.equal result Int64.zero))]

let int64_add_commutative (x : int64) (y : int64) : int64 =
  Int64.add x y
[@@spec fun x y ->
  ret (fun result -> assert (Int64.equal result (Int64.add y x)))]

let int64_sub_self (x : int64) : int64 =
  Int64.sub x x
[@@spec fun x -> ret (fun result -> assert (Int64.equal result Int64.zero))]

let int64_mul_commutative (x : int64) (y : int64) : int64 =
  Int64.mul x y
[@@spec fun x y ->
  ret (fun result -> assert (Int64.equal result (Int64.mul y x)))]

let int64_div_self (x : int64) : int64 =
  Int64.div x x
[@@spec fun x ->
  assert (not (Int64.equal x Int64.zero));
  ret (fun result -> assert (Int64.equal result Int64.one))]

let int64_unsigned_div_self (x : int64) : int64 =
  Int64.unsigned_div x x
[@@spec fun x ->
  assert (not (Int64.equal x Int64.zero));
  ret (fun result -> assert (Int64.equal result Int64.one))]

let int64_rem_self (x : int64) : int64 =
  Int64.rem x x
[@@spec fun x ->
  assert (not (Int64.equal x Int64.zero));
  ret (fun result -> assert (Int64.equal result Int64.zero))]

let int64_unsigned_rem_self (x : int64) : int64 =
  Int64.unsigned_rem x x
[@@spec fun x ->
  assert (not (Int64.equal x Int64.zero));
  ret (fun result -> assert (Int64.equal result Int64.zero))]

let int64_lognot_involutive (x : int64) : int64 =
  Int64.lognot (Int64.lognot x)
[@@spec fun x -> ret (fun result -> assert (Int64.equal result x))]

let int64_logand_self (x : int64) : int64 =
  Int64.logand x x
[@@spec fun x -> ret (fun result -> assert (Int64.equal result x))]

let int64_logor_zero (x : int64) : int64 =
  Int64.logor x Int64.zero
[@@spec fun x -> ret (fun result -> assert (Int64.equal result x))]

let int64_logxor_self (x : int64) : int64 =
  Int64.logxor x x
[@@spec fun x -> ret (fun result -> assert (Int64.equal result Int64.zero))]

let int64_min_commutative (x : int64) (y : int64) : int64 =
  Int64.min x y
[@@spec fun x y ->
  ret (fun result -> assert (Int64.equal result (Int64.min y x)))]

let int64_max_commutative (x : int64) (y : int64) : int64 =
  Int64.max x y
[@@spec fun x y ->
  ret (fun result -> assert (Int64.equal result (Int64.max y x)))]

let int64_compare_reflexive (x : int64) : int =
  Int64.compare x x
[@@spec fun x -> ret (fun result -> assert (result = 0))]

let int64_unsigned_compare_reflexive (x : int64) : int =
  Int64.unsigned_compare x x
[@@spec fun x -> ret (fun result -> assert (result = 0))]

let int64_equal_reflexive (x : int64) : bool =
  Int64.equal x x
[@@spec fun x -> ret (fun result -> assert result)]

let int64_shift_left_zero (x : int64) : int64 =
  Int64.shift_left x 0
[@@spec fun x -> ret (fun result -> assert (Int64.equal result x))]

let int64_shift_right_zero (x : int64) : int64 =
  Int64.shift_right x 0
[@@spec fun x -> ret (fun result -> assert (Int64.equal result x))]

let int64_shift_right_logical_zero (x : int64) : int64 =
  Int64.shift_right_logical x 0
[@@spec fun x -> ret (fun result -> assert (Int64.equal result x))]

let widening_roundtrip (x : int32) : int32 =
  Int64.to_int32 (Int64.of_int32 x)
[@@spec fun x -> ret (fun result -> assert (Int32.equal result x))]

let widening_add_low_bits (x : int32) (y : int32) : int32 =
  Int64.to_int32 (Int64.add (Int64.of_int32 x) (Int64.of_int32 y))
[@@spec fun x y ->
  ret (fun result -> assert (Int32.equal result (Int32.add x y)))]
