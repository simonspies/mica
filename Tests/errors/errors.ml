open Mica

let checked_pos (n : int) : int =
  if n > 0 then n else failwith "expected a positive number"
[@@spec fun n ->
  assert (n > 0);
  ret (fun v ->
    assert (v = n))];;

let checked_sub (a : int) (b : int) : int =
  if a < b then invalid_arg "underflow" else a - b
[@@spec fun a b ->
  assert (b <= a);
  ret (fun v ->
    assert (v = a - b))];;

let _ = assert (checked_pos 5 = 5)

let _ = assert (checked_sub 7 2 = 5)
