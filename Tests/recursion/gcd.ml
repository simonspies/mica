(* TEST: roundtrip *)
open Mica

let rec gcd (a: int) (b: int) : int =
  if b = 0 then a
  else gcd b (a mod b)
[@@spec fun x y ->
  assert (y >= 0);
  assert (x >= 0);
  ret (fun v ->
    assert (v >= 0);
    assert (v <= x + y))]
;;
let _ = assert (gcd 12 8 >= 0)