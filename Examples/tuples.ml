open Mica

(* Functions that use tuples as arguments or return values. *)

(* 1. Swap a pair: returns (b, a) given (a, b) as ints *)
let swap_pair (p: int * int) : int * int =
  let a = p.1 in
  let b = p.2 in
  (b, a)
[@@spec fun p ->
  ret (fun v ->
    assert (p.1 = v.2);
    assert (p.2 = v.1))];;