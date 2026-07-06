open Mica

(* Functions that use tuples as arguments or return values. *)

(* 1. Swap a pair: returns (b, a) given (a, b) as ints *)
let swap_pair ((a : int), (b : int)) : int * int =
  (b, a)
[@@spec fun ((a : int), (b : int)) ->
  ret (fun ((c : int), (d : int)) ->
    assert (a = d);
    assert (b = c))];;

let sum_pair_pattern ((x : int), (y : int)) : int =
  x + y
[@@spec fun ((x : int), (y : int)) ->
  ret (fun v ->
    assert (v = x + y))];;
