(* TEST: roundtrip *)
open Mica

(* A ghost bound the caller supplies. `hi` has no run-time footprint: it exists
   only so the specification can talk about the range the result stays in. *)
let bump (x : int) : int = x + 1
[@@spec fun x ->
  assert (x < hi);
  ret (fun v ->
    assert (v <= hi))]
[@@ghost (hi : int)]
;;

let use_literal (n : int) : int =
  if n < 100 then (bump n [@ghost 100]) else n
[@@spec fun n ->
  ret (fun v ->
    assert (v <= 100 || v = n))]
;;

(* A ghost argument may be any specification-level expression over the names in
   scope, run-time arguments included. *)
let use_expression (n : int) (k : int) : int =
  if n < k then (bump n [@ghost (k + 1)]) else n
[@@spec fun n k ->
  ret (fun v ->
    assert (v <= k + 1 || v = n))]
;;

(* A ghost parameter is in scope in the body, so it can be passed on. *)
let bump_twice (x : int) : int = (bump (bump x [@ghost bound - 1]) [@ghost bound])
[@@spec fun x ->
  assert (x + 1 < bound);
  ret (fun v ->
    assert (v <= bound))]
[@@ghost (bound : int)]
;;

let _ = assert (use_literal 3 <= 100)
