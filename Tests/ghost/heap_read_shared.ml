(* TEST: no-compile *)
open Mica

(* A shared array has no points-to assertion, so ghost code cannot read it. *)
let first (a : int array) : int =
  let%ghost x = a.(0) in
  0
[@@spec fun a ->
  assert (0 < Array.length a);
  ret (fun r -> assert (r = 0))]
