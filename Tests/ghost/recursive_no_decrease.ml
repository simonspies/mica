(* TEST: no-compile *)
open Mica

(* The measure must go down at the call. Here it goes up. *)

let rec ge_zero (n : int) : int =
  if n <= 0 then 0 else ge_zero (n + 1)
[@@ghost]
[@@spec fun x ->
  assert (0 <= x);
  ret (fun r -> assert (0 <= r))]
[@@decreases x]
