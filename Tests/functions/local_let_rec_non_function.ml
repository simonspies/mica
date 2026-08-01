(* TEST: no-compile *)

open Mica

(* A `let rec` with no arguments has to bind a function literal; there is
   nothing for the self-reference to mean otherwise. *)
let f (n : int) : int =
  let rec x = 3 in
  x
[@@spec fun n -> ret (fun r -> assert (r = 3))]
