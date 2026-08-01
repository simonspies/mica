(* TEST: no-compile *)

open Mica

(* The annotation is checked: the bound expression has to have that type. *)
let f (n : int) : int =
  let b : bool = n in
  0
[@@spec fun n -> ret (fun r -> assert (r = 0))]
