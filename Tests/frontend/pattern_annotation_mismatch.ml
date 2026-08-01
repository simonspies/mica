(* TEST: no-compile *)

open Mica

(* A pattern annotation is checked, like the annotation written after the
   binder: the bound expression has to have that type. *)
let f (n : int) : int =
  let (b : bool) = n in
  0
[@@spec fun n -> ret (fun r -> assert (r = 0))]
