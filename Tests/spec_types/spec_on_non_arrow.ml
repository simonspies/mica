open Mica

(* A specification describes a function. On any other type it has no meaning
   and is rejected. *)
let f (x : int [@spec fun y -> ret (fun r -> assert (r > y))]) : int = x
