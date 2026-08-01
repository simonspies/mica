(* TEST: no-compile *)

open Mica

(* When the let takes arguments the annotation is the function's return type,
   and the body is checked against it. *)
let f (n : int) : int =
  let bump (x : int) : bool = x + 1 in
  n
[@@spec fun n -> ret (fun r -> assert (r = n))]
