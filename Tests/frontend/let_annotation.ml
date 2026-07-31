(* TEST: roundtrip *)

open Mica

(* A `let` annotation is the bound value's own type when the let takes no
   arguments. It means the same written on the pattern itself. *)

let no_args (n : int) : int =
  let b : int = n + 1 in
  b
[@@spec fun n -> ret (fun r -> assert (r = n + 1))]

let on_pattern (n : int) : int =
  let (b : int) = n + 1 in
  b
[@@spec fun n -> ret (fun r -> assert (r = n + 1))]
