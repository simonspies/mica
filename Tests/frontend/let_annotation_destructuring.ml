open Mica

(* A destructuring let has no single binder to carry the annotation, so it is
   rejected rather than silently dropped. *)
let f (n : int) : int =
  let (a, b) : int * int = (n, n) in
  a + b
[@@spec fun n -> ret (fun r -> assert (r = n + n))]
