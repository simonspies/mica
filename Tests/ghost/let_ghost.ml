(* TEST: roundtrip *)
open Mica

(* A ghost binding is deleted before the program is compiled, so nothing that
   runs may read `m`. Ghost code that follows it may. *)
let use (x : int) : int =
  let%ghost m = x + 1 in
  let%ghost _k = (assert (m = x + 1); m + 1) in
  x + 1
[@@spec fun x -> ret (fun v -> assert (v = x + 1))]
