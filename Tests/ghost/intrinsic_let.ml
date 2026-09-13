(* TEST: roundtrip *)
open Mica

(* Ghost code may call a primitive: its result is the term the specification of
   the primitive gives. *)
let clamp (x : int) : int =
  let%ghost m = Int.max x 0 in
  let%ghost _ = assert (0 <= m && x <= m) in
  if x < 0 then 0 else x
[@@spec fun x -> ret (fun v -> assert (0 <= v))]
