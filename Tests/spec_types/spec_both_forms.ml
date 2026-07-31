open Mica

(* A declaration is specified once: either through [@@spec] or through the
   specification on its own type, not both. *)
let f : (int -> int) [@spec fun x -> ret (fun r -> assert (r > x))] =
  fun x -> x + 1
[@@spec fun x -> ret (fun r -> assert (r >= x))]
