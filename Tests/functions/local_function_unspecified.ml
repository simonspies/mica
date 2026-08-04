open Mica

(* A function literal in an expression position is verified against its own
   specification. An unspecified one is rejected: an unspecified function type
   is logically uninhabited, so nothing could be concluded about the value. *)

let use (n : int) : int =
  let f = fun x -> x + 1 in
  n
[@@spec fun n ->
  ret (fun v -> assert (v = n))]
