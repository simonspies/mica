(* TEST: roundtrip *)
open Mica

(* A ghost call of a primitive must prove the precondition of the primitive.
   In the `Some` branch the match gives it. *)
let get (o : int option) : int =
  match o with
  | None -> 0
  | Some x ->
    let%ghost v = Option.value o in
    let%ghost _ = assert (v = x) in
    x
[@@spec fun o -> ret (fun r -> assert true)]
