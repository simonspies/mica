(* TEST: no-compile *)
open Mica

(* Nothing proves that `o` is `Some`, so the ghost call of `Option.value`
   fails. *)
let get (o : int option) : int =
  let%ghost _ = Option.value o in
  0
[@@spec fun o -> ret (fun r -> assert true)]
