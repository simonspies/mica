(* TEST: no-compile *)
open Mica

let bad (x : int option) : int =
  match x with
  | None -> 0
  | Some _ -> ()
