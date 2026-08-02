(* TEST: no-compile *)
open Mica

(* `with` commits to at least one arm, so a match with none is reported here
   rather than parsed into an empty match and caught two stages later. *)
let f x = match x with
