(* TEST: no-compile *)

open Mica

(* An attribute error points at the attribute: [@@spec] without a payload is
   reported where it is written, not at the start of the file. *)
let f (n : int) : int = n
[@@spec]
