(* TEST: no-compile *)

open Mica

(* Every declaration attribute is accounted for: an unknown name is rejected
   rather than silently ignored. *)
let f (n : int) : int = n
[@@bogus]
