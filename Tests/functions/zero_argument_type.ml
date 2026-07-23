(* TEST: no-compile *)

open Mica

(* The frontend rejects zero-argument function expressions. *)
let zero = fun : int -> 0
