(* TEST: no-compile *)

open Mica

(* The same for [@@fn]. *)
let f (n : int) : int = n
[@@fn]
[@@fn]
