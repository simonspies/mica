(* TEST: no-compile *)

open Mica

(* The same for [@@impl]. *)
let f (n : int) : int = n
[@@fn]
[@@impl]
[@@impl]
