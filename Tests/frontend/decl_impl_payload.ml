(* TEST: no-compile *)

open Mica

(* [@@impl] derives its specification from [@@fn], so there is nothing to
   write after it. *)
let f (n : int) : int = n
[@@fn]
[@@impl 3]
