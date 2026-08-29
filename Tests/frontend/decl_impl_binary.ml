(* TEST: no-compile *)

open Mica

(* A spec-level function compiles to a solver symbol of one argument. Several
   are written as a tuple. *)
let f (n : int) (m : int) : int = n + m
[@@fn]
[@@impl]
