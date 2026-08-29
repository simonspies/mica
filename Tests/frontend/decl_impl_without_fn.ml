(* TEST: no-compile *)

open Mica

(* [@@impl] states that the body implements the spec-level function [@@fn]
   derives, so it says nothing on its own. *)
let f (n : int) : int = n
[@@impl]
