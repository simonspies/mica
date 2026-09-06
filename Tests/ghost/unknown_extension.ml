(* TEST: no-compile *)
open Mica

let use (x : int) : int =
  let%magic m = x + 1 in
  m
