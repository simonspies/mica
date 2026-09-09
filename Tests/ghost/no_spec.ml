(* TEST: no-compile *)
open Mica

let bump (x : int) : int = x + 1
[@@ghost (hi : int)]
