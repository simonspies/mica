(* TEST: no-compile *)
open Mica

let rec loop (n : int) (k : int) : int = loop n k
[@@fn] [@@decreases n];;
