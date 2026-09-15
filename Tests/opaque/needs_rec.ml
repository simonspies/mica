(* TEST: no-compile *)
open Mica

let double (n : int) : int = n + n
[@@fn] [@@opaque]
