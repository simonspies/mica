(* TEST: no-compile *)
open Mica

(* A signature variable is the caller's choice, so the body may not narrow it
   to [int]. This is the difference from OCaml, where the annotation is only a
   hint and this declaration types as [int -> int]. *)
let f (x : 'a) : 'a = x + 1
