(* TEST: no-compile *)
open Mica

(* A data declaration has no body for inference to solve a variable from, so a
   payload may name only the declaration's own parameters. *)
type 'a t = A of 'b

let f (n : int) : int = n
