(* TEST: no-compile *)
open Mica

(* A record declaration binds no type variables, so a field type may name none.
   Rejected at the declaration, like a sum declaration's payload. *)
type t = { f : 'b }

let g (n : int) : int = n
