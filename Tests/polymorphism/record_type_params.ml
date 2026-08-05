(* TEST: no-compile *)
open Mica

(* A record type is registered at arity zero, so a parameter would go nowhere
   and every use of the name would fail on its arity instead. Rejected at the
   declaration, where the mistake is. *)
type 'a t = { f : 'a }

let g (n : int) : int = n
