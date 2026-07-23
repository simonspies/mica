(* TEST: no-compile *)

open Mica

let add (x : int) (y : int) : int = x + y

(* TinyML applications are n-ary; the runtime has no partial application. *)
let add_one = add 1
