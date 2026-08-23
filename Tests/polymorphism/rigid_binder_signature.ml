(* TEST: no-compile *)
open Mica

(* The declaration's own binder is a binding site too, so ['a] written there is
   as rigid as one written on the function's arguments. *)
let f : ('a -> 'a) = fun x -> x + 1
