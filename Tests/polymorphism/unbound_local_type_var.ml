(* TEST: no-compile *)
open Mica

(* Only a signature binds a type variable, so ['b] here stands for nothing.
   OCaml would make it an inference variable shared across the declaration and
   solve it; mica rejects it, so that writing ['a] always means the same
   thing. *)
let f (x : 'a) : 'a =
  let g (y : 'b) = y in
  x
