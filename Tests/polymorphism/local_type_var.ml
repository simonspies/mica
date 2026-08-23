open Mica

(* A local annotation may name the declaration's own type variables: the
   signature binds them for the whole body. *)
let pair_up (x : 'a) : 'a * 'a =
  let g (y : 'a * 'a) = y in
  g (x, x)

(* A local whose type the program does not spell out is left to inference —
   that, not a type variable, is what to write when the type is uninteresting. *)
let twice (n : int) : int =
  let g y = y in
  let (a, b) = g (n, n) in
  a + b
