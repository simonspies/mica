open Mica

(* A polymorphic spec-level function. At the FOL level a type variable is just
   `Value`: the encoding has one sort for values and derives no constraint from
   ['a], so [label] becomes a single symbol every instantiation shares. Its
   argument reaches the result, so destructuring the pair in a postcondition
   gets the number back out. *)
let label ((x : 'a), (n : int)) : 'a * int = (x, n + 1)
[@@fn];;

let bump_int (n : int) : int = n + 1
[@@spec fun n -> ret (fun v -> let (_, k) = label (n, n) in assert (v = k))];;

let bump_bool (b : bool) : int = 1
[@@spec fun b -> ret (fun v -> let (_, k) = label (b, 0) in assert (v = k))];;

let bump_pair (n : int) : int = n + 1
[@@spec fun n -> ret (fun v -> let (_, k) = label ((n, n), n) in assert (v = k))];;
