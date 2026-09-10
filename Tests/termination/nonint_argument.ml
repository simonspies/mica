open Mica

(* The measure is an integer; the argument it ranks need not be. *)
let rec settle (b : bool) : int =
  if b then 0 else settle true
[@@fn] [@@decreases if b then 0 else 1];;
