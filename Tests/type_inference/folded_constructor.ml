(* TEST: no-compile *)
open Mica

(* A list literal comes out as `int list` however many constructor
   applications built it, not as one nested sum per element. *)

let use (n : int) : bool =
  let xs = [n; n + 1; n + 2] in
  xs
