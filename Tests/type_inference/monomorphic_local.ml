(* TEST: no-compile *)
open Mica

let bad : int =
  let xs = [] in
  let ys : int list = 1 :: xs in
  let zs : bool list = true :: xs in
  0
