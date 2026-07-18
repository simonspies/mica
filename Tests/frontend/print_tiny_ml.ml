(* TEST: --print-tiny-ml --no-check *)
open Mica

(* Pins the TinyML rendering of the elaborated program. *)
let abs_ (x: int) : int = if x < 0 then 0 - x else x
[@@spec fun x ->
  ret (fun v ->
    if x >= 0 then assert (v = x)
    else assert (v = -x))];;
