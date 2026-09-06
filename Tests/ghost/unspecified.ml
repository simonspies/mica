(* TEST: no-compile *)
open Mica

let plain (x : int) : int = x + 1
;;

let use (n : int) : int = (plain n [@ghost 100])
[@@spec fun n -> ret (fun v -> assert (v = n + 1))]
