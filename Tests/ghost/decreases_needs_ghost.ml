(* TEST: no-compile *)
open Mica

let rec countdown (n : int) : int = if n <= 0 then 0 else countdown (n - 1)
[@@spec fun n -> ret (fun v -> assert (v = 0))]
[@@decreases n]
