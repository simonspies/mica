(* TEST: no-compile *)
open Mica

let bad x : int = x
[@@spec fun x -> ret (fun r -> assert (r = x))]
