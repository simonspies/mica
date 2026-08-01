(* TEST: no-compile *)

open Mica

(* The same for a local `let`. *)
let f (n : int) : int =
  let (bump : bool) (x : int) : int = x + 1 in
  bump n
[@@spec fun n -> ret (fun r -> assert (r = n + 1))]
