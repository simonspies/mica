(* TEST: no-compile *)
open Mica

(* Logic.eq is for specifications only. Its precondition is False. Therefore
   the verifier rejects each call to it from the body of a function. *)
let bad (m1 : (int * int) list) (m2 : (int * int) list) : bool =
  Logic.eq m1 m2
[@@spec fun m1 m2 -> ret (fun r -> assert true)];;
