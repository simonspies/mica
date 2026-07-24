(* TEST: no-compile *)
open Mica

(* Logic.eq is spec-only: its precondition is False, so any attempt to call it
   from a runtime body is rejected. *)
let bad (m1 : (int * int) list) (m2 : (int * int) list) : bool =
  Logic.eq m1 m2
[@@spec fun m1 m2 -> ret (fun r -> assert true)];;
