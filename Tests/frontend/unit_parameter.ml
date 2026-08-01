(* TEST: no-compile *)

open Mica

(* KNOWN GAP (#156): `()` is not accepted in a binder position — not as a parameter
   (`let f () = e`, `fun () -> e`) and not as a `let` pattern (`let () = e`).
   This file pins that behaviour.

   The fix is to elaborate `()` as an empty product, which needs unit support
   in `letProd`: the typing rule, the operational semantics, the weakest
   precondition, and the verifier all key on a tuple value today. *)
let f () : int = 3
[@@spec fun u -> ret (fun r -> assert (r = 3))]
