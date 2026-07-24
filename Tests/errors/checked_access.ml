open Mica

(* Guarded error paths.

   [failwith] and [invalid_arg] have precondition [False]: a call verifies
   only in a contradictory context.  Each function below guards its raise
   with a check that the spec's precondition rules out, so the verifier
   proves every raise dead while the compiled code keeps its runtime
   protection. *)

(* First element, guarded against the empty vector. *)
let first (v : int vec) : int =
  if Vec.length v = 0 then failwith "empty vector"
  else Vec.get v 0
[@@spec fun v ->
  assert (Vec.length v > 0);
  ret (fun r -> assert (r = Vec.get v 0))];;

(* Bounds-checked access with distinct error messages per failure mode. *)
let checked_get (v : int vec) (i : int) : int =
  if i < 0 then invalid_arg "negative index"
  else if i >= Vec.length v then invalid_arg "index past the end"
  else Vec.get v i
[@@spec fun v i ->
  assert (0 <= i && i < Vec.length v);
  ret (fun r -> assert (r = Vec.get v i))];;

let _ = assert (first (Vec.make 3 7) = 7)

let _ = assert (checked_get (Vec.set (Vec.make 3 0) 2 9) 2 = 9)
