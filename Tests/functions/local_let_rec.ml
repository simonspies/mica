(* TEST: roundtrip *)

open Mica

(* A local recursive function is specified through its own type, exactly as a
   recursive declaration is: the self-reference is typed at the specified
   arrow, so the recursive call goes through the specification. *)
let count_down (n : int) : int =
  let rec go : (int -> int) [@spec fun i ->
                  assert (i >= 0);
                  ret (fun r -> assert (r = 0))] =
    fun i -> if i <= 0 then 0 else go (i - 1) in
  if n >= 0 then go n else 0
[@@spec fun n -> ret (fun r -> assert (r = 0))]
