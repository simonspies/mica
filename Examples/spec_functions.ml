(* Spec-level functions: fn-marked definitions introduce SMT functions
   that specifications can call as ordinary applications. *)

let inc (x: int) : int = x + 1
[@@fn];;

let incr_via_spec (x: int) : int = x + 1
[@@spec fun x ->
  let y = inc x in
  ret (fun v ->
    assert (v = y))];;

let double_incr_via_spec (x: int) : int = incr_via_spec (incr_via_spec x)
[@@spec fun x ->
  let y = inc x in
  ret (fun v ->
    assert (y = x + 1);
    assert (v = x + 2))];;
