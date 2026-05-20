(* Spec-level functions: fn-marked definitions introduce SMT functions
   that specifications can call with bind (call ...). *)

let inc_spec (x: int) : int = x + 1
[@@fn inc];;

let incr_via_spec (x: int) : int = x + 1
[@@spec fun x ->
  bind (call inc x) @@ fun y ->
  ret (fun v ->
    assert (v = y))];;

let double_incr_via_spec (x: int) : int = incr_via_spec (incr_via_spec x)
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  bind (call inc x) @@ fun y ->
  bind (isint y) @@ fun m ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (m = n + 1);
    assert (r = n + 2))];;
