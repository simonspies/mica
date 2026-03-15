(* Single-argument functions with type annotations for the verifier.        *)
(* Multi-argument functions are not yet supported (Spec.complete requires   *)
(* exactly one argument with full type annotation).                         *)
(*                                                                           *)
(* Known limitation: if a function may return the raw input value (not      *)
(* wrapped in an arithmetic expression), the postcondition `bind (isint v)` *)
(* cannot resolve the integer term and the verifier will report             *)
(* "could not resolve type predicate for r". The examples below are chosen  *)
(* to avoid this: every code path produces a fresh arithmetic result.       *)

(* 1. Increment: result is exactly one more than the input *)
let incr (x: int) : int = x + 1
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r = n + 1);
    ret ())];;

(* 2. Double: result is exactly twice the input *)
let double (x: int) : int = x * 2
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r = n * 2);
    ret ())];;

(* 3. Predecessor: result is exactly one less than the input *)
let pred_ (x: int) : int = x - 1
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r = n - 1);
    ret ())];;

(* 4. Square: result is exactly the square of the input *)
let square (x: int) : int = x * x
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r = n * n);
    ret ())];;

(* 5. Sign: result is -1, 0, or 1 according to the sign of the input.    *)
(*    Every branch produces a fresh arithmetic value, so isint resolves.  *)
let sign (x: int) : int = if x < 0 then 0 - 1 else if x = 0 then 0 else 1
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    if n < 0 then assert (r = 0 - 1); ret ()
    else if n = 0 then assert (r = 0); ret ()
    else assert (r = 1); ret ())];;

(* 6. Let-binding: compute (x + 1) * 2 using an intermediate let.       *)
(*    Tests that let-bound variables in the body are compiled correctly.  *)
let double_succ (x: int) : int =
  let y = x + 1 in
  y * 2
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r = (n + 1) * 2);
    ret ())];;

(* 7. Cube: result is n*n*n *)
let cube (x: int) : int = x * x * x
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r = n * n * n);
    ret ())];;
(*
(* 8. Subtract ten: result is x - 10 *)
let sub10 (x: int) : int = x - 10
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r = n - 10);
    ret ())];;

(* 9. Conditional lower bound: either branch produces 0+something or 0-something, *)
(*    so we can only assert a weaker property. Here: result is non-negative        *)
(*    when input is non-negative (using a branch spec).                            *)
let nonneg_floor (x: int) : int = if x >= 0 then x + 0 else 0 - x
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r >= 0);
    ret ())];;

(* 10. SHOULD FAIL: wrong spec — claims result = n + 2 but body computes n + 1 *)
let wrong_incr (x: int) : int = x + 1
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r = n + 2);
    ret ())];;

(* 11. SHOULD FAIL: precondition is satisfied but postcondition is too strong:  *)
(*     the spec claims r >= n + 1, but the result is just n.                    *)
let bad_double (x: int) : int = x * 2
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r >= n + 1);
    ret ())];;

(* 12. Weaker spec: result is a multiple of 2 (r = n * 2 implies r >= n * 2 - 1, *)
(*     but here we just assert r >= 0 assuming n >= 0).                            *)
(*     Pre: n >= 0; post: r >= 0.                                                  *)
let double_nonneg (x: int) : int = x * 2
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  assert (n >= 0);
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r >= 0);
    ret ())];;
*)