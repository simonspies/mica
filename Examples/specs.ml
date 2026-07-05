open Mica

(* Single-argument functions with type annotations for the verifier. *)

(* 1. Identity: returns the input unchanged *)
let id (x: int) : int = x
[@@spec fun x ->
  ret (fun v ->
    assert (v = x))];;

(* 2. Increment: result is exactly one more than the input *)
let incr (x: int) : int = x + 1
[@@spec fun x ->
  ret (fun v ->
    assert (v = x + 1))];;

(* 3. Double: result is exactly twice the input *)
let double (x: int) : int = x * 2
[@@spec fun x ->
  ret (fun v ->
    assert (v = x * 2))];;

(* 4. Predecessor: result is exactly one less than the input *)
let pred_ (x: int) : int = x - 1
[@@spec fun x ->
  ret (fun v ->
    assert (v = x - 1))];;

(* 5. Square: result is exactly the square of the input *)
let square (x: int) : int = x * x
[@@spec fun x ->
  ret (fun v ->
    assert (v = x * x))];;

(* 6. Sign: result is -1, 0, or 1 according to the sign of the input. *)
let sign (x: int) : int = if x < 0 then 0 - 1 else if x = 0 then 0 else 1
[@@spec fun x ->
  ret (fun v ->
    if x < 0 then assert (v = 0 - 1)
    else if x = 0 then assert (v = 0)
    else assert (v = 1))];;

(* 7. Let-binding: compute (x + 1) * 2 using an intermediate let.       *)
(*    Tests that let-bound variables in the body are compiled correctly.  *)
let double_succ (x: int) : int =
  let y = x + 1 in
  y * 2
[@@spec fun x ->
  ret (fun v ->
    assert (v = (x + 1) * 2))];;

(* 8. Cube: result is n*n*n *)
let cube (x: int) : int = x * x * x
[@@spec fun x ->
  ret (fun v ->
    assert (v = x * x * x))];;
(* 9. Subtract ten: result is x - 10 *)
let sub10 (x: int) : int = x - 10
[@@spec fun x ->
  ret (fun v ->
    assert (v = x - 10))];;

(* 10. Conditional lower bound: either branch produces 0+something or 0-something, *)
(*     so we can only assert a weaker property. Here: result is non-negative        *)
(*     when input is non-negative (using a branch spec).                            *)
let nonneg_floor (x: int) : int = if x >= 0 then x + 0 else 0 - x
[@@spec fun x ->
  ret (fun v ->
    assert (v >= 0))];;

(* 11. Weaker spec: given x >= 0, only assert the result is non-negative. *)
let double_nonneg (x: int) : int = x * 2
[@@spec fun x ->
  assert (x >= 0);
  ret (fun v ->
    assert (v >= 0))];;

(* SHOULD FAIL: wrong spec — claims result = x + 2 but body computes x + 1 *)
(* let wrong_incr (x: int) : int = x + 1
[@@spec fun x ->
  ret (fun v ->
    assert (v = x + 2))];;  *)

(* SHOULD FAIL: postcondition too strong — claims v >= x + 1, but the body *)
(*     returns x * 2, which is smaller when x = 0.                          *)
(* let bad_double (x: int) : int = x * 2
[@@spec fun x ->
  ret (fun v ->
    assert (v >= x + 1))];;  *)
