(* Multi-argument functions and inter-function dependencies.
   Later declarations use the specs of earlier ones as their
   "induction hypotheses" for function calls. *)

(* Two-argument addition. *)
let add (x: int) (y: int) : int = x + y
[@@spec fun x y ->
  ret (fun v ->
    assert (v = x + y))];;

(* Two-argument max: result is >= both inputs. *)
let max (x: int) (y: int) : int =
  if x >= y then x else y
[@@spec fun x y ->
  ret (fun v ->
    assert (v >= x);
    assert (v >= y))];;

(* Double via add: uses the earlier `add` spec. *)
let double_via_add (x: int) : int = add x x
[@@spec fun x ->
  ret (fun v ->
    assert (v = x + x))];;

(* Clamp from below: uses the earlier `max` spec. *)
let clamp_low (lo: int) (x: int) : int = max lo x
[@@spec fun lo x ->
  ret (fun v ->
    assert (v >= lo);
    assert (v >= x))];;

(* Nested calls: add (add x 1) (add x 1) = 2*(x+1). *)
let incr_double (x: int) : int = add (add x 1) (add x 1)
[@@spec fun x ->
  ret (fun v ->
    assert (v = 2 * (x + 1)))];;
