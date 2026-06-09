(* Float examples *)

(* `fp.leq x x` holds unless x is NaN; loads float_le and float_is_nan. *)
let le_refl (x : float) : float =
  x
[@@spec fun x -> ret (fun v -> assert (Float.le v x || Float.is_nan x))];;

(* abs is non-negative or NaN; loads float_abs, float_le, float_is_nan. *)
let abs_nonneg (x : float) : float =
  Float.abs x
[@@spec fun x -> ret (fun v -> assert (Float.le 0. v || Float.is_nan v))];;

(* min picks an operand, so it is le-bounded by max; exercises the
   float_min / float_max ite-cascade axioms together. *)
let min_le_max (a : float) (b : float) : float =
  Float.min a b
[@@spec fun a b ->
  ret (fun v ->
    assert (Float.le v (Float.max a b)
            || Float.is_nan a || Float.is_nan b))];;

(* Arithmetic round-trip: loads float_add / float_sub / float_mul /
   float_div / float_neg / float_sqrt in one query. *)
let arith (a : float) (b : float) : float =
  ((a +. b) -. a) *. (a /. b)
[@@spec fun a b ->
  ret (fun v ->
    assert (Float.is_finite v
            || Float.is_nan v
            || Float.equal (Float.abs v) (Float.sqrt (Float.neg v))
            || not (Float.is_finite v)))];;

(* Constants and of_int: nan is not finite; of_int and infinity load too. *)
let consts (n : int) : float =
  Float.of_int n
[@@spec fun n ->
  ret (fun v ->
    assert (not (Float.is_finite Float.nan)
            || Float.le v Float.infinity
            || Float.is_nan v))];;


let dist (x : float) (y : float) : float =
  Float.abs (x -. y)
[@@spec fun x y ->
  assert (Float.is_finite x && Float.is_finite y
          && Float.is_finite (x -. y));
  ret (fun v -> assert (Float.le 0. v))];;
