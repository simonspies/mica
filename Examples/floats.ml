open Mica

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

(* Arithmetic pipeline over bounded finite inputs; the final absolute value is
   finite and non-negative. *)
let arith (a : float) (b : float) (scale : float) : float =
  Float.abs (Float.min (a *. scale) b)
[@@spec fun a b scale ->
  assert (Float.is_finite a && Float.is_finite b && Float.is_finite scale);
  assert (Float.le 0. a && Float.le a 1.);
  assert (Float.le 0. b && Float.le b 1.);
  assert (Float.le 1. scale && Float.le scale 2.);
  ret (fun v ->
    assert (Float.is_finite v && Float.le 0. v)
    )];;

(* Square root of an absolute value is non-negative or NaN. *)
let sqrt_abs (x : float) : float =
  Float.sqrt (Float.abs x)
[@@spec fun x ->
  ret (fun v ->
    assert (Float.le 0. v || Float.is_nan v))];;

(* Constants and of_int: integer conversions are finite and bounded by infinities. *)
let consts (n : int) : float =
  Float.of_int n
[@@spec fun n ->
  ret (fun v ->
    assert (Float.is_finite v);
    assert (Float.le Float.neg_infinity v);
    assert (Float.le v Float.infinity))];;


let dist (x : float) (y : float) : float =
  Float.abs (x -. y)
[@@spec fun x y ->
  assert (Float.is_finite x && Float.is_finite y
          && Float.is_finite (x -. y));
  ret (fun v -> assert (Float.le 0. v))];;
