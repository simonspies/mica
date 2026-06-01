(* `Int.min` and `Int.max` are qualified paths registered in the prelude
   resolver; they route to the user-declared top-level values `int_min`
   and `int_max`. The body of `clamp` uses the qualified forms,
   exercising the resolver from a value position. *)

let int_min (x : int) (y : int) : int = if x <= y then x else y
[@@spec fun x y ->
  ret (fun v -> if x <= y then assert (v = x) else assert (v = y))];;

let int_max (x : int) (y : int) : int = if x <= y then y else x
[@@spec fun x y ->
  ret (fun v -> if x <= y then assert (v = y) else assert (v = x))];;

let clamp (lo : int) (hi : int) (x : int) : int =
  Int.max (Int.min x hi) lo
[@@spec fun lo hi x ->
  assert (lo <= hi);
  ret (fun v ->
    assert (lo <= v);
    assert (v <= hi))]
;;
