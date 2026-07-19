open Mica

let checked_pos (n : int) : int =
  if n > 0 then n else failwith "expected a positive number"
[@@spec fun n ->
  assert (n > 0);
  ret (fun v ->
    assert (v = n))];;

let checked_sub (a : int) (b : int) : int =
  if a < b then invalid_arg "underflow" else a - b
[@@spec fun a b ->
  assert (b <= a);
  ret (fun v ->
    assert (v = a - b))];;

let _ = assert (checked_pos 5 = 5)

let _ = assert (checked_sub 7 2 = 5)

(* Local bindings shadow bare prelude primitives. *)
let shadow_failwith (n : int) : int =
  let failwith = n + 1 in
  failwith
[@@spec fun n ->
  ret (fun v ->
    assert (v = n + 1))];;

let shadow_argument (failwith : int) : int = failwith
[@@spec fun failwith ->
  ret (fun v ->
    assert (v = failwith))];;

(* Top-level bindings shadow the opened prelude in later declarations. *)
let invalid_arg (x : int) : int = x + 2
[@@spec fun x ->
  ret (fun v ->
    assert (v = x + 2))];;

let shadow_invalid_arg (n : int) : int = invalid_arg n
[@@spec fun n ->
  ret (fun v ->
    assert (v = n + 2))];;

let _ = assert (shadow_failwith 4 = 5)

let _ = assert (shadow_argument 4 = 4)

let _ = assert (shadow_invalid_arg 4 = 6)
