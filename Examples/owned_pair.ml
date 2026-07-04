(* Owned-reference lookup is a performance-sensitive path. To resolve `!r`, the
   verifier walks the ownership context and uses low-effort checks to test
   whether the dereferenced location equals each candidate's location. *)

type ilist = Nil | Cons of int * ilist

(* A recursive function whose relational encoding contributes guarded axioms. *)
let rec length (xs : ilist) : int =
  match xs with
  | Nil -> 0
  | Cons p -> 1 + length p.2
[@@spec fun xs -> ret (fun v -> assert (v >= 0))];;

(* Two owned cells of the same type: each read may skip candidates before the
   matching points-to is consumed. *)
let two_cells (x : int) : int =
  let r1 = ref 1 [@owned] in
  let r2 = ref 2 [@owned] in
  let a = !r1 in
  let b = !r2 in
  a + b
[@@spec fun x ->
  ret (fun v ->
    assert (v = 3))];;

(* Three owned cells: more candidates exercise more non-matching probes. *)
let three_cells (x : int) : int =
  let r1 = ref 1 [@owned] in
  let r2 = ref 2 [@owned] in
  let r3 = ref 3 [@owned] in
  let a = !r1 in
  let b = !r2 in
  let c = !r3 in
  a + b + c
[@@spec fun x ->
  ret (fun v ->
    assert (v = 6))];;
