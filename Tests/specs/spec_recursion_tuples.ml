open Mica

(* Spec-level recursive functions over tuples.

   Exercises three pieces of newly-added spec-function machinery in
   combination: tuples, let-bindings, and tuple construction at
   recursive call sites.

   The relational encoder requires unary calls, so a recursion that
   takes several arguments is paired into a single tuple value.

   Spec discipline: in pre- and postconditions one cannot unfold the
   relation arbitrarily — the verifier only unfolds the body one
   level. So a function that recurses on the argument can export
   facts about that recursion, but a non-recursive caller can only
   export the equality with the relational result. The closed entry
   point at the bottom illustrates this restriction. *)

(* --- Sum of [1..n] via tail recursion on an `(acc, i)` pair. --- *)

(* Spec-level recursive definition, run at both levels. Each recursive
   runtime call discharges `sum_acc (acc+i, i-1) = result`; the generated
   postcondition follows by one body unfolding. *)
let rec sum_acc ((acc : int), (i : int)) : int =
  if i < 1 then acc
  else sum_acc (acc + i, i - 1)
[@@fn] [@@impl];;

(* Closed entry point.  This function does not carry recursion itself,
   so its spec can only restate what `sum_acc` already promised on
   the initial `(0, n)` pair.  The verifier accepts this without
   inspecting the body of `sum_acc` any further. *)
let sum_to_n (n: int) : int = sum_acc (0, n)
[@@spec fun n ->
  ret (fun v ->
    let expected = sum_acc (0, n) in
    assert (v = expected))];;
