(* Spec-level recursive functions over tuples.

   Exercises three pieces of newly-added spec-function machinery in
   combination: tuples, let-bindings, and tuple construction at
   recursive call sites.

   The relational encoder requires unary calls, so a recursion that
   takes several arguments is paired into a single tuple value. The
   spec function is declared once with `[@@fn name]`; a runtime
   implementation of the same shape is then verified against it by
   calling the spec function as an ordinary application in the spec.

   Spec discipline: in pre- and postconditions one cannot unfold the
   relation arbitrarily — the verifier only unfolds the body one
   level. So a function that recurses on the argument can export
   facts about that recursion, but a non-recursive caller can only
   export the equality with the relational result. The closed entry
   point at the bottom illustrates this restriction. *)

(* --- Sum of [1..n] via tail recursion on an `(acc, i)` pair. --- *)

(* Spec-level recursive definition. The `[@@fn sum_acc]` annotation
   registers it as an SMT function; specs invoke it by its OCaml name
   `sum_acc_rec`. *)
let rec sum_acc_rec (s: int * int) : int =
  let acc = s.0 in
  let i   = s.1 in
  if i < 1 then acc
  else sum_acc_rec (acc + i, i - 1)
[@@fn sum_acc];;

(* Runtime version with the same shape, verified against the spec
   function exactly. Each recursive runtime call discharges
   `sum_acc_rec (acc+i, i-1) = result`; the postcondition's
   `sum_acc_rec s` is then equal to that, by one body unfolding. *)
let rec sum_acc (s: int * int) : int =
  let acc = s.0 in
  let i   = s.1 in
  if i < 1 then acc
  else sum_acc (acc + i, i - 1)
[@@spec fun s ->
  ret (fun v ->
    let expected = sum_acc_rec s in
    assert (v = expected))];;

(* Closed entry point.  This function does not carry recursion itself,
   so its spec can only restate what `sum_acc` already promised on the
   initial `(0, n)` pair.  The verifier accepts this without inspecting
   the body of `sum_acc` any further. *)
let sum_to_n (n: int) : int = sum_acc (0, n)
[@@spec fun n ->
  ret (fun v ->
    let expected = sum_acc_rec (0, n) in
    assert (v = expected))];;
