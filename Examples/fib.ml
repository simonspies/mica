(* Recursive specification function for Fibonacci. *)
let rec fib (n: int) : int =
  if n < 1 then 0
  else if n < 2 then 1
  else fib (n - 1) + fib (n - 2)
[@@fn];;

(* Recursive implementation. *)
let rec fib_impl (n: int) : int =
  if n < 1 then 0
  else if n < 2 then 1
  else fib_impl (n - 1) + fib_impl (n - 2)
[@@spec fun x ->
  assert (x >= 0);
  ret (fun v ->
    let expected = fib x in
    assert (v = expected))]
;;

(* Iterative implementation verified against the tree-recursive spec.

   Loop invariant:
     0 <= i <= n,  a = fib(i),  b = fib(i+1).
   The recursive call advances i by one, swapping b into a and a+b into b.
   The verifier discharges fib(i+2) = fib(i+1) + fib(i) by a single unfolding
   of the body-def and value axioms, given fib_rel-def at i and i+1. *)
let rec fib_loop (n: int) (i: int) (a: int) (b: int) : int =
  if i >= n then a
  else fib_loop n (i + 1) b (a + b)
[@@spec fun n i a b ->
  assert (n >= 0);
  assert (i >= 0);
  assert (i <= n);
  let fi  = fib i in
  let fip = fib (i + 1) in
  assert (a = fi);
  assert (b = fip);
  ret (fun v ->
    let expected = fib n in
    assert (v = expected))]
;;

(* Closed iterative entry point: discharge the loop's invariant at i = 0,
   where fib(0) = 0 and fib(1) = 1 are immediate from one body unfolding. *)
let fib_iter (n: int) : int = fib_loop n 0 0 1
[@@spec fun x ->
  assert (x >= 0);
  ret (fun v ->
    let expected = fib x in
    assert (v = expected))]
;;
