(* Recursive specification function for Fibonacci. *)
let rec fib_spec (n: int) : int =
  if n < 1 then 0
  else if n < 2 then 1
  else fib_spec (n - 1) + fib_spec (n - 2)
[@@fn fib];;

(* Recursive implementation. *)
let rec fib (n: int) : int =
  if n < 1 then 0
  else if n < 2 then 1
  else fib (n - 1) + fib (n - 2)
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  assert (n >= 0);
  ret (fun v ->
    bind (call fib x) @@ fun expected ->
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
  bind (isint n) @@ fun nn ->
  bind (isint i) @@ fun ii ->
  bind (isint a) @@ fun aa ->
  bind (isint b) @@ fun bb ->
  let ip1 = ii + 1 in
  assert (nn >= 0);
  assert (ii >= 0);
  assert (ii <= nn);
  bind (call fib i)   @@ fun fi  ->
  bind (isint fi)     @@ fun fii ->
  bind (call fib ip1) @@ fun fip ->
  bind (isint fip)    @@ fun fipi ->
  assert (aa = fii);
  assert (bb = fipi);
  ret (fun v ->
    bind (call fib n) @@ fun expected ->
    bind (isint expected) @@ fun ee ->
    bind (isint v)        @@ fun rr ->
    assert (rr = ee))]
;;

(* Closed iterative entry point: discharge the loop's invariant at i = 0,
   where fib(0) = 0 and fib(1) = 1 are immediate from one body unfolding. *)
let fib_iter (n: int) : int = fib_loop n 0 0 1
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  assert (n >= 0);
  ret (fun v ->
    bind (call fib x) @@ fun expected ->
    assert (v = expected))]
;;
