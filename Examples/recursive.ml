(* Recursive functions and what the verifier can prove about them.
   The verifier uses the spec as the induction hypothesis for recursive calls,
   so a valid spec must be an inductive invariant.
   Z3's quantifier-free linear arithmetic can express exact specs for
   linear recurrences and weaker invariants for nonlinear ones. *)

(* 1. Multiplication by 2 via repeated addition.
      Exact spec: r = 2 * n.  Linear recurrence, verified exactly. *)
let rec double_rec (n: int) : int =
  if n <= 0 then 0
  else double_rec (n - 1) + 2
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  assert (n >= 0);
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r = n * 2);
    ret ())];;

(* 2. Power of 2: computes 2^n.
      We cannot express 2^n in linear arithmetic, so we prove the weaker
      (but nontrivial) invariant r >= 1.
      Verification: base case 1 >= 1; inductive case 2 * r' >= 2 >= 1. *)
let rec pow2 (n: int) : int =
  if n <= 0 then 1
  else pow2 (n - 1) * 2
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  assert (n >= 0);
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r >= 1);
    ret ())];;

(* 3. Triangle numbers: computes 1 + 2 + ... + n.
      Exact spec: r = n*(n+1)/2. Z3's nonlinear arithmetic handles this —
      the inductive step reduces to (n-1)*n/2 + n = n*(n+1)/2, i.e.
      (n²+n)/2 = (n²+n)/2. *)
let rec triangle (n: int) : int =
  if n <= 0 then 0
  else triangle (n - 1) + n
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  assert (n >= 0);
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r = n * (n + 1) / 2);
    ret ())];;
