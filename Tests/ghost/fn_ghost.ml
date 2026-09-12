(* TEST: roundtrip *)
open Mica

(* [@@fn ghost] makes a spec-level function callable from ghost code. The
   verifier checks the body a second time, as a proof that the function is
   defined at its argument and returns the value the body computes. With
   [@@impl] the same body is also verified as run-time code, so one declaration
   serves specifications, ghost code, and calls that run. *)
let rec sum (n : int) : int =
  if n <= 0 then 0 else n + sum (n - 1)
[@@fn ghost] [@@impl] [@@decreases n]
;;

(* A spec-level function may call another one. *)
let twice_sum (n : int) : int = sum n + sum n
[@@fn ghost]
;;

(* A ghost lemma proves what the axioms alone do not give: the induction is on
   the [@@decreases] measure, and the recursive call is the hypothesis. *)
let rec sum_nonneg (n : int) : unit =
  if n <= 0 then () else sum_nonneg (n - 1)
[@@ghost]
[@@spec fun x ->
  assert (0 <= x);
  ret (fun u -> assert (0 <= sum x))]
[@@decreases x]
;;

let bump (x : int) : int = x + 1
[@@spec fun x ->
  assert (x < hi);
  ret (fun v -> assert (v <= hi))]
[@@ghost (hi : int)]
;;

(* The name means the spec-level function in ghost code and the compiled one at
   run time, so the result of the call is the value the specification names. *)
let total (n : int) : int =
  let%ghost _ = sum_nonneg n in
  sum n
[@@spec fun n ->
  assert (0 <= n);
  ret (fun v -> assert (v = sum n && 0 <= v))]
;;

(* Each ghost binding carries an equation with its spec-level function, so the
   ghost argument to `bump` is the one the postcondition mentions. The lemma
   supplies the bound that the argument needs. *)
let use (n : int) : int =
  let%ghost _ = sum_nonneg n in
  let%ghost s = sum n in
  let%ghost t = twice_sum n in
  let%ghost _ = assert (t = s + s) in
  bump n [@ghost (n + t + 1 : int)]
[@@spec fun n ->
  assert (0 <= n);
  ret (fun v -> assert (v <= n + twice_sum n + 1))]
