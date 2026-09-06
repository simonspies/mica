open Mica

(* A recursive ghost declaration is a proof by induction. The [@@decreases]
   measure ranks the arguments, and a recursive call must lower it: here the
   induction hypothesis is the lemma at `x - 1`. *)

let rec sum (n : int) : int =
  if n <= 0 then 0 else n + sum (n - 1)
[@@fn] [@@impl];;

let rec sum_nonneg (n : int) : unit =
  if n <= 0 then () else sum_nonneg (n - 1)
[@@ghost]
[@@spec fun x ->
  assert (0 <= x);
  ret (fun u -> assert (0 <= sum x))]
[@@decreases x]
;;

let use (n : int) : int =
  let%ghost _ = sum_nonneg n in
  sum n
[@@spec fun n ->
  assert (0 <= n);
  ret (fun v -> assert (0 <= v))]
