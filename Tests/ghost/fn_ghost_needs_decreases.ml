(* TEST: no-compile *)
open Mica

(* The proof is an induction on the [@@decreases] measure. A recursive
   function without a measure cannot be called from ghost code. *)
let rec sum (n : int) : int =
  if n <= 0 then 0 else n + sum (n - 1)
[@@fn ghost]
;;

let use (n : int) : int =
  let%ghost _ = sum n in
  n
[@@spec fun n -> ret (fun v -> assert (v = n))]
