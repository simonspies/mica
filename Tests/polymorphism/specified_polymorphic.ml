open Mica

(* A specified declaration whose signature writes down ['a] is verified once,
   for an arbitrary meaning of ['a], and installed generalized. The argument
   reaches the result, so each use instantiates ['a] at its own type while the
   arithmetic the specification pins down survives the instantiation. *)
let pair_up (x : 'a) (n : int) : 'a * int = (x, n + 1)
[@@spec fun x n -> ret (fun v -> let (_, k) = v in assert (k = n + 1))]

let use_int (n : int) : int =
  let (_, k) = pair_up n 3 in k
[@@spec fun n -> ret (fun v -> assert (v = 4))]

let use_bool (b : bool) : int =
  let (_, k) = pair_up b 3 in k
[@@spec fun b -> ret (fun v -> assert (v = 4))]

let use_pair (n : int) : int =
  let (_, k) = pair_up (n, n) 3 in k
[@@spec fun n -> ret (fun v -> assert (v = 4))]
