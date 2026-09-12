(* TEST: roundtrip *)
open Mica

let rec countdown (n : int) : int =
  if n <= 0 then 0 else countdown (n - 1)
[@@fn] [@@impl] [@@decreases n];;

(* Calls to countdown do not need to decrease f's measure. *)
let rec f (n : int) : int =
  if n >= 10 then countdown 100 else
    let k = countdown (n + 10) in
    f (n + 1) + k
[@@fn] [@@decreases 10 - n];;

let lemma (n : int) : unit = ()
[@@ghost]
[@@spec fun n -> ret (fun result -> assert (f n = f n))];;
