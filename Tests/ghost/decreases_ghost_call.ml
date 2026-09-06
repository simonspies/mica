(* TEST: no-compile roundtrip *)
open Mica

let rank (n : int) : int = n
[@@ghost]
[@@spec fun x -> ret (fun r -> assert (r = x))]
;;

let rec lemma (n : int) : unit = ()
[@@ghost]
[@@spec fun x -> ret (fun u -> assert true)]
[@@decreases rank x]
