(* TEST: no-compile roundtrip *)
open Mica

let rec lemma (n : int) : unit = ()
[@@ghost]
[@@spec fun x -> ret (fun u -> assert true)]
[@@decreases n]
