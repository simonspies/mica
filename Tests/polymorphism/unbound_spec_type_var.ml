(* TEST: no-compile *)
open Mica

(* A specification is written against the signature it annotates, so it may
   name the variables the signature binds and no others. A variable only a
   spec mentions could never be determined at a call site. *)
let get (r : (int ref [@owned])) : int = !r
[@@spec fun r -> bind (own r) @@ fun (v : 'b) -> ret (fun res -> assert (res = v))]
