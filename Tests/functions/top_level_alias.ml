open Mica

(* A top-level alias currently does not retain a verifier value binding. The
   following use therefore documents the present boundary of top-level
   declaration threading. *)
let id (x : int) : int = x
[@@spec fun x -> ret (fun v -> assert (v = x))];;

let alias = id;;

let use_alias (x : int) : int = alias x
[@@spec fun x -> ret (fun v -> assert (v = x))];;
