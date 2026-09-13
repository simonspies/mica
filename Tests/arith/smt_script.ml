(* TEST: --smt-commands-only --timeout=30000 *)
open Mica

(* Pins the SMT script generated for a minimal verified function. The
   preamble shows the budget from [--timeout]. *)
let id_ (x: int) : int = x
[@@spec fun x -> ret (fun v -> assert (v = x))];;

(* The same recursion twice. Without a measure it is axiomatized in both
   directions; with one, the two definedness axioms give way to the totality
   assertion the termination query establishes. *)
let rec countdown (n : int) : int =
  if n <= 0 then 0 else countdown (n - 1)
[@@fn];;

let rec countdown_measured (n : int) : int =
  if n <= 0 then 0 else countdown_measured (n - 1)
[@@fn] [@@decreases n];;
