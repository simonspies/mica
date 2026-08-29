open Mica

(* [@@impl] on a polymorphic spec-level function. Its specification is stated
   at the declaration's own type variables, not at fresh ones. *)

let label ((x : 'a), (n : int)) : 'a * int = (x, n + 1)
[@@fn] [@@impl];;

let bump (n : int) : int =
  let (_, k) = label (n, n) in k
[@@spec fun n -> ret (fun v -> assert (v = n + 1))];;
