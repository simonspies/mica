open Mica

(* Applying a function value that carries no specification is rejected: an
   unspecified function type is logically uninhabited, so there is nothing to
   call it with. *)

let apply (f : int -> int) (n : int) : int = f n
[@@spec fun f n ->
  ret (fun v -> assert (v = v))]
