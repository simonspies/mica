open Mica

(* A data declaration's field types are elaborated before any specification
   could be typechecked, so [@spec] is not accepted there. *)
type box = { run : (int -> int) [@spec fun x -> ret (fun r -> assert (r > x))] }
