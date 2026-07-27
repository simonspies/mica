open Mica

(* An arrow carries at most one specification. *)
let f (g : ((int -> int) [@spec fun x -> ret (fun r -> assert (r > x))])
                         [@spec fun x -> ret (fun r -> assert (r >= x))]) (n : int) : int = g n
