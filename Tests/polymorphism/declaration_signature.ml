open Mica

(* The signature may equally be written on the declaration's own binder; it is
   the same binding site, so [pair_up] is polymorphic either way. *)
let pair_up :
  ('a -> 'a * int) [@spec fun x -> ret (fun v -> let (_, k) = v in assert (k = 2))] =
  fun x -> (x, 2)

let use_int (n : int) : int =
  let (_, k) = pair_up n in k
[@@spec fun n -> ret (fun v -> assert (v = 2))]

let use_str (s : string) : int =
  let (_, k) = pair_up s in k
[@@spec fun s -> ret (fun v -> assert (v = 2))]
