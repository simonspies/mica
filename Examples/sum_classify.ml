open Mica

(* Sum type construction with if/then/else *)
type result = Ok of int | Err of int

let classify (x : int) : result =
  if x >= 0 then Ok x else Err x
[@@spec fun x ->
  ret (fun v ->
    if x >= 0 then
      (bind (isinj 0 2 v) @@ fun (payload : int) -> assert (payload = x))
    else
      (bind (isinj 1 2 v) @@ fun (payload : int) -> assert (payload = x)))];;
