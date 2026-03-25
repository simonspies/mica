(* Sum type construction with if/then/else *)
type result = Ok of int | Err of int

let classify (x : int) : result =
  if x >= 0 then Ok x else Err x
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  ret (fun v ->
    if n >= 0 then (assert (v = inj 0 2 x); ret ())
    else (assert (v = Err x); ret ()))];;
