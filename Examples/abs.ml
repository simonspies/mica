(* Absolute value with an exact functional spec: r = |n|.
   We split on the sign of n using assertion-level if/then/else. *)
let abs_ (x: int) : int = if x < 0 then 0 - x else x
[@@spec fun x ->
  ret (fun v ->
    if x >= 0 then assert (v = x)
    else assert (v = -x))];;

(* ReLU / max-with-zero: exact spec r = max(n, 0). *)
let relu (x: int) : int = if x < 0 then 0 else x
[@@spec fun x ->
  ret (fun v ->
    if x >= 0 then assert (v = x)
    else assert (v = 0))];;

(* Clamp to [-10, 10] with exact spec. *)
let clamp (x: int) : int =
  if x < 0 - 10 then 0 - 10
  else if x > 10 then 10
  else x
[@@spec fun x ->
  ret (fun v ->
    if x < 0 - 10 then assert (v = 0 - 10)
    else if x > 10 then assert (v = 10)
    else assert (v = x))];;
