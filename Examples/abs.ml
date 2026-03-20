(* Absolute value with an exact functional spec: r = |n|.
   We split on the sign of n using assertion-level if/then/else. *)
let abs_ (x: int) : int = if x < 0 then 0 - x else x
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    if n >= 0 then assert (r = n); ret ()
    else assert (r = -n); ret ())];;

(* ReLU / max-with-zero: exact spec r = max(n, 0). *)
let relu (x: int) : int = if x < 0 then 0 else x
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    if n >= 0 then assert (r = n); ret ()
    else assert (r = 0); ret ())];;

(* Clamp to [-10, 10] with exact spec. *)
let clamp (x: int) : int =
  if x < 0 - 10 then 0 - 10
  else if x > 10 then 10
  else x
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    if n < 0 - 10 then assert (r = 0 - 10); ret ()
    else if n > 10 then assert (r = 10); ret ()
    else assert (r = n); ret ())];;
