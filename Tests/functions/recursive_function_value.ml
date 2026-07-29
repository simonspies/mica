open Mica

(* A recursive self-reference has the declaration's specified arrow type, so it
   can be captured as a value and then called through that specification. *)
let rec count (n : int) : int =
  if n <= 0 then 0
  else
    let recur = count in
    recur (n - 1) + 1
[@@spec fun n ->
  assert (n >= 0);
  ret (fun r -> assert (r = n))];;
