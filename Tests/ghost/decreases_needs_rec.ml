(* TEST: no-compile *)
open Mica

let widen (lo : int) (hi : int) : unit = ()
[@@ghost]
[@@spec fun lo hi ->
  assert (lo <= hi);
  ret (fun u -> assert (lo <= hi))]
[@@decreases hi - lo]
