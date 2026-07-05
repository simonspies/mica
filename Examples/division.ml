open Mica

let half (x: int) : int =
  x / 2
[@@spec fun v ->
  ret (fun r ->
    assert (r * 2 <= v);
    assert (v < (r + 1) * 2))]
;;
let _ = assert (half 10 = 5)
;;
let _ = assert (half 7 = 3)
