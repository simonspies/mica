let half (x: int) : int =
  x / 2
[@@spec fun v ->
  bind (isint v) @@ fun n ->
  ret (fun r ->
    bind (isint r) @@ fun q ->
    assert (q * 2 <= n);
    assert (n < (q + 1) * 2))]
;;
let _ = assert (half 10 = 5)
;;
let _ = assert (half 7 = 3)
