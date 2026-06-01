let clamp (lo : int) (hi : int) (x : int) : int =
  Int.max (Int.min x hi) lo
[@@spec fun lo hi x ->
  assert (lo <= hi);
  ret (fun v ->
    assert (lo <= v);
    assert (v <= hi))]
;;
