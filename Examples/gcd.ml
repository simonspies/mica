let rec gcd (a: int) (b: int) : int =
  if b = 0 then a
  else gcd b (a mod b)
[@@spec fun x y ->
  bind (isint x) @@ fun a ->
  bind (isint y) @@ fun b ->
  assert (b >= 0);
  assert (a >= 0);
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r >= 0);
    assert (r <= a + b);
    ret ())]
;;
let _ = assert (gcd 12 8 >= 0)
