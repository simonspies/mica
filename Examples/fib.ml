let rec fib (n: int) : int =
  if n = 0 then 0
  else if n = 1 then 1
  else fib (n - 1) + fib (n - 2)
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r >= 0);
    ret ())]
;;
let _ = assert (0 <= fib 10)
