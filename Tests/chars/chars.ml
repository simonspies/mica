open Mica

let code_chr (n : int) : int =
  Char.code (Char.chr n)
[@@spec fun n ->
  assert (0 <= n);
  assert (n < 256);
  ret (fun v ->
    assert (v = n))];;

let equal_self (c : char) : bool =
  Char.equal c c
[@@spec fun c ->
  ret (fun v ->
    assert (v))];;

let _ = assert (Char.code 'A' = 65)

let _ = assert (Char.equal (Char.chr 65) 'A')
