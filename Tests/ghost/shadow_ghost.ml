open Mica

let lemma (n : int) : int = n
[@@ghost]
[@@spec fun n -> ret (fun r -> assert (r = n))];;
let replacement (n : int) : int = n + 1
[@@spec fun n -> ret (fun r -> assert (r = n + 1))];;
let use (n : int) : int =
  let%ghost lemma = replacement in
  let%ghost x = lemma n in
  let%ghost _ = assert (x = n) in
  n
[@@spec fun n -> ret (fun r -> assert (r = n))]
