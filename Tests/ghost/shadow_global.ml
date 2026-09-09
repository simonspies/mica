open Mica

let lemma (n : int) : int = n
[@@ghost]
[@@spec fun n -> ret (fun r -> assert (r = n))];;
let lemma (n : int) : int = n + 1;;
let use (n : int) : int =
  let%ghost _ = lemma n in
  n
[@@spec fun n -> ret (fun r -> assert (r = n))]
