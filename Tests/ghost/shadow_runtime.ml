open Mica

let lemma (n : int) : int = n
[@@spec fun n -> ret (fun r -> assert (r = n))];;
let lemma (n : int) : int = n
[@@ghost]
[@@spec fun n -> ret (fun r -> assert (r = n))];;
let use (n : int) : int =
  lemma n
[@@spec fun n -> ret (fun r -> assert (r = n))]
