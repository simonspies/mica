(* The rewriter's input; `erase.expected` is what must come out of it. *)

let widen (x : int) (y : int) : unit = ignore (x + y)
[@@ghost]
[@@spec fun x y -> assert (x <= y); ret (fun _ -> emp)]

let bump (n : int) : int = n + 1
[@@ghost (hi : int)]
[@@spec fun n -> assert (n < hi); ret (fun v -> assert (v <= hi))]

let use (n : int) : int =
  let%ghost () = widen n 100 in
  let%ghost m = n + 1 in
  (bump n [@ghost 100])
