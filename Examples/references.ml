(* Examples that exercise allocation, dereference, assignment, and sequencing. *)

(* Swap the contents of two integer references. *)
let swap (x : int ref) (y : int ref) : unit =
  let tmp = !x in
  x := !y;
  y := tmp
[@@spec fun x y ->
  bind (own x) @@ fun vx ->
  bind (isint vx) @@ fun a ->
  bind (own y) @@ fun vy ->
  bind (isint vy) @@ fun b ->
  ret (fun r ->
    assert (r = ());
    bind (own x) @@ fun vx2 ->
    bind (isint vx2) @@ fun a2 ->
    bind (own y) @@ fun vy2 ->
    bind (isint vy2) @@ fun b2 ->
    assert (a2 = b);
    assert (b2 = a))];;

(* Swap two local cells and return the observed pair. *)
let swap_pair_via_refs (a : int) (b : int) : int * int =
  let x = ref a in
  let y = ref b in
  swap x y;
  (!x, !y)
[@@spec fun a b ->
  bind (isint a) @@ fun n ->
  bind (isint b) @@ fun m ->
  ret (fun v ->
    bind (isint v.0) @@ fun fst ->
    bind (isint v.1) @@ fun snd ->
    assert (fst = m);
    assert (snd = n))];;

(* Reuse swap twice; the state returns to the start. *)
let id_by_swapping_twice (a : int) (b : int) : int * int =
  let x = ref a in
  let y = ref b in
  swap x y;
  swap x y;
  (!x, !y)
[@@spec fun a b ->
  bind (isint a) @@ fun n ->
  bind (isint b) @@ fun m ->
  ret (fun v ->
    bind (isint v.0) @@ fun fst ->
    bind (isint v.1) @@ fun snd ->
    assert (fst = n);
    assert (snd = m))];;

(* Sum into the left cell while keeping the right one unchanged. *)
let sum_into_left_local (a : int) (b : int) : int * int =
  let x = ref a in
  let y = ref b in
  x := !x + !y;
  (!x, !y)
[@@spec fun a b ->
  bind (isint a) @@ fun n ->
  bind (isint b) @@ fun m ->
  ret (fun v ->
    bind (isint v.0) @@ fun left ->
    bind (isint v.1) @@ fun right ->
    assert (left = n + m);
    assert (right = m))];;

(* A slightly more creative reference program: conditionally normalize order by swapping. *)
let sort2_via_swap (a : int) (b : int) : int * int =
  let x = ref a in
  let y = ref b in
  if !x > !y then swap x y else ();
  (!x, !y)
[@@spec fun a b ->
  bind (isint a) @@ fun n ->
  bind (isint b) @@ fun m ->
  ret (fun v ->
    bind (isint v.0) @@ fun fst ->
    bind (isint v.1) @@ fun snd ->
    assert (fst <= snd);
    if n > m then
      assert (fst = m && snd = n)
    else
      assert (fst = n && snd = m))];;

(* Two increments through the same local cell. *)
let bump_twice (n : int) : int =
  let x = ref n in
  x := !x + 1;
  x := !x + 1;
  !x
[@@spec fun n ->
  bind (isint n) @@ fun m ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r = m + 2))];;
