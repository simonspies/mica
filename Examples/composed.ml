(* Multi-argument functions and inter-function dependencies.
   Later declarations use the specs of earlier ones as their
   "induction hypotheses" for function calls. *)

(* Two-argument addition. *)
let add (x: int) (y: int) : int = x + y
[@@spec fun x y ->
  bind (isint x) @@ fun a ->
  bind (isint y) @@ fun b ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r = a + b))];;

(* Two-argument max: result is >= both inputs. *)
let max (x: int) (y: int) : int =
  if x >= y then x else y
[@@spec fun x y ->
  bind (isint x) @@ fun a ->
  bind (isint y) @@ fun b ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r >= a);
    assert (r >= b))];;

(* Double via add: uses the earlier `add` spec. *)
let double_via_add (x: int) : int = add x x
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r = n + n))];;

(* Clamp from below: uses the earlier `max` spec. *)
let clamp_low (lo: int) (x: int) : int = max lo x
[@@spec fun lo x ->
  bind (isint lo) @@ fun l ->
  bind (isint x) @@ fun n ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r >= l);
    assert (r >= n))];;

(* Nested calls: add (add x 1) (add x 1) = 2*(x+1). *)
let incr_double (x: int) : int = add (add x 1) (add x 1)
[@@spec fun x ->
  bind (isint x) @@ fun n ->
  ret (fun v ->
    bind (isint v) @@ fun r ->
    assert (r = 2 * (n + 1)))];;
