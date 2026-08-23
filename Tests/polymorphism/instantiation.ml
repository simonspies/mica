(* TEST: roundtrip *)
open Mica

(* What a use site may pick: the argument's type variable is instantiated at a
   named type, at a specified function, at another declaration's variable, and
   at two unrelated types at once. Each use carries a number through the
   polymorphic declaration, so the instantiation has to survive to prove it. *)

let carry (x : 'a) (n : int) : 'a * int = (x, n + 1)
[@@spec fun x n -> ret (fun v -> let (_, k) = v in assert (k = n + 1))]

(* A recursive named type — the payload's variable is substituted under the
   fixpoint the logical relation unfolds. *)
let at_list (l : int list) : int =
  let (_, k) = carry l 3 in k
[@@spec fun l -> ret (fun v -> assert (v = 4))]

(* A specified arrow, called back out of the pair it was carried in. *)
let bump (n : int) : int = n + 1
[@@spec fun n -> ret (fun v -> assert (v = n + 1))]

let at_function (u : unit) : int =
  let (f, k) = carry bump 3 in f k
[@@spec fun u -> ret (fun v -> assert (v = 5))]

(* The enclosing declaration's own rigid variable, twice over. *)
let at_variable (y : 'b) : int =
  let (z, k) = carry y 3 in
  let (_, m) = carry z k in m
[@@spec fun y -> ret (fun v -> assert (v = 5))]

(* A declaration with two variables, used at two different pairs of types. *)
let pick (x : 'a) (y : 'b) (n : int) : 'b * int = (y, n + 1)
[@@spec fun x y n -> ret (fun v -> let (_, k) = v in assert (k = n + 1))]

let at_int_bool (n : int) (b : bool) : int =
  let (_, k) = pick n b 3 in k
[@@spec fun n b -> ret (fun v -> assert (v = 4))]

let at_bool_int (b : bool) (n : int) : int =
  let (_, k) = pick b n 3 in k
[@@spec fun b n -> ret (fun v -> assert (v = 4))]
