(* A flat [m]-by-[n] matrix stored in a single shared [int array].

   The element at row [r], column [c] lives at flat index [r * n + c]. 
   The main point of this example is pushing the boundaries on nonlinear 
   arithmetic, since for element access the verifier must prove  
   [r * n + c < m * n] from [0 <= r < m] and [0 <= c < n]. *)


(* Element read.  The bound [r * n + c < length a] follows from
   [r * n + c < m * n <= length a], the first step being the nonlinear part. *)
let mget (a : int array) (m : int) (n : int) (r : int) (c : int) : int =
  a.(r * n + c)
[@@spec fun a m n r c ->
  assert (0 <= r && r < m);
  assert (0 <= c && c < n);
  assert (m * n <= Array.length a);
  ret (fun v -> assert (true))];;

(* Element write, same index discipline. *)
let mset (a : int array) (m : int) (n : int) (r : int) (c : int) (v : int) : unit =
  a.(r * n + c) <- v
[@@spec fun a m n r c v ->
  assert (0 <= r && r < m);
  assert (0 <= c && c < n);
  assert (m * n <= Array.length a);
  ret (fun res -> assert (true))];;

(* Allocate an [m]-by-[n] matrix.  [Array.make]'s nonnegative-length obligation
   becomes [0 <= m * n], again nonlinear. *)
let make_matrix (m : int) (n : int) : int array =
  Array.make (m * n) 0
[@@spec fun m n ->
  assert (0 <= m && 0 <= n);
  ret (fun a -> assert (m * n <= Array.length a))];;


(* ---------------------------------------------------------------------- *)
(* Fill                                                                   *)
(* ---------------------------------------------------------------------- *)

(* Set every column of row [r] to [v]. *)
let rec set_row (a : int array) (m : int) (n : int) (r : int) (c : int) (v : int) : unit =
  if c < n then
    (mset a m n r c v;
     set_row a m n r (c + 1) v)
  else ()
[@@spec fun a m n r c v ->
  assert (0 <= r && r < m);
  assert (0 <= c);
  assert (m * n <= Array.length a);
  ret (fun res -> assert (true))];;

(* Set every row. *)
let rec fill_rows (a : int array) (m : int) (n : int) (r : int) (v : int) : unit =
  if r < m then
    (set_row a m n r 0 v;
     fill_rows a m n (r + 1) v)
  else ()
[@@spec fun a m n r v ->
  assert (0 <= r);
  assert (m * n <= Array.length a);
  ret (fun res -> assert (true))];;

let fill (a : int array) (m : int) (n : int) (v : int) : unit =
  fill_rows a m n 0 v
[@@spec fun a m n v ->
  assert (m * n <= Array.length a);
  ret (fun res -> assert (true))];;


(* ---------------------------------------------------------------------- *)
(* In-place transpose of a square matrix                                  *)
(* ---------------------------------------------------------------------- *)

(* Swap [(r, c)] with [(c, r)] for each [c] above the diagonal in row [r]. *)
let rec transpose_inner (a : int array) (n : int) (r : int) (c : int) : unit =
  if c < n then
    (let x = mget a n n r c in
     let y = mget a n n c r in
     mset a n n r c y;
     mset a n n c r x;
     transpose_inner a n r (c + 1))
  else ()
[@@spec fun a n r c ->
  assert (0 <= r && r < n);
  assert (0 <= c);
  assert (n * n <= Array.length a);
  ret (fun res -> assert (true))];;

let rec transpose_rows (a : int array) (n : int) (r : int) : unit =
  if r < n then
    (transpose_inner a n r (r + 1);
     transpose_rows a n (r + 1))
  else ()
[@@spec fun a n r ->
  assert (0 <= r);
  assert (n * n <= Array.length a);
  ret (fun res -> assert (true))];;

let transpose (a : int array) (n : int) : unit =
  transpose_rows a n 0
[@@spec fun a n ->
  assert (n * n <= Array.length a);
  ret (fun res -> assert (true))];;
