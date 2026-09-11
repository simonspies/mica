let failwith = Stdlib.failwith
let invalid_arg = Stdlib.invalid_arg

type 'a list = [] | (::) of 'a * 'a list
type 'a option = None | Some of 'a

let rec list_length = function
  | [] -> 0
  | _ :: tail -> 1 + list_length tail

let rec list_append left right =
  match left with
  | [] -> right
  | head :: tail -> head :: list_append tail right

let list_rev value =
  let rec loop acc = function
    | [] -> acc
    | head :: tail -> loop (head :: acc) tail
  in
  loop [] value

let ( @ ) = list_append

module List = struct
  let length = list_length
  let append = list_append
  let rev = list_rev
end

module Option = struct
  let is_some = function Some _ -> true | None -> false
  let is_none = function None -> true | Some _ -> false
  let value = function Some value -> value | None -> invalid_arg "Option.value"
end

module String = struct
  let length = Stdlib.String.length
  let get = Stdlib.String.get
  let sub = Stdlib.String.sub
  let cat = Stdlib.String.cat
  let equal = Stdlib.String.equal
  let starts_with prefix s = Stdlib.String.starts_with ~prefix s
  let ends_with suffix s = Stdlib.String.ends_with ~suffix s
end

module Char = struct
  let code = Stdlib.Char.code
  let chr = Stdlib.Char.chr
  let equal = Stdlib.Char.equal
end

module Int = struct
  let min = Stdlib.min
  let max = Stdlib.max
end

module Int32 = struct
  let zero = Stdlib.Int32.zero
  let one = Stdlib.Int32.one
  let minus_one = Stdlib.Int32.minus_one
  let min_int = Stdlib.Int32.min_int
  let max_int = Stdlib.Int32.max_int
  let neg = Stdlib.Int32.neg
  let lognot = Stdlib.Int32.lognot
  let add = Stdlib.Int32.add
  let sub = Stdlib.Int32.sub
  let mul = Stdlib.Int32.mul
  let div = Stdlib.Int32.div
  let unsigned_div = Stdlib.Int32.unsigned_div
  let rem = Stdlib.Int32.rem
  let unsigned_rem = Stdlib.Int32.unsigned_rem
  let logand = Stdlib.Int32.logand
  let logor = Stdlib.Int32.logor
  let logxor = Stdlib.Int32.logxor
  let min = Stdlib.Int32.min
  let max = Stdlib.Int32.max
  let compare = Stdlib.Int32.compare
  let unsigned_compare = Stdlib.Int32.unsigned_compare
  let equal = Stdlib.Int32.equal
  let shift_left = Stdlib.Int32.shift_left
  let shift_right = Stdlib.Int32.shift_right
  let shift_right_logical = Stdlib.Int32.shift_right_logical
  let of_int = Stdlib.Int32.of_int
  let to_int = Stdlib.Int32.to_int
end

module Int64 = struct
  let zero = Stdlib.Int64.zero
  let one = Stdlib.Int64.one
  let minus_one = Stdlib.Int64.minus_one
  let min_int = Stdlib.Int64.min_int
  let max_int = Stdlib.Int64.max_int
  let neg = Stdlib.Int64.neg
  let lognot = Stdlib.Int64.lognot
  let add = Stdlib.Int64.add
  let sub = Stdlib.Int64.sub
  let mul = Stdlib.Int64.mul
  let div = Stdlib.Int64.div
  let unsigned_div = Stdlib.Int64.unsigned_div
  let rem = Stdlib.Int64.rem
  let unsigned_rem = Stdlib.Int64.unsigned_rem
  let logand = Stdlib.Int64.logand
  let logor = Stdlib.Int64.logor
  let logxor = Stdlib.Int64.logxor
  let min = Stdlib.Int64.min
  let max = Stdlib.Int64.max
  let compare = Stdlib.Int64.compare
  let unsigned_compare = Stdlib.Int64.unsigned_compare
  let equal = Stdlib.Int64.equal
  let shift_left = Stdlib.Int64.shift_left
  let shift_right = Stdlib.Int64.shift_right
  let shift_right_logical = Stdlib.Int64.shift_right_logical
  let of_int = Stdlib.Int64.of_int
  let to_int = Stdlib.Int64.to_int
  let of_int32 = Stdlib.Int64.of_int32
  let to_int32 = Stdlib.Int64.to_int32
end

module Float = struct
  let abs = Stdlib.Float.abs
  let neg = Stdlib.Float.neg
  let sqrt = Stdlib.Float.sqrt
  let is_nan = Stdlib.Float.is_nan
  let is_finite = Stdlib.Float.is_finite
  let of_int = Stdlib.Float.of_int
  let add = Stdlib.Float.add
  let sub = Stdlib.Float.sub
  let mul = Stdlib.Float.mul
  let div = Stdlib.Float.div
  let min = Stdlib.Float.min
  let max = Stdlib.Float.max
  let equal = Stdlib.Float.equal
  let lt (x : float) y = x < y
  let le (x : float) y = x <= y
  let nan = Stdlib.Float.nan
  let infinity = Stdlib.Float.infinity
  let neg_infinity = Stdlib.Float.neg_infinity
end

module Array = struct
  let make = Stdlib.Array.make
  let length = Stdlib.Array.length
  let get = Stdlib.Array.get
  let set = Stdlib.Array.set
end

module Iarray = struct
  let make n x : 'a iarray = Stdlib.Iarray.init n (fun _ -> x)
  let length = Stdlib.Iarray.length
  let get = Stdlib.Iarray.get

  (* Functional update: vectors are immutable, so [set] copies. *)
  let set (v : 'a iarray) i x : 'a iarray =
    let a = Stdlib.Iarray.to_array v in
    Stdlib.Array.set a i x;
    Stdlib.Iarray.of_array a
end

type 'a vec = 'a iarray
module Vec = Iarray

module Range = struct
  let rec all a b f = a >= b || (f a && all (a + 1) b f)
  let rec exists a b f = a < b && (f a || exists (a + 1) b f)
end
