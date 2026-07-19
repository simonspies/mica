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
