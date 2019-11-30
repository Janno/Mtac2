module Nat = struct
  type o = O_
  type 'a s = S_ of 'a

  type one = o s
  type two = one s
  type three = two s
  type four = three s

  type _ nat =
    | O : o nat
    | S : 'n nat -> ('n s) nat

  let to_int : type n. n nat -> int = fun n ->
    let rec to_int_acc : type n. int -> n nat -> int = fun acc -> function
      | O -> acc
      | S n -> to_int_acc (acc + 1) n
    in to_int_acc 0 n

  module type T =
  sig
    type t
    val wit : t nat
  end

  let rec of_int : int -> (module T) = fun n ->
    if n = 0 then
      (module struct
        type t = o
        let wit = O
      end) else
      let (module M) = of_int (n - 1) in
      (module struct
        type t = M.t s
        let wit = S M.wit
      end)

end

module type T = Nat.T

module Vector = struct
  open Nat

  type (_, _) nlist =
    | Nil  : (o, 'a) nlist
    | Cons : 'a * ('n, 'a) nlist -> ('n s, 'a) nlist

  module Ops = struct
    let ( ==& ) : type n. 'a -> (n, 'a) nlist -> (n s, 'a) nlist = fun x y -> Cons (x, y)
    let ( ==! ) : (Nat.o, 'a) nlist = Nil
  end

  open Ops

  exception ArrayTooSmall
  exception ArrayTooBig
  let from_array : type n. n nat -> 'a array -> (n, 'a) nlist = fun n arr ->
    let m = Nat.to_int n in
    if Array.length arr > m then raise ArrayTooBig
    else if Array.length arr < m then raise ArrayTooSmall
    else
      let rec from_array : type n. int -> n nat -> (n, 'a) nlist = fun i n ->
        match n with
        | O -> (==!)
        | S(n) -> Array.get arr i ==& from_array (i+1) n
      in from_array 0 n
end
