module Nat : sig
  type o = O_
  type 'a s = S_ of 'a
  type one = o s
  type two = one s
  type three = two s
  type four = three s
  type _ nat = O : o nat | S : 'n nat -> 'n s nat
  val to_int : 'a nat -> int
  module type T = sig type t val wit : t nat end
  val of_int : int -> (module T)
end

module type T = Nat.T

module Vector : sig
  type (_, _) nlist =
      Nil : (Nat.o, 'a) nlist
    | Cons : 'a * ('n, 'a) nlist -> ('n Nat.s, 'a) nlist
  module Ops :
  sig
    val ( ==& ) : 'a -> ('b, 'a) nlist -> ('b Nat.s, 'a) nlist
    val ( ==! ) : (Nat.o, 'a) nlist
  end
  exception ArrayTooSmall
  exception ArrayTooBig
  val from_array : 'n Nat.nat -> 'a array -> ('n, 'a) nlist
end
