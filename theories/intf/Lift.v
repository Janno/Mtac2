From Mtac2.intf Require Import M.

Set Universe Polymorphism.


(** Execution of tactics at unification *)
Polymorphic Definition lift {A} (f: M A) (v : A) := A.
