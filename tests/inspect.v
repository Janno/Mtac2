From Mtac2 Require Import Mtac2 Sorts MTele Specif Logic.

Mtac Do (M.inspect_mind nat).

Mtac Do (M.inspect_mind (@msigT)).

Mtac Do (M.inspect_mind (@meq)).


Polymorphic Inductive many_indices (A : Type) : forall x y : A, x =m= y -> Type :=.

Mtac Do (M.inspect_mind (@many_indices)).
