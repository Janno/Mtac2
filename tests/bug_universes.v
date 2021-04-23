From Mtac2 Require Import Mtac2.

(* Local Close Scope tactic_scope. *)
(* Inductive Inhabited (T: Type) : Prop := inhabits (t : T). *)
(* Polymorphic Inductive SpecificType@{u} : Prop := SpecificValue. *)
(* Definition inhabit (T: Type) : M (Inhabited T) := *)
(* let value_of := *)
(*     mfix1 go (T: Type) : M T := *)
(*       mmatch T in Type as T return M T with *)
(*       | [? L R] (L * R)%type => l <- go L; r <- go R; M.ret (l, r) *)
(*       | SpecificType : Type => M.ret SpecificValue *)
(*       end *)
(* in *)
(*   v <- value_of T; *)
(*   M.ret (inhabits T v). *)

(* Monomorphic Universes x y z. *)

(* Mtac Do inhabit (SpecificType@{x} * SpecificType@{y} * SpecificType@{z}) >>= M.print_term. *)
(* Set Printing Universes. *)
(* Mtac Do inhabit (SpecificType@{x} * SpecificType@{y} * SpecificType@{z}) >>= M.print_term. *)

(* Monomorphic Universes a b c. *)
(* Monomorphic Constraint a < b. *)
(* Set Unicoq Debug. *)
(* Fail Mtac Do inhabit (SpecificType@{a} * SpecificType@{b} * SpecificType@{c}) >>= M.print_term. *)

(* Definition result := *)
(*   ltac:(mrun (inhabit (SpecificType@{x} * SpecificType@{y} * SpecificType@{z}))). *)
(* Print result. *)

(* Definition inhabit'@{u+} (T: Type) : M (Inhabited T) := *)
(* let value_of := *)
(*     mfix1 go (T: Type) : M T := *)
(*       mmatch T in Type as T return M T with *)
(*       | [? L R] (L * R)%type => l <- go L; r <- go R; M.ret (l, r) *)
(*       | SpecificType@{u} : Type => M.ret SpecificValue *)
(*       end *)
(* in *)
(*   v <- value_of T; *)
(*   M.ret (inhabits T v). *)

(* Monomorphic Universes x' y' z'. *)
(* Unset Unicoq Debug. *)
(* Set Unicoq Trace. *)
(* Definition result' := *)
(*   ltac:(mrun (inhabit' (SpecificType@{x'} * SpecificType@{y'} * SpecificType@{z'}))). *)
(* Print result'. *)

(* Polymorphic Definition value_of@{u+} := *)
(*   mfix1 go (T: Type) : M T := *)
(*     mmatch T in Type as T return M T with *)
(*     | [? L R] (L * R)%type => l <- go L; r <- go R; M.ret (l, r) *)
(*     | SpecificType@{u} : Type => M.ret SpecificValue *)
(*   end. *)

(* CoInductive Refresh (Out : Prop) : Prop := *)
(* { refresh_rec : @Refresh Out *)
(* ; refresh_body :  Out -> Out *)
(* }. *)

(* Polymorphic CoFixpoint refresh_value_of@{u+} := *)
(*   {| refresh_rec := refresh_value_of *)
(*   ;  refresh_body := fun go (T: Type) => *)
(*         mmatch T in Type as T return M T with *)
(*         | [? L R] (L * R)%type => l <- go L; r <- go R; M.ret (l, r) *)
(*         | SpecificType@{u} : Type => M.ret SpecificValue *)
(*      end *)
(*   |}. *)

(* Definition refresh_prim {A} : A -> M A. Admitted. *)

(* Definition refresh {A} {B: A -> Type} : *)
(*   Refresh (forall (a : A), M (B a)) -> forall a, M (B a) := *)
(*   mfix2 go (t : Refresh (forall (a : A), M (B a))) (a : A) : M (B a) := *)
(*     let '{|refresh_rec := rec; refresh_body := body|} := t in *)
(*     rec <- refresh_prim rec; *)
(*     body (go rec) a. *)

(* Definition value_of_fixed : forall T, M T := *)
(*   refresh refresh_value_of. *)



(* Set Printing Universes. *)
(* Definition test (T : Type) : M T := *)
(*   mmatch Set return M T with *)
(*   | T =>[eq] match eq in _ =m= X return M X with | meq_refl => M.ret unit end *)
(*   end. *)

(* Mtac Do test. *)

Set Universe Polymorphism.

(* Demonstrate that id indeed has the right type *)
Definition test@{i j} : Type@{i} -> Type@{max(i,j)} := id.

(* Demonstrate that ltac gets it right *)
Lemma testL@{i j} : Type@{i} -> Type@{max(i,j)}.
Proof. exact id. Qed.

(* M.ret somehow works in 8.8 *)
Lemma testM@{i j} : Type@{i} -> Type@{max(i,j)}.
MProof.
M.ret id.
Qed.

(* runTac works too *)
Lemma testMTac@{i j} : Type@{i} -> Type@{max(i,j)}.
MProof.
T.exact id.
Qed.

(* apply doesn't generate a new universe index (it used to be the case) *)
Lemma testMTacApply@{i j} : Type@{i} -> Type@{max(i,j)}.
MProof.
T.apply (@id).
Qed.

(* and ltac's 8.8  doesn't do that either *)
Lemma testLApply@{i j} : Type@{i} -> Type@{max(i,j)}.
Proof. apply @id. Qed.

Notation "p '=e>' b" := (pbase p%core (fun _ => b%core) UniEvarconv)
  (no associativity, at level 201) : pattern_scope.
Notation "p '=e>' [ H ] b" := (pbase p%core (fun H => b%core) UniEvarconv)
  (no associativity, at level 201, H at next level) : pattern_scope.

Definition test_match@{k m+} {A:Type@{k}} (x:A) : tactic :=
  mmatch A with
  | [? B:Type@{m}] B =c> T.exact x
  end.


Lemma testMmatch@{i j} : Type@{i} -> Type@{max(i,j)}.
MProof.
test_match (fun x=>x).
Qed.

Lemma testMmatch'@{i j} : Type@{i} -> Type@{j}.
MProof.
test_match (fun x=>x).
Qed.
Print testMmatch.
Print testMmatch'.

Definition testdef : Type -> Type := fun x=>x.
Lemma testret : Type -> Type.
MProof.
M.ret (fun x=>x).
Qed. (* If this fails we likely swapped LHS & RHS of the cumulative unification in [ifM] *)
Print testret.

Lemma testexact : Type -> Type.
MProof.
T.exact (fun x=>x).
Qed.
About testexact.


(* The code below tests that we correctly unify the type of the mtac program with the conclusion.
   If it fails, we either do not unify them at all or we messed up the order of the cumulative unification.
 *)
Module ifM.
  #[local] Set Polymorphic Inductive Cumulativity.

  Polymorphic Inductive tree@{i j} : Type@{j} :=
  | Node : tree -> tree -> tree
  | Leaf (T: Type@{i}) : tree.

  Polymorphic Definition mk_tree@{i j +} : forall (n:nat), M tree :=
    mfix1 go (n : nat) : M tree :=
      match n with
      | 0 => M.ret@{j} (Leaf Type@{i})
      | S n =>
        l <- go n;
        r <- go n;
        M.ret (Node l r)
      end%MC.

  Monomorphic Universes k1 k2 k3 k4.
  Goal tree.
    mrun (mk_tree@{k1 k2 k3 k4} 1).
  Qed.
End ifM.
