From Mtac2 Require Import Mtac2 Sorts MTele Specif Logic.
Import TeleNotation.

Set Printing Universes.

Mtac Do (M.inspect_mind nat).


Module TestMonoMono.

Inductive U1@{i} : Type@{i}.
Definition U1_mind := ltac:(mrun (M.inspect_mind U1)).


Inductive P1 (P: Type) : Type.
Definition P1_mind := ltac:(mrun (M.inspect_mind P1)).
Definition P1_mind_1_Prop := ltac:(mrun (M.inspect_mind (P1 Prop))).
Definition P1_mind_1_Set := ltac:(mrun (M.inspect_mind (P1 Set))).
Definition P1_mind_1_Type := ltac:(mrun (M.inspect_mind (P1 Type))).

Inductive I1 : forall (P: Type), Type :=.
Definition I1_mind := ltac:(mrun (M.inspect_mind I1)).
Definition I1_mind_1_Prop := ltac:(mrun (M.inspect_mind (I1 Prop))).
Definition I1_mind_1_Set := ltac:(mrun (M.inspect_mind (I1 Set))).
Definition I1_mind_1_Type := ltac:(mrun (M.inspect_mind (I1 Type))).

Inductive I1C1 : forall (P: Type), Type := i1c1 : I1C1 Type.
Definition I1C1_mind := ltac:(mrun (M.inspect_mind I1C1)).
Definition I1C1_mind_1_Prop := ltac:(mrun (M.inspect_mind (I1C1 Prop))).
Definition I1C1_mind_1_Set := ltac:(mrun (M.inspect_mind (I1C1 Set))).
Definition I1C1_mind_1_Type := ltac:(mrun (M.inspect_mind (I1C1 Type))).

Inductive I1C1' : forall (P: Type), Type := i1c1' T : I1C1' T.
Definition I1C1'_mind := ltac:(mrun (M.inspect_mind I1C1')).
Definition I1C1'_mind_1_Prop := ltac:(mrun (M.inspect_mind (I1C1' Prop))).
Definition I1C1'_mind_1_Set := ltac:(mrun (M.inspect_mind (I1C1' Set))).
Definition I1C1'_mind_1_Type := ltac:(mrun (M.inspect_mind (I1C1' Type))).

Inductive I2 : forall (P: Type), (P -> Type) -> Type :=.
Definition I2_mind := ltac:(mrun (M.inspect_mind I2)).
Definition I2_mind_1_Prop := ltac:(mrun (M.inspect_mind (I2 Prop))).
Definition I2_mind_1_Set := ltac:(mrun (M.inspect_mind (I2 Set))).
Definition I2_mind_1_Type := ltac:(mrun (M.inspect_mind (I2 Type))).
Definition I2_mind_2_Type := ltac:(mrun (M.inspect_mind (I2 Type (id)))).

Inductive P1I1 (P: Type) : (P -> Type) -> Type :=.
Definition P1I1_mind := ltac:(mrun (M.inspect_mind P1I1)).
Definition P1I1_mind_1_Prop := ltac:(mrun (M.inspect_mind (P1I1 Prop))).
Definition P1I1_mind_1_Set := ltac:(mrun (M.inspect_mind (P1I1 Set))).
Definition P1I1_mind_1_Type := ltac:(mrun (M.inspect_mind (P1I1 Type))).
Definition P1I1_mind_2_Type := ltac:(mrun (M.inspect_mind (P1I1 Type (id)))).

Polymorphic Inductive P1I1C1 (P: Type) : (P -> Type) -> Type := p1i1c1 : P1I1C1 P (fun p => unit).
Polymorphic Definition test := M.inspect_mind P1I1C1.
Definition P1I1C1_mind := ltac:(mrun (M.inspect_mind P1I1C1)).
Definition P1I1C1_mind_1_Prop := ltac:(mrun (M.inspect_mind (P1I1C1 Prop))).
Definition P1I1C1_mind_1_Set := ltac:(mrun (M.inspect_mind (P1I1C1 Set))).
Definition P1I1C1_mind_1_Type := ltac:(mrun (M.inspect_mind (P1I1C1 Type))).
Definition P1I1C1_mind_2_Type := ltac:(mrun (M.inspect_mind (P1I1C1 Type (id)))).

Inductive P1I1C1' (P: Type) : (P -> Type) -> Type := p1i1c1' (R : P -> Type) (p : P) (r : R p) : P1I1C1' P R.
Definition P1I1C1'_mind := ltac:(mrun (M.inspect_mind P1I1C1')).
Definition P1I1C1'_mind_1_Prop := ltac:(mrun (M.inspect_mind (P1I1C1' Prop))).
Definition P1I1C1'_mind_1_Set := ltac:(mrun (M.inspect_mind (P1I1C1' Set))).
Definition P1I1C1'_mind_1_Type := ltac:(mrun (M.inspect_mind (P1I1C1' Type))).
Definition P1I1C1'_mind_2_Type := ltac:(mrun (M.inspect_mind (P1I1C1' Type (id)))).


Inductive P2I1C1 (P: Type) (p: P) : P -> Type  := p2i1c1 : P2I1C1 P p p.
Definition P2I1C1_mind := ltac:(mrun (M.inspect_mind P2I1C1)).
Definition P2I1C1_mind_1_Prop := ltac:(mrun (M.inspect_mind (P2I1C1 Prop))).
Definition P2I1C1_mind_1_Set := ltac:(mrun (M.inspect_mind (P2I1C1 Set))).
Definition P2I1C1_mind_1_Type := ltac:(mrun (M.inspect_mind (P2I1C1 Type))).
Definition P2I1C1_mind_2_Type := ltac:(mrun (M.inspect_mind (P2I1C1 Type Type))).


Inductive P2C1 (P: Type) (R: P -> Type) : Type := p2c1 (p : P) (r : R p) : P2C1 P R.
Definition P2C1_mind := ltac:(mrun (M.inspect_mind P2C1)).
Definition P2C1_mind_1_Prop := ltac:(mrun (M.inspect_mind (P2C1 Prop))).
Definition P2C1_mind_1_Set := ltac:(mrun (M.inspect_mind (P2C1 Set))).
Definition P2C1_mind_1_Type := ltac:(mrun (M.inspect_mind (P2C1 Type))).
Definition P2C1_mind_2_Type := ltac:(mrun (M.inspect_mind (P2C1 Type (id)))).

End TestMonoMono.

Unset Strict Universe Declaration.

(* Universes *)
(* Mtac2Tests_inspect_4994 *)
(* Mtac2Tests_inspect_4995 *)
(* Mtac2Tests_inspect_5001 *)
(* Mtac2Tests_inspect_5002 *)
(* Mtac2Tests_inspect_5003 *)
(* Mtac2Tests_inspect_5007 *)
(* Mtac2Tests_inspect_5021 *)
(* Mtac2Tests_inspect_5022 *)
(* Mtac2Tests_inspect_5026 *)
(* Mtac2Tests_inspect_5027 *)
(* Mtac2Tests_inspect_5031 *)
(* Mtac2Tests_inspect_5032 *)
(* Mtac2Tests_inspect_5033 *)
(* Mtac2Tests_inspect_5034 *)
(* Mtac2Tests_inspect_5035 *)
(* Mtac2Tests_inspect_5036 *)
(* Mtac2Tests_inspect_5037 *)
(* Mtac2Tests_inspect_5040 *)
(* Mtac2Tests_inspect_5041 *)
(* Mtac2Tests_inspect_5045 *)
(* Mtac2Tests_inspect_5046 *)
(* Mtac2Tests_inspect_5047 *)
(* Mtac2Tests_inspect_5048 *)
(* Mtac2Tests_inspect_5049 *)
(* Mtac2Tests_inspect_5050 *)
(* Mtac2Tests_inspect_5051 *)
(* Mtac2Tests_inspect_5052 *)
(* Mtac2Tests_inspect_5053 *)
(* Mtac2Tests_inspect_5054 *)
(* Mtac2Tests_inspect_5055 *)
(* Mtac2Tests_inspect_5056 *)
(* Mtac2Tests_inspect_5057 *)
(* Mtac2Tests_inspect_5058 *)
(* Mtac2Tests_inspect_5059 *)
(* Mtac2Tests_inspect_5060 *)
(* Mtac2Tests_inspect_5061 *)
(* Mtac2Tests_inspect_5062 *)
(* Mtac2Tests_inspect_5063 *)
(* Mtac2Tests_inspect_5064 *)
(* Mtac2Tests_inspect_5065 *)
(* Mtac2Tests_inspect_5066 *)
(* . *)
(* Definition X := forall *)
(*     (_ : forall (A : Type@{Mtac2Tests_inspect_4994}) (_ : forall _ : A, Type@{Mtac2Tests_inspect_4995}), *)
(*          Type@{max(Mtac2Tests_inspect_4994,Mtac2Tests_inspect_4995)}) (A : Type@{Mtac2Tests_inspect_4994}) *)
(*     (_ : forall _ : A, Type@{Mtac2Tests_inspect_4995}), *)
(*   mprod@{Mtac2Tests_inspect_5036 Mtac2Tests_inspect_5037} *)
(*     (mlist@{Mtac2Tests_inspect_5035} *)
(*        (constr_def@{Mtac2Tests_inspect_5031 Mtac2Tests_inspect_5032 Mtac2Tests_inspect_5033 Mtac2Tests_inspect_5034} *)
(*                   mBase@{Mtac2Tests_inspect_5007})) unit *)
(* . *)

(* Definition Y := @constrs_defs_in_ctx@{Mtac2Tests_inspect_5047 Mtac2Tests_inspect_5048 Mtac2Tests_inspect_5049 *)
(*     Mtac2Tests_inspect_5050 Mtac2Tests_inspect_5051 Mtac2Tests_inspect_5052 Mtac2Tests_inspect_5053 *)
(*     Mtac2Tests_inspect_5054 Mtac2Tests_inspect_5055 Mtac2Tests_inspect_5056 Mtac2Tests_inspect_5057 *)
(*     Mtac2Tests_inspect_5058 Mtac2Tests_inspect_5059 Mtac2Tests_inspect_5060 Mtac2Tests_inspect_5061 *)
(*     Mtac2Tests_inspect_5062 Mtac2Tests_inspect_5063 Mtac2Tests_inspect_5064 Mtac2Tests_inspect_5065 *)
(*     Mtac2Tests_inspect_5066} *)
(*     (@mTele@{Mtac2Tests_inspect_5003} Type@{Mtac2Tests_inspect_4994} *)
(*        (fun A : Type@{Mtac2Tests_inspect_4994} => *)
(*         @mTele@{Mtac2Tests_inspect_5002} (forall _ : A, Type@{Mtac2Tests_inspect_4995}) *)
(*           (fun _ : forall _ : A, Type@{Mtac2Tests_inspect_4995} => mBase@{Mtac2Tests_inspect_5001}))) *)
(*     (@mcons@{Mtac2Tests_inspect_5046} *)
(*        (ind_def@{Mtac2Tests_inspect_5040 Mtac2Tests_inspect_5041 Mtac2Tests_inspect_5057 Mtac2Tests_inspect_5058 *)
(*           Mtac2Tests_inspect_5062} *)
(*           (@mTele@{Mtac2Tests_inspect_5003} Type@{Mtac2Tests_inspect_4994} *)
(*              (fun A : Type@{Mtac2Tests_inspect_4994} => *)
(*               @mTele@{Mtac2Tests_inspect_5002} (forall _ : A, Type@{Mtac2Tests_inspect_4995}) *)
(*                 (fun _ : forall _ : A, Type@{Mtac2Tests_inspect_4995} => mBase@{Mtac2Tests_inspect_5001})))) *)
(*        (Build_ind_def@{Mtac2Tests_inspect_5026 Mtac2Tests_inspect_5027 Mtac2Tests_inspect_5057 *)
(*           Mtac2Tests_inspect_5058 Mtac2Tests_inspect_5062} *)
(*           (@mTele@{Mtac2Tests_inspect_5003} Type@{Mtac2Tests_inspect_4994} *)
(*              (fun A : Type@{Mtac2Tests_inspect_4994} => *)
(*               @mTele@{Mtac2Tests_inspect_5002} (forall _ : A, Type@{Mtac2Tests_inspect_4995}) *)
(*                 (fun _ : forall _ : A, Type@{Mtac2Tests_inspect_4995} => mBase@{Mtac2Tests_inspect_5001}))) *)
(*           (String (Ascii.Ascii true false true true false true true false) *)
(*              (String (Ascii.Ascii true true false false true true true false) *)
(*                 (String (Ascii.Ascii true false false true false true true false) *)
(*                    (String (Ascii.Ascii true true true false false true true false) *)
(*                       (String (Ascii.Ascii false false true false true false true false) EmptyString))))) *)
(*           (Build_ind_sig@{Mtac2Tests_inspect_5021 Mtac2Tests_inspect_5022 Mtac2Tests_inspect_5057 *)
(*              Mtac2Tests_inspect_5058 Mtac2Tests_inspect_5062} *)
(*              (@mTele@{Mtac2Tests_inspect_5003} Type@{Mtac2Tests_inspect_4994} *)
(*                 (fun A : Type@{Mtac2Tests_inspect_4994} => *)
(*                  @mTele@{Mtac2Tests_inspect_5002} (forall _ : A, Type@{Mtac2Tests_inspect_4995}) *)
(*                    (fun _ : forall _ : A, Type@{Mtac2Tests_inspect_4995} => mBase@{Mtac2Tests_inspect_5001}))) *)
(*              S.Type_sort *)
(*              (fun (A : Type@{Mtac2Tests_inspect_4994}) (_ : forall _ : A, Type@{Mtac2Tests_inspect_4995}) => *)
(*               mBase@{Mtac2Tests_inspect_5007}))) *)
(*        (@mnil@{Mtac2Tests_inspect_5045} *)
(*           (ind_def@{Mtac2Tests_inspect_5040 Mtac2Tests_inspect_5041 Mtac2Tests_inspect_5057 Mtac2Tests_inspect_5058 *)
(*              Mtac2Tests_inspect_5062} *)
(*              (@mTele@{Mtac2Tests_inspect_5003} Type@{Mtac2Tests_inspect_4994} *)
(*                 (fun A : Type@{Mtac2Tests_inspect_4994} => *)
(*                  @mTele@{Mtac2Tests_inspect_5002} (forall _ : A, Type@{Mtac2Tests_inspect_4995}) *)
(*                        (fun _ : forall _ : A, Type@{Mtac2Tests_inspect_4995} => mBase@{Mtac2Tests_inspect_5001})))))) *)
(* . *)

(* Definition X' := Eval compute in X. *)
(* Definition Y' := Eval compute in Y. *)

(* Print Universes. *)
(* Print Universes Subgraph ( *)
(* Mtac2Tests_inspect_4994 *)
(* Mtac2Tests_inspect_4995 *)
(* Mtac2Tests_inspect_5054 *)
(* ) *)
(*  "test.dot". *)
(* (* Definition bla : X' = Y' := ltac:(refine eq_refl). *) *)

(* Set Printing All. *)
Mtac Do (M.inspect_mind (@msigT)).

Set Printing All.
Mtac Do (M.inspect_mind (@meq)).

Universes
U18514
U18537
U18538
U18539
U18540
U18541
U18542
U18543
U18544
U18545
U18546
U18547
U18548
U18549
U18550
U18551
U18552
U18553
U18554
U18555
U18556
U18562
U18563
U18564
U18569
U18570
U18576
U18633
U18634
U18635
U18636
U18637
U18638
U18639
U18640
U18641
U18642
U18643
U18644
U18645
U18646
U18648
U18650
U18651
.

Mtac Do (M.inspect_mind (@meq)).

Definition meq_mind := ltac:(mrun (M.inspect_mind (@meq))).

Polymorphic Inductive many_indices (A : Type) : forall x y : A, x =m= y -> Type :=.

Mtac Do (M.inspect_mind (@many_indices)).
