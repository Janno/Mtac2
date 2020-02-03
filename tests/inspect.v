From Mtac2 Require Import Mtac2 Sorts MTele Specif Logic NEList.
From Coq Require Vector.
Import TeleNotation.

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


Inductive P2I1C1M2T1 (P: Type) (p: P) : P -> Type  :=
  p2i1c1m2t1 : P2I1C1M2T2 P p p -> P2I1C1M2T1 P p p
with P2I1C1M2T2 (P: Type) (p: P) : P -> Type  :=
  p2i1c1m2t2 : P2I1C1M2T1 P p p -> P2I1C1M2T2 P p p
.
Definition P2I1C1M2T1_mind := ltac:(mrun (M.inspect_mind P2I1C1M2T1)).

Inductive P2I1C2M2T1 (P: Type) (p: P) : P -> Type  :=
  p2i1c2m2t1_1 : P2I1C2M2T2 P p p -> P2I1C2M2T1 P p p
| p2i1c2m2t1_2 : nat -> P2I1C2M2T1 P p p
with P2I1C2M2T2 (P: Type) (p: P) : P -> Type  :=
  p2i1c2m2t2_1 : P2I1C2M2T1 P p p -> P2I1C2M2T2 P p p
| p2i1c2m2t2_2 : bool -> P2I1C2M2T2 P p p
.
Definition P2I1C2M2T1_mind := ltac:(mrun (M.inspect_mind P2I1C2M2T1)).


Inductive P2C1 (P: Type) (R: P -> Type) : Type := p2c1 (p : P) (r : R p) : P2C1 P R.
Definition P2C1_mind := ltac:(mrun (M.inspect_mind P2C1)).
Definition P2C1_mind_1_Prop := ltac:(mrun (M.inspect_mind (P2C1 Prop))).
Definition P2C1_mind_1_Set := ltac:(mrun (M.inspect_mind (P2C1 Set))).
Definition P2C1_mind_1_Type := ltac:(mrun (M.inspect_mind (P2C1 Type))).
Definition P2C1_mind_2_Type := ltac:(mrun (M.inspect_mind (P2C1 Type (id)))).

End TestMonoMono.

Mtac Do (M.inspect_mind (@msigT)).

Mtac Do (M.inspect_mind (@meq)).

Mtac Do (M.inspect_mind (@meq)).

Definition meq_mind := ltac:(mrun (M.inspect_mind (@meq))).

Polymorphic Inductive many_indices (A : Type) : forall x y : A, x =m= y -> Type :=.

Mtac Do (M.inspect_mind (@many_indices)).


Module Matches.
  Notation "'t1'" := (match 1 with | 0 => false | _ => true end).
  Notation t1_tgt :=
    (
      Match.Build_Val
        (Mutual.Build_Nth
           (Mutual.Build_Val
              (Mutual.Build_Def
                 false
                 [tele ]
                 [ne:Inductive.Build_Def
                       [tele ]
                       "nat"
                       (Inductive.Build_Sig [tele ] Typeₛ [tele ])
                 ]
                 (fun nat : Set =>
                    [m: Constructor.Par.Build_Def [tele ] [tele ] "O" [tele ] tt
                    | Constructor.Par.Build_Def [tele ] [tele ] "S" [tele _ : nat ] (fun _ : nat => tt)])) nat
              (m:0; S; tt))
           0
           0
           0
        )
        tt
        tt
        1
        Typeₛ
        (fun _ : nat => bool)
        (m:false; fun _ : nat => true; tt)
    ).

  Mtac Do (M.inspect_match t1).
  Definition t1_repr := ltac:(mrun (M.inspect_match t1)).
  Definition t1_correct : (t1_repr =m= t1_tgt) := meq_refl.

  Import Vector.

  Parameter n : nat.
  Parameter T : Type.
  Parameter v : Vector.t T (S n).
  Notation "'t2'" := (
                  match v in Vector.t _ k return match k with 0 => unit | S _ => T end with
                  | Vector.nil _ => tt
                  | Vector.cons _ x _ _ => x
                  end
                 ).

  Mtac Do (
         m <- M.inspect_match t2;
         t2' <- M.build_match m;
         match Match.sort m as s return forall T : s, T -> M unit with
         | Propₛ => fun _ _ => M.failwith "wrong sort"
         | Typeₛ =>
           fun T2' t2' =>
             oeq <- M.unify T2' _ UniCoq;
             match oeq with
             | mNone => M.failwith "wrong type"
             | mSome eq =>
               match eq in _ =m= X return X -> M unit with
               | meq_refl => fun t2_ => M.unify_or_fail UniMatchNoRed t2_ t2';; M.ret tt
               end t2
             end
         end _ t2'
       )%MC.

End Matches.
