From Mtac2 Require Import Mtac2 Sorts MTele Specif NEList.
Import M.notations.
Definition test := c <- M.declare dok_Definition "bla" false 1; M.print_term c.
Goal unit.
  MProof.
  (* TODO: inlining test here used to *not* work because of universes. *)
  c <- M.declare dok_Definition "bla" false 1; M.print_term c.
Qed.

Goal unit.
MProof. test. Qed.

Typeclasses eauto := debug.
Structure ST := mkS { s : nat }.

Require Mtac2.lib.List.
Import Mtac2.lib.List.ListNotations.
Definition cs := c1 <- M.declare dok_CanonicalStructure "bla" false (fun (x : nat) => (fun x => mkS x) x);
                    c2 <- M.declare dok_Definition "bli" true c1;
                    M.declare_implicits c2 [m: ia_MaximallyImplicit];;
                    M.ret tt.

Compute ltac:(mrun cs).
Print bla.
Print Coercions.
Print Canonical Projections.
Print bli.
Fail Compute (bli 1).
Compute (@bli 1).

Module DeclareTest.
  Fail Compute ltac:(mrun (M.declare_implicits (1+1) [m:])).
  Local Arguments Nat.add {_ _}.
  Fail Compute ltac:(mrun (M.declare_implicits (Nat.add) [m:])).
  Fail Compute ltac:(mrun (M.declare_implicits (Nat.add (n:=1)) [m:])).
  Compute ltac:(mrun (M.declare_implicits (@Nat.add) [m:])).
  Compute ltac:(mrun (M.declare_implicits (@Nat.add) [m: ia_MaximallyImplicit | ia_MaximallyImplicit])).
  Definition should_work0 := Nat.add (n:=3) (m :=2).
  Compute ltac:(mrun (M.declare_implicits (@Nat.add) [m: ia_Implicit | ia_Explicit])).
  Definition should_work2 := Nat.add (n:=3) 2.
  Compute ltac:(mrun (M.declare_implicits (@Nat.add) [m: ia_Explicit | ia_MaximallyImplicit])).
  Definition should_work1 := Nat.add (m :=3) 2.
  Compute ltac:(mrun (M.declare_implicits (@Nat.add) [m: ia_Explicit | ia_Explicit])).
  Definition should_work := Nat.add 3 2.
End DeclareTest.
Require Import Strings.String.
Import M.notations.

Fixpoint defineN (n : nat) : M unit :=
  match n with
  | 0 => M.ret tt
  | S n =>
    s <- M.pretty_print n;
    M.declare dok_Definition ("NAT"++s)%string false n;;
    defineN n
  end.
Fail Print NAT0.
Compute ltac:(mrun (defineN 4)).

Print NAT0.
Print NAT1.
Print NAT2.
Print NAT3.
Fail Print NAT4.

Set Printing All. (* nasty *)
Fail Compute ltac:(mrun (defineN 4)).
Search "NAT". (* Now there are no definitions like "NATS (S O)" *)
Fail Compute ltac:(mrun (M.get_reference "NATS O")).

Definition ev := c <- M.declare dok_Definition "_" true (S O); M.print_term c.
Compute (M.eval ev). (* it was failing *)

Unset Printing All.

(* ouch, there should be a catchable error. but what about previously declared objects? *)
Definition alrdecl := mtry defineN 5 with [?s] AlreadyDeclared s => M.print s;; M.ret tt end.
Compute ltac:(mrun alrdecl).

Print NAT4. (* definitions before the failing one are declared. *)

(* we should check that the terms are closed w.r.t. section variables *)
(* JANNO: for now we just raise an catchable exception. *)
Fail Compute fun x y =>
          ltac:(mrun (
                    mtry
                      M.declare dok_Definition "lenS" true (Le.le_n_S x y);; M.ret tt
                      with | UnboundVar => M.failwith "This must fail" | _ => M.ret tt end
               )).

(* This used to fail because of weird universe issues. *)
Compute ltac:(mrun (c <- M.declare dok_Definition "blu" true (Le.le_n_S); M.print_term c)).
Definition decl_blu := (c <- M.declare dok_Definition "blu" true (Le.le_n_S); M.print_term c).
(* This now fails because the previous failure no longer exists and [blu] is declared. *)
Fail Compute ltac:(mrun decl_blu).

Print blu.


Definition backtracking_test :=
  mtry
    M.declare dok_Definition "newone" false tt;;
    M.declare dok_Definition "blu" false tt;;
    M.ret tt
  with [?s] AlreadyDeclared s => M.ret tt end.

Compute ltac:(mrun backtracking_test).

Print newone. (* is this expected? or should the "state" of definitions be also backtracked? *)
Print blu.


Module Inductives.
  Set Polymorphic Inductive Cumulativity.
  Unset Universe Minimization ToSet.
  Import ListNotations.

Definition typ_of {A : Type} (a : A) := A.
Import TeleNotation.
Notation P := [tele (T : Type) (k : nat)].
Module M1.
  Notation I2 := {| ind_def_name := "blubb__";
                    ind_def_sig :=
                      {| ind_sig_sort := Propₛ;
                         ind_sig_arity := fun T k => [tele _ : k = k]
                      |}
                 |}.
  Program Definition mind_test := (M.declare_mind false P ([ne: I2])).
  Eval cbv beta iota fix delta [mfold_right typ_of] in typ_of mind_test.
  (* Eval cbv beta iota fix delta [mfold_right typ_of] in *)

  Definition testprog :=
    mind_test
      (fun (I2 : forall T k, k = k -> _) T k =>
          mnil
      ).

  Eval cbv in testprog.

  Eval cbn in ltac:(mrun(
                        let t := dreduce ((@S.Fun), testprog) testprog in
                        t
                   )).

End M1.

Module M2.
  Notation I2 := {| ind_def_name := "blubb__";
                    ind_def_sig :=
                      {| ind_sig_sort := Propₛ;
                         ind_sig_arity := fun T k => [tele _ : k = k]
                      |}
                 |}.
  Program Definition mind_test := (M.declare_mind false P ([ne: I2])).
  Eval cbv beta iota fix delta [mfold_right typ_of] in typ_of mind_test.
  (* Eval cbv beta iota fix delta [mfold_right typ_of] in *)

  Program Definition testprog :=
    mind_test
      (fun I2 T k =>
          [m:
             {| constr_def_name := "c1";
                constr_def_tele := [tele _ : T];
                constr_def_indices := (S.Fun (sort:=Typeₛ) (fun t => ((mexistT _ eq_refl tt))));
             |}
          ]
      ).

  Eval cbv in testprog.

  Eval cbn in ltac:(mrun(
                        let t := dreduce ((@S.Fun), testprog) testprog in
                        t
                   )).

End M2.

Module M3.

  Notation I1 :=
    {| ind_def_name := "bla__";
       ind_def_sig := {| ind_sig_sort := Typeₛ;
                         ind_sig_arity := fun T k => [tele]
                      |}
    |}.
  Notation I2 :=
    {|
      ind_def_name := "blubb__";
      ind_def_sig := {| ind_sig_sort := Propₛ;
                        ind_sig_arity := fun T k => [tele]
                     |}
    |}.
Program Definition mind_test := (M.declare_mind false P ([ne: I1,  I2])).
Eval cbv beta iota fix delta [mfold_right typ_of] in typ_of mind_test.
(* Eval cbv beta iota fix delta [mfold_right typ_of] in *)

Program Definition testprog :=
    mind_test
    (fun I1 I2 T k =>
       (m:
          [m:
             {| constr_def_name := "c1";
                constr_def_tele := mTele (fun t : I2 T k => mBase);
                constr_def_indices := (S.Fun (sort:=Typeₛ) (fun t => tt))
             |}
          ];
          [m:
             {| constr_def_name := "c2";
                constr_def_tele := mTele (fun t : I2 T k => mBase);
                constr_def_indices := (S.Fun (sort:=Typeₛ) (fun t => tt))
             |}
          ]
        )
    ).

Eval cbn in ltac:(mrun(
                      let t := dreduce ((@S.Fun), testprog) testprog in
                      t
    )).

End M3.

Module M4.
  Notation I1 :=
    {| ind_def_name := "bla__";
       ind_def_sig := {| ind_sig_sort := Typeₛ;
                         ind_sig_arity := fun T k => [tele x y : nat]
                      |}
    |}.
  Notation I2 :=
    {|
      ind_def_name := "blubb__";
      ind_def_sig := {| ind_sig_sort := Propₛ;
                        ind_sig_arity := fun T k => [tele _ : k = k]
                     |}
    |}.

  Program Definition mind_test := (M.declare_mind false P ([ne: I1,  I2])).
  Eval cbv beta iota fix delta [mfold_right typ_of] in typ_of mind_test.
  (* Eval cbv beta iota fix delta [mfold_right typ_of] in *)

  Program Definition testprog :=
    mind_test
      (fun I1 I2 T k =>
         (m:
            [m:
               {| constr_def_name := "c1";
                  constr_def_tele := [tele _ : I2 T k eq_refl];
                  constr_def_indices := (S.Fun (sort:=Typeₛ) (fun t => (mexistT _ 1 (mexistT _ 2 tt))))
               |}
            ];
          mnil)
      ).
  Eval cbv in testprog.

  Eval cbn in ltac:(mrun(
                        let t := dreduce ((@S.Fun), testprog) testprog in
                        t
                   )).

End M4.
End Inductives.
