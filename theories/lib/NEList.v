From Mtac2.lib Require Import List Datatypes.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Inductive nelist {A : Type} : Type :=
| ne_sing : A -> nelist
| ne_cons : A -> nelist -> nelist.

Arguments nelist _ : clear implicits.

Section Funs.
  Context {A : Type}.

  Fixpoint length (l : nelist A) : nat :=
    match l with
    | ne_sing _ => 1
    | ne_cons _ l => S (length l)
    end.

  Definition hd (l : nelist A) : A :=
    match l with
    | ne_sing a | ne_cons a _ => a
    end.

  Definition tl (l : nelist A) : option (nelist A) :=
    match l with
    | ne_sing a => None
    | ne_cons _ l => (Some l)
    end.

  Fixpoint last (l : nelist A) : A :=
    match l with
    | ne_sing a => a
    | ne_cons _ l => last l
    end.

  Fixpoint nth (n : nat) (l : nelist A) : A :=
    match n, l with
    | 0, (ne_sing a | ne_cons a _) => a
    | S n, ne_cons _ l => nth n l
    | S _, ne_sing a => a
    end.

  Fixpoint to_list (l : nelist A) : mlist A :=
    match l with
    | ne_sing a => mcons a mnil
    | ne_cons a l => mcons a (to_list l)
    end.

  Lemma nth_correct n l : nth n l = mnth n (to_list l) (last l).
  Proof.
    revert l.
    induction n; intros l.
    - destruct l; reflexivity.
    - induction l.
      + now destruct n.
      + cbn. now rewrite IHn.
  Qed.

  Fixpoint append (l l' : nelist A) : nelist A :=
    match l with
    | ne_sing a => ne_cons a l'
    | ne_cons a l => ne_cons a (append l l')
    end.

  Theorem app_assoc (l m n : nelist A) : append l (append m n) = append (append l m) n.
  Proof.
    revert m n.
    induction l; intros m n; [reflexivity|].
    cbn. f_equal. exact (IHl _ _).
  Qed.

  Fixpoint rev (l : nelist A) : nelist A :=
    match l with
    | ne_sing a => ne_sing a
    | ne_cons a l => append (rev l) (ne_sing a)
    end.

  Fixpoint rev_append (l l' : nelist A) : nelist A :=
    match l with
    | ne_sing a => ne_cons a l'
    | ne_cons a l => rev_append l (ne_cons a l')
    end.

  Definition rev' l : nelist A :=
    match l with
    | ne_sing a => ne_sing a
    | ne_cons a l => rev_append l (ne_sing a)
    end.

  Fixpoint map {B} (F : A -> B) (l : nelist A) : nelist B :=
    match l with
    | ne_sing a => ne_sing (F a)
    | ne_cons a l => ne_cons (F a) (map F l)
    end.

  Fixpoint reduce (F : A -> A -> A) (l: nelist A) : A :=
    match l with
    | ne_sing a => a
    | ne_cons a l => F a (reduce F l)
    end.

  Fixpoint fold_right' {B} (F : A -> B -> B)  (I : A -> B) (l : nelist A) : B :=
    match l with
    | ne_sing a => I a
    | ne_cons a l => F a (fold_right' F I l)
    end.

  Fixpoint fold_left' {B} (F : B -> A -> B) (l : nelist A) (I : A -> B) : B :=
    match l with
    | ne_sing a => I a
    | ne_cons a l => fold_left' F l (fun a_i => F (I a) a_i)
    end.

  Lemma fold_right'_app {B} (F : A -> B -> B) I
        (l l' : nelist A) :
    fold_right' F I (append l l') = fold_right' F (fun a => F a (fold_right' F I l')) l.
  Proof.
    revert I l'. induction l; intros I l'; [reflexivity|].
    cbn. f_equal. exact (IHl _ _).
  Qed.

  Lemma fold_left'_rev_right {B} (F : A -> B -> B) I
        (l : nelist A) :
    fold_right' F I (rev l) = fold_left' (fun b a => F a b) l I.
  Proof.
    revert F I; induction l; intros F I; [reflexivity|].
    cbn. rewrite fold_right'_app. cbn.
    rewrite IHl. reflexivity.
  Qed.

  Fixpoint fold_right {B} (F : A -> B -> B)  (I : B) (l : nelist A) : B :=
    match l with
    | ne_sing a => F a I
    | ne_cons a l => F a (fold_right F I l)
    end.

  Fixpoint fold_left {B} (F : B -> A -> B) (l : nelist A) I : B :=
    match l with
    | ne_sing a => F I a
    | ne_cons a l => fold_left F l (F I a)
    end.


  Lemma fold_right_app {B} (F : A -> B -> B) I
        (l l' : nelist A) :
    fold_right F I (append l l') = fold_right F (fold_right F I l') l.
  Proof.
    revert I l'. induction l; intros I l'; [reflexivity|].
    cbn. f_equal. exact (IHl _ _).
  Qed.

  Lemma fold_left_rev_right {B} (F : A -> B -> B) I
        (l : nelist A) :
    fold_right F I (rev l) = fold_left (fun b a => F a b) l I.
  Proof.
    revert F I; induction l; intros F I; [reflexivity|].
    cbn. rewrite fold_right_app. cbn.
    rewrite IHl. reflexivity.
  Qed.

  (* Theorem fold_symmetric : *)
  (*   forall (F : A -> A -> A), *)
  (*   (forall x y z : A, F x (F y z) = F (F x y) z) -> *)
  (*   forall (a0 : A), *)
  (*     (forall y : A, F a0 y = F y a0) -> *)
  (*     forall (l : nelist A), fold_left F l a0 = fold_right F a0 l. *)
  (* Proof. *)
  (*   intros F HF a0 HF2 l. *)
  (*   rewrite <- fold_left_rev_right. *)
  (*   revert a0 HF2. induction l; intros a0 HF2. *)
  (*   - cbn. rewrite HF2. reflexivity. *)
  (*   - cbn. *)
  (*     rewrite fold_right_app. *)
  (*     rewrite IHl; clear IHl. *)
  (*     cbn. *)

End Funs.

Import ProdNotations.

Fixpoint netuple_nth {A} {f : A -> Type} {l : nelist A} (n: nat) :
  reduce mprod (map f l) -> f (nth n l) :=
  match l as l, n as n return reduce mprod (map f l) -> f (nth n l) with
  | ne_sing _, 0
  | ne_sing _, S _ => fun x => x
  (* We need to be very careful to not force the tuple in the two cases below.
     This function will eventually be called on tuples of unknown value and we
     need it to compute despite that. *)
  | ne_cons _ _, 0 => fun xs => mfst xs
  | ne_cons _ l, S n => fun xs => netuple_nth n (msnd xs)
  end
.


Declare Scope ne_list_scope.
Delimit Scope ne_list_scope with ne_list.
Bind Scope ne_list_scope with nelist.

Notation "'[ne:' x ]" := (ne_sing x) : ne_list_scope.
Notation "'[ne:' x , .. , y , z ]" := (ne_cons x .. (ne_cons y (ne_sing z)) ..) : ne_list_scope.
