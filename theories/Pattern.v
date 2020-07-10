From Mtac2 Require Import Logic List intf.Unification Sorts MTele Exceptions.
Import Sorts.S.
Import ListNotations.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Set Polymorphic Inductive Cumulativity.

(** Pattern matching without pain *)
(* The M will be instantiated with the M monad or the gtactic monad. In principle,
we could make it part of the B, but then higher order unification will fail. *)
Inductive pattern@{a} (A : Type@{a}) (B : A -> Prop) : Prop :=
  | pany : (forall x : A, B x) -> pattern A B
  | pbase : forall x : A, B x -> Unification -> pattern A B
  | ptele : forall {C:Type@{a}}, (forall x : C, pattern A B) -> pattern A B
  | psort : (Sort -> pattern A B) -> pattern A B.


Arguments pany {A B} _.
Arguments pbase {A B} _ _ _.
Arguments ptele {A B C} _.
Arguments psort {A B} _.

Inductive branch : forall {A : Type} {B : A -> Prop}, Prop :=
| branch_pattern {A : Type} {B : A -> Prop}: pattern A B -> @branch A B
| branch_app_static {A : Type} {B : A -> Prop}:
    forall {m:MTele} (uni : Unification) (C : selem_of (MTele_Const (s:=Typeₛ) A m)),
      MTele_sort (MTele_ConstMap (si := Typeₛ) Propₛ (fun a : A => B a) C) ->
      @branch A B
| branch_forallP {B : Prop -> Prop}:
    (forall (X : Type) (Y : X -> Prop), B (forall x : X, Y x)) ->
    @branch Prop B
| branch_forallT {B : Type -> Prop}:
    (forall (X : Type) (Y : X -> Type), B (forall x : X, Y x)) ->
    @branch Type B.
Arguments branch _ _ : clear implicits.


(* | branch_app_dynamic {A} {B : forall A, A -> Type} {y}: *)
(*     (forall X (Y : X -> Type) (f : forall x, Y x) (x : X), M (B _ (f x))) -> *)
(*     @branch M _ B A y *)

Declare Scope pattern_scope.
Delimit Scope pattern_scope with pattern.

Notation "[¿ s .. t ] ps" := (psort (fun s => .. (psort (fun t => ps)) ..))
  (at level 202, s binder, t binder, ps at next level, only parsing) : pattern_scope.
Notation "'[S?' s .. t ] ps" := (psort (fun s => .. (psort (fun t => ps)) ..))
  (at level 202, s binder, t binder, ps at next level) : pattern_scope.

Notation "[? x .. y ] ps" := (ptele (fun x => .. (ptele (fun y => ps)).. ))
  (at level 202, x binder, y binder, ps at next level) : pattern_scope.
Notation "p => b" := (pbase p%core b%core UniMatch)
  (no associativity, at level 201) : pattern_scope.
(* Notation "p => [ H ] b" := (pbase p%core (fun H => b%core) UniMatch) *)
(*   (no associativity, at level 201, H at next level) : pattern_scope. *)
(* Notation "p => [ H .. G ] b" := (pbase p%core (fun H => .. (fun G => b%core) .. ) UniMatch) *)
  (* (no associativity, at level 201, H binder, G binder) : pattern_scope. *)

Notation "p '=n>' b" := (pbase p%core b%core UniMatchNoRed)
  (no associativity, at level 201) : pattern_scope.
(* Notation "p '=n>' [ H ] b" := (pbase p%core b%core UniMatchNoRed) *)
(*   (no associativity, at level 201, H at next level) : pattern_scope. *)
(* Notation "p =n> [ H .. G ] b" := (pbase p%core (fun H => .. (fun G => b%core) .. ) UniMatchNoRed) *)
(*   (no associativity, at level 201, H binder, G binder) : pattern_scope. *)

Notation "p '=u>' b" := (pbase p%core b%core UniCoq)
  (no associativity, at level 201) : pattern_scope.
(* Notation "p '=u>' [ H ] b" := (pbase p%core (fun H => b%core) UniCoq) *)
(*   (no associativity, at level 201, H at next level) : pattern_scope. *)
(* Notation "p =u> [ H .. G ] b" := (pbase p%core (fun H => .. (fun G => b%core) .. ) UniCoq) *)
(*   (no associativity, at level 201, H binder, G binder) : pattern_scope. *)

Notation "p '=c>' b" := (pbase p%core b%core UniEvarconv)
  (no associativity, at level 201) : pattern_scope.
(* Notation "p '=c>' [ H ] b" := (pbase p%core (fun H => b%core) UniEvarconv) *)
(*   (no associativity, at level 201, H at next level) : pattern_scope. *)
(* Notation "p =c> [ H .. G ] b" := (pbase p%core (fun H => .. (fun G => b%core) .. ) UniEvarconv) *)
(*   (no associativity, at level 201, H binder, G binder) : pattern_scope. *)

Delimit Scope pattern_scope with pattern.

Notation "'_' 'as' _catchall => b " := (pany (fun _catchall => b%core))
  (at level 201, b at next level) : pattern_scope.



Declare Scope branch_scope.

Notation "[¿ s .. t ] ps" := (branch_pattern (psort (fun s => .. (psort (fun t => ps%pattern)) ..)))
  (at level 202, s binder, t binder, ps at next level, only parsing) : branch_scope.
Notation "'[S?' s .. t ] ps" := (branch_pattern (psort (fun s => .. (psort (fun t => ps%pattern)) ..)))
  (at level 202, s binder, t binder, ps at next level) : branch_scope.

Notation "[? x .. y ] ps" := (branch_pattern (ptele (fun x => .. (ptele (fun y => ps%pattern)).. )))
  (at level 202, x binder, y binder, ps at next level) : branch_scope.
Notation "p => b" := (branch_pattern (pbase p%core b%core UniMatch))
  (no associativity, at level 201) : branch_scope.
(* Notation "p => [ H ] b" := (branch_pattern (pbase p%core (fun H => b%core) UniMatch)) *)
(*   (no associativity, at level 201, H at next level) : branch_scope. *)
(* Notation "p => [ H .. G ] b" := (branch_pattern (pbase p%core (fun H => .. (fun G => b%core) .. ) UniMatch)) *)
(*   (no associativity, at level 201, H binder, G binder) : branch_scope. *)

Notation "p '=n>' b" := (branch_pattern (pbase p%core b%core UniMatchNoRed))
  (no associativity, at level 201) : branch_scope.
(* Notation "p '=n>' [ H ] b" := (branch_pattern (pbase p%core (fun H => b%core) UniMatchNoRed)) *)
(*   (no associativity, at level 201, H at next level) : branch_scope. *)
(* Notation "p =n> [ H .. G ] b" := (branch_pattern (pbase p%core (fun H => .. (fun G => b%core) .. ) UniMatchNoRed)) *)
(*   (no associativity, at level 201, H binder, G binder) : branch_scope. *)

Notation "p '=u>' b" := (branch_pattern (pbase p%core b%core UniCoq))
  (no associativity, at level 201) : branch_scope.
(* Notation "p '=u>' [ H ] b" := (branch_pattern (pbase p%core (fun H => b%core) UniCoq)) *)
(*   (no associativity, at level 201, H at next level) : branch_scope. *)
(* Notation "p =u> [ H .. G ] b" := (branch_pattern (pbase p%core (fun H => .. (fun G => b%core) .. ) UniCoq)) *)
(*   (no associativity, at level 201, H binder, G binder) : branch_scope. *)

Notation "p '=c>' b" := (branch_pattern (pbase p%core b%core UniEvarconv))
  (no associativity, at level 201) : branch_scope.

Delimit Scope branch_scope with branch.

Notation "'_' 'as' _catchall => b " := (branch_pattern (pany (fun _catchall => b%core)))
  (at level 201, b at next level) : branch_scope.

Declare Scope with_pattern_scope.

Notation "'with' | p1 | .. | pn 'end'" :=
  ((@mcons (branch _ _) p1%branch (.. (@mcons (branch _ _) pn%branch [m:]) ..)))
  (at level 91, p1 at level 210, pn at level 210) : with_pattern_scope.
Notation "'with' p1 | .. | pn 'end'" :=
  ((@mcons (branch _ _) p1%branch (.. (@mcons (branch _ _) pn%branch [m:]) ..)))
  (at level 91, p1 at level 210, pn at level 210) : with_pattern_scope.

Delimit Scope with_pattern_scope with with_pattern.

(* Syntax for decomposition of applications with a known head symbol.

   The [=>] arrows are annotated with the reduction strategy used for the
   initial arguments that are part of the head symbol term [f]. The delimiter
   [|] separates the head symbol term from the arguments, which are binders that
   can be refered to in [b]
*)

Notation "'[#' ] f '|' x .. z '=n>' b" :=
  (branch_app_static
     (m := mTele (fun x => .. (mTele (fun z => mBase)) ..))
     UniMatchNoRed
     f
     (fun x => .. (fun z => b) ..)
  ) (at level 201, x binder, z binder) : branch_scope.

Notation "'[#' ] f '|' '=n>' b" :=
  (branch_app_static (m := mBase) UniMatchNoRed f b) (at level 201) : branch_scope.

Notation "'[#' ] f '|' x .. z '=m>' b" :=
  (branch_app_static
     (m := mTele (fun x => .. (mTele (fun z => mBase)) ..))
     UniMatch
     f
     (fun x => .. (fun z => b) ..)
  ) (at level 201, x binder, z binder) : branch_scope.

Notation "'[#' ] f '|' '=m>' b" :=
  (branch_app_static (m := mBase) UniMatch f b) (at level 201) : branch_scope.

Notation "'[#' ] f '|' x .. z '=u>' b" :=
  (branch_app_static
     (m := mTele (fun x => .. (mTele (fun z => mBase)) ..))
     UniCoq
     f
     (fun x => .. (fun z => b) ..)
  ) (at level 201, x binder, z binder) : branch_scope.

Notation "'[#' ] f '|' '=u>' b" :=
  (branch_app_static (m := mBase) UniCoq f b) (at level 201) : branch_scope.

Notation "'[#' ] f '|' x .. z '=c>' b" :=
  (branch_app_static
     (m := mTele (fun x => .. (mTele (fun z => mBase)) ..))
     UniEvarconv
     f
     (fun x => .. (fun z => b) ..)
  ) (at level 201, x binder, z binder) : branch_scope.

Notation "'[#' ] f '|' '=c>' b" :=
  (branch_app_static (m := mBase) UniEvarconv f b) (at level 201) : branch_scope.


(* Syntax for decomposition of [forall x : X, P x].

   We define two variants, one for [Prop] and for [Type].
   The initial tokens are [[!Prop]] and [[!Type]] and the remaining
   syntax tries to mirror an actual [forall].
 *)
Notation "'[!Prop' ] 'forall' '_' : X , P =n> b" :=
  (branch_forallP (fun X P => b))
    (at level 201) : branch_scope.
Notation "'[!Type' ] 'forall' '_' : X , P =n> b" :=
  (branch_forallT (fun X P => b))
    (at level 201) : branch_scope.

Structure Predicate :=
  PREDICATE {
    predicate_pred : Prop
  }.

Structure Matcher {A} :=
  MATCHER {
    matcher_pred: forall y, Predicate;
    matcher_ret: Prop;
    _ : forall (E: Exception) (ps : mlist (branch A (fun y => predicate_pred (matcher_pred y)))), matcher_ret
  }.
Arguments Matcher {_}.
Arguments MATCHER {_}.

Definition matcher_match {A} (m : Matcher) : forall (E: Exception) (ps : mlist (branch A (fun y => predicate_pred (matcher_pred m y)))), matcher_ret m :=
  ltac:(destruct m as [ ? ? x]; refine x).

Structure InDepMatcher :=
  INDEPMATCHER {
    idmatcher_return : Prop;
    _ : forall A (y : A) (E: Exception) (ps : mlist (branch A (fun _ => idmatcher_return))), idmatcher_return;
  }.

Definition idmatcher_match (m : InDepMatcher) : forall A y (E: Exception) (ps : mlist (branch A (fun _ => idmatcher_return m))), idmatcher_return m :=
  ltac:(destruct m as [ ? x]; refine x).

Definition idmatcher_match_invert (m : InDepMatcher) (A : Type) (y : A) (R : Prop) :
  R =m= idmatcher_return m ->
  forall (_ : Exception) (_ : mlist (branch A (fun _ => R))),
    (* R y =m= matcher_return y m -> *)
    R.
  intros ->. eauto using idmatcher_match. Defined.

Arguments idmatcher_match _ _ _ & _.

Definition matcher_match_invert (A : Type) (y : A) (m : Matcher) (R : A -> Prop) :
  (matcher_ret m =m= R y) ->
  (fun y => predicate_pred (matcher_pred m y)) =m= R ->
  forall (_ : Exception) (_ : mlist (branch A R)),
    (* R y =m= matcher_return y m -> *)
    R y.
  intros <- <-. eauto using matcher_match. Defined.

Arguments matcher_match_invert _ _ _ _ & _ _ _ _ .


Notation "'mmatch' x ls" :=
  (idmatcher_match _ _ x DoesNotMatch ls%with_pattern)
  (at level 200, ls at level 91).
Notation "'mmatch' x 'return' p ls" :=
  (idmatcher_match_invert _ _ x p meq_refl DoesNotMatch ls%with_pattern)
  (at level 200, ls at level 91).
Notation "'mmatch' x 'as' y 'return' p ls" :=
  (matcher_match_invert _ x _ (fun y => p%type) meq_refl meq_refl DoesNotMatch ls%with_pattern)
  (at level 200, ls at level 91).
Notation "'mmatch' x 'in' T 'as' y 'return' p ls" :=
  (matcher_match_invert T%type x _ (fun y => p%type) meq_refl meq_refl DoesNotMatch ls%with_pattern)
  (at level 200, ls at level 91).
