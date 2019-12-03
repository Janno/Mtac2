From Coq Require Import BinNums String.
From Mtac2 Require Import Datatypes List.
Import ProdNotations.
From Mtac2.intf Require Import Dyn MTele Sorts.
From Mtac2.lib Require Import Datatypes Specif.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Set Polymorphic Inductive Cumulativity.

Record Constr_dyn :=
  mkConstr_dyn {
      constr_dyn_constr : dyn;
      constr_dyn_name : string;
    }.

Record Ind_dyn :=
  mkInd_dyn {
      ind_dyn_ind : dyn;
      ind_dyn_ind_name : string;
      ind_dyn_nparams : N;
      ind_dyn_nindices : N;
      ind_dyn_constrs : mlist Constr_dyn;
    }.


Record ind_sig {params : MTele} : Type :=
  {
    ind_sig_sort : S.Sort;
    ind_sig_arity : MTele_ConstT MTele params;
  }.
Arguments ind_sig _ : clear implicits.

(* Definition ind_arity (params : MTele) := S.Sort *m MTele_ConstT (MTele) params. *)
Record ind_def {params: MTele} : Type :=
  { ind_def_name : string; ind_def_sig : ind_sig params }.
Arguments ind_def _ : clear implicits.

Definition ind_arg {params} (i : ind_def params) : Type :=
  let sort := ind_sig_sort (ind_def_sig i) in
  let arity := ind_sig_arity (ind_def_sig i) in
    MTele_val (curry_sort Typeₛ
                 (fun a' => MTele_Sort sort (apply_constT arity a'))
              ).

Definition inds_args {params} (sigs : mlist (ind_def params)) (to : Type) : Type :=
  mfold_right (fun sig accu => ind_arg sig -> accu) to sigs.

Record constr_def {ind_mt : MTele} : Type :=
  {
    constr_def_name : string;
    constr_def_tele : MTele;
    constr_def_indices : MTele_ConstT (ArgsOf ind_mt) constr_def_tele;
  }.
Arguments constr_def _ : clear implicits.
(* Definition constr_def (ind_mt : MTele) := *)
(*   string *m msigT (MTele_ConstT (ArgsOf ind_mt)). *)

(* Compute the actual type of constructor [c] given an inductive [ind] of sort [sort_ind]. *)
Definition constr_def_value {ind_mt} (sort_ind : S.Sort)
  (ind : MTele_Sort sort_ind ind_mt) (c : constr_def ind_mt) : Type :=
  MTele_val (
      curry_sort
        sort_ind
        (fun c_args =>
           let i_args := apply_const (s:=Typeₛ) (constr_def_indices c) c_args in
           apply_sort ind i_args
        )
    ).

Definition constrs_def (ind_mt : MTele) : Type :=
  mlist (constr_def ind_mt).

Definition constrs_defs {params} (sigs : mlist (ind_def params)) (a : ArgsOf params) :=
  mfold_right (fun '{| ind_def_sig := {| ind_sig_arity:=ind |} |} acc =>
                 constrs_def (apply_constT ind a) *m acc
              ) unit sigs.

Definition constrs_defs_in_ctx {params} (sigs : mlist (ind_def params)) :=
  inds_args sigs (MTele_val (curry_sort Typeₛ (constrs_defs sigs))).



Record constr_def_wop {params} (ind : MTele_ConstT MTele params) :=
  {
    constr_def_wop_name : string;
    constr_def_wop_tele : MTele_ConstT MTele params;
    constr_def_wop_indices : MTele_val (curry_sort Typeₛ (fun args => MTele_ConstT (ArgsOf (apply_constT ind args)) (apply_constT constr_def_wop_tele args)));
  }.

Definition constrs_def_wop {params} (ind : MTele_ConstT MTele params) :=
  mlist (constr_def_wop ind).

Definition constrs_defs_wop {params} (sigs : mlist (ind_def params)) :=
  mfold_right (fun '{| ind_def_sig := {| ind_sig_arity:=ind |} |} acc =>
                 constrs_def_wop ind *m acc
              ) unit sigs.

Definition constrs_defs_in_ctx_wop {params} (sigs : mlist (ind_def params)) :=
  inds_args sigs (constrs_defs_wop sigs).

Record Mind_Spec :=
  {
    mind_spec_polymorphic: bool;
    mind_spec_params : MTele;
    mind_spec_ind_sigs : mlist (ind_def mind_spec_params);
    mind_spec_constr_sigs : constrs_defs_in_ctx_wop mind_spec_ind_sigs;
  }.

(* Definition inds {params} : forall (sigs : mlist (ind_def params)), Type := *)
(*   mfold_right (fun ind_def acc => *)
(*                  ind_arg ind_def *m acc *)
(*               ) unit. *)

(* Definition constrs {params} {ind} (ia : @ind_arg params ind) : Type := *)
(*   MTele_val ( *)
(*       curry_sort *)
(*         Typeₛ *)
(*         (fun args => *)
(*            (* let sort := ind_sig_sort (ind_def_sig ia ) in *) *)
(*            let sort := ind_sig_sort (ind_def_sig ind) in *)
(*            let tele := apply_const (s:=Typeₛ) (ind_sig_arity (ind_def_sig ind)) args in *)
(*            let ia := apply_curry (apply_val (s:=Typeₛ) ia args) in *)
(*            forall cs : constrs_def tele, *)
(*              mfold_right (fun c acc => constr_def_value sort ia c *m acc) unit cs *)
(*         ) *)
(*     ). *)

(* Fixpoint constrs {params} {sigs} : @inds params sigs -> constrs_defs_in_ctx sigs -> Type := *)
(*   match sigs as sigs return inds sigs -> constrs_defs_in_ctx sigs  -> Type with *)
(*   | mnil => fun 'tt _ =>  unit *)
(*   | sig :m: sigs => fun '(m: ind, inds) C => let '(m: constrs, C) := C ind in _ *)
(*   end. *)

(* Record Mind := *)
(*   { *)
(*     mind_spec := Mind_Spec; *)
(*     mind_inds :=  *)
(*   } *)

Record Mind_Entry :=
  {
    mind_entry_mind: Mind_Spec;
    mind_entry_index: N;
    mind_entry_params_given: N;
    mind_entry_indices_given: N;
  }.

Record Case :=
    mkCase {
        case_ind : Type;
        case_val : case_ind;
        case_return : dyn;
        case_branches : mlist dyn
        }.
