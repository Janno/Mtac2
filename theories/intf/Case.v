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


Record ind_sig (params : MTele) : Type :=
  {
    ind_sig_sort : S.Sort;
    ind_sig_arity : MTele_ConstT MTele params;
  }.

(* Definition ind_arity (params : MTele) := S.Sort *m MTele_ConstT (MTele) params. *)
Record ind_def (params: MTele) : Type :=
  { ind_def_name : string; ind_def_sig : ind_sig params }.

Definition ind_arg {params} : ind_def params -> Type :=
  fun '({| ind_def_sig := {| ind_sig_sort:=sort; ind_sig_arity :=arity |} |}) =>
    MTele_val (curry_sort Typeₛ
                 (fun a' => MTele_Sort sort (apply_constT arity a'))
              ).

Definition inds_args {params} (sigs : mlist (ind_def params)) (to : Type) : Type :=
  mfold_right (fun sig accu => ind_arg sig -> accu) to sigs.

Record constr_def (ind_mt : MTele) : Type :=
  {
    constr_def_name : string;
    constr_def_tele : MTele;
    constr_def_indices : MTele_ConstT (ArgsOf ind_mt) constr_def_tele;
  }.
(* Definition constr_def (ind_mt : MTele) := *)
(*   string *m msigT (MTele_ConstT (ArgsOf ind_mt)). *)

Definition constrs_def (ind_mt : MTele) : Type :=
  mlist (constr_def ind_mt).

Definition constrs_defs {params} (sigs : mlist (ind_def params)) (a : ArgsOf params) :=
  mfold_right (fun '{| ind_def_sig := {| ind_sig_arity:=ind |} |} acc =>
                 constrs_def (apply_constT ind a) *m acc
              ) unit sigs.

Definition constrs_defs_in_ctx {params} (sigs : mlist (ind_def params)) :=
  inds_args sigs (MTele_val (curry_sort Typeₛ (constrs_defs sigs))).

Record Mind :=
  {
    mind_polymorphic: bool;
    mind_params : MTele;
    mind_ind_sigs : mlist (ind_def mind_params);
    mind_constr_sigs : constrs_defs_in_ctx mind_ind_sigs;
  }.

Record Mind_Entry :=
  {
    mind_entry_mind: Mind;
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
