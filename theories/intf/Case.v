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



Record constr_def_wop {params} {ind : MTele_ConstT MTele params} :=
  {
    constr_def_wop_name : string;
    constr_def_wop_tele : MTele_ConstT MTele params;
    constr_def_wop_indices : MTele_val (curry_sort Typeₛ (fun args => MTele_ConstT (ArgsOf (apply_constT ind args)) (apply_constT constr_def_wop_tele args)));
  }.
Arguments constr_def_wop {_} _.

Definition constr_def_value_wop
           {params}
           {i : ind_def params}
           (ia: ind_arg i)
           (c : constr_def_wop (ind_sig_arity (ind_def_sig i))) : Type :=
  MTele_val (
      curry_sort
        Typeₛ
        (fun p_args =>
           let c_params := apply_constT (constr_def_wop_tele c) p_args in
           let c_inds := apply_val (s:=Typeₛ) (constr_def_wop_indices c) p_args in
           let c_inds := apply_curry_sort c_inds in
           let ia := apply_val (s:=Typeₛ) ia p_args in
           let ia := apply_curry_sort ia in
           MTele_sort (
               curry_sort
                 _
                 (fun c_args =>
                    let args := apply_constT c_inds c_args in
                    let ind := apply_sort ia args in
                    ind
                 )
             )
        )
    ).

Definition constrs_def_wop {params} (ind : MTele_ConstT MTele params) :=
  mlist (constr_def_wop ind).

Definition constrs_defs_wop {params} : forall (sigs : mlist (ind_def params)), Type :=
  mfold_right (fun sig acc =>
                 constrs_def_wop (ind_sig_arity (ind_def_sig sig)) *m acc
              ) unit.

Definition constrs_defs_in_ctx_wop {params} (sigs : mlist (ind_def params)) :=
  inds_args sigs (constrs_defs_wop sigs).

Record Mind_Spec :=
  {
    mind_spec_polymorphic: bool;
    mind_spec_params : MTele;
    mind_spec_ind_sigs : mlist (ind_def mind_spec_params);
    mind_spec_constr_sigs : constrs_defs_in_ctx_wop mind_spec_ind_sigs;
  }.

Definition inds {params} : forall (sigs : mlist (ind_def params)), Type :=
  mfold_right (fun ind_def acc =>
                 ind_arg ind_def *m acc
              ) unit.

Fixpoint constrs_type {params} {sig : ind_def params} (ia : ind_arg sig) :
  forall (cs : mlist (constr_def_wop (ind_sig_arity (ind_def_sig sig)))), Type :=
  mfold_right (fun c acc => constr_def_value_wop ia c *m acc) unit.

Fixpoint constrs_types {params} {sigs : mlist (ind_def params)} :
  forall
    (ias : inds sigs)
    (css : constrs_defs_wop sigs), Type
  :=
    match sigs as sigs return
          forall
            (ias : inds sigs)
            (css : constrs_defs_wop sigs), Type
  with
  | mnil => fun 'tt 'tt => unit
  | sig :m: sigs => fun '(m: ia, ias) '(m: cs, css) => constrs_type ia cs *m constrs_types ias css
  end.


Definition constrs
           {params}
           {sigs : mlist (ind_def params)}
           (css : inds_args sigs (constrs_defs_wop sigs))
           (is : inds sigs) :
  Type :=
  (fun (sigs' : mlist (ind_def params)) (is' : inds sigs') =>
     fix go {sigs : mlist (ind_def params)} :
        forall
          (css : inds_args sigs (constrs_defs_wop sigs'))
          (is : inds sigs),
          Type :=
     match sigs as sigs return
           forall
             (css : inds_args sigs (constrs_defs_wop sigs'))
             (is : inds sigs),
             Type
     with
     | mnil =>
       fun (css : constrs_defs_wop sigs') 'tt =>
         constrs_types is' css
     | sig :m: sigs =>
       fun css '(m: ia, is) =>
         let css := css ia in
         go css is
     end)
    sigs is sigs css is
.

Record Mind :=
  {
    mind_spec : Mind_Spec;
    mind_inds : inds (mind_spec_ind_sigs mind_spec);
    mind_constrs : constrs (mind_spec_constr_sigs mind_spec) (mind_inds)
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
