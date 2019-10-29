From Coq Require Import BinNums String.
From Mtac2 Require Import Datatypes List.
Import ProdNotations.
From Mtac2.intf Require Import Dyn.

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

Record Case :=
    mkCase {
        case_ind : Type;
        case_val : case_ind;
        case_return : dyn;
        case_branches : mlist dyn
        }.