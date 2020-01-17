From Coq Require Import BinNums String.
From Mtac2 Require Import Datatypes List NEList.
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


Record ind_sig@{p pi po i} {params : MTele@{p}} : Type :=
  {
    ind_sig_sort : S.Sort;
    ind_sig_arity : MTele_ConstT@{p pi po} MTele@{i} params;
  }.
Arguments ind_sig _ : clear implicits.

(* Definition ind_arity (params : MTele) := S.Sort *m MTele_ConstT (MTele) params. *)
Record ind_def@{p+} {params: MTele@{p}} : Type :=
  { ind_def_name : string; ind_def_sig : ind_sig params }.
Arguments ind_def _ : clear implicits.

Definition ind_arg@{p+} {params : MTele@{p}} (i : ind_def params) : Type :=
  let sort := ind_sig_sort (ind_def_sig i) in
  let arity := ind_sig_arity (ind_def_sig i) in
    MTele_val (curry_sort Typeₛ
                 (fun a' : ArgsOf@{p} params => MTele_Sort sort (apply_constT arity a'))
              ).

Definition inds_args {params} (sigs : nelist (ind_def params)) (to : Type) : Type :=
  fold_right (fun sig accu => ind_arg sig -> accu) to sigs.

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

Definition constrs_defs {params} (sigs : nelist (ind_def params)) (a : ArgsOf params) :=
  let cs := map (fun i =>
                   let ind := ind_sig_arity (ind_def_sig (i)) in
                   constrs_def (apply_constT ind a)
                ) sigs
  in reduce mprod cs.

Definition constrs_defs_in_ctx {params} (sigs : nelist (ind_def params)) :=
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
        (fun p_args =>          (* packed parameters of [i] *)
           let c_inds := apply_val (s:=Typeₛ) (constr_def_wop_indices c) p_args in
           let c_inds := apply_curry_sort c_inds in
           let ia := apply_val (s:=Typeₛ) ia p_args in
           let ia := apply_curry_sort ia in
           MTele_val (
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

Definition constrs_defs_wop {params} (sigs : nelist (ind_def params)) : Type :=
  let cs_defs := map (fun sig => constrs_def_wop (ind_sig_arity (ind_def_sig sig))) sigs
  in reduce mprod cs_defs.

Definition constrs_defs_in_ctx_wop {params} (sigs : nelist (ind_def params)) :=
  inds_args sigs (constrs_defs_wop sigs).

Record Mind_Spec :=
  {
    mind_spec_polymorphic: bool;
    mind_spec_params : MTele;
    mind_spec_ind_sigs : nelist (ind_def mind_spec_params);
    mind_spec_constr_sigs : constrs_defs_in_ctx_wop mind_spec_ind_sigs;
  }.

Definition inds {params} (sigs : nelist (ind_def params)) :Type :=
  reduce mprod (map ind_arg sigs).

Definition constrs_wop {params} {sig : ind_def params} (ia : ind_arg sig) :
  forall (cs : mlist (constr_def_wop (ind_sig_arity (ind_def_sig sig)))), Type :=
  mfold_right (fun c acc => constr_def_value_wop ia c *m acc) unit.

Fixpoint constrs_types {params} {sigs : nelist (ind_def params)} :
  forall
    (ias : inds sigs)
    (css : constrs_defs_wop sigs), Type
  :=
    match sigs as sigs return
          forall
            (ias : inds sigs)
            (css : constrs_defs_wop sigs), Type
  with
  | ne_sing sig =>
    fun ia cs => constrs_wop ia cs
  | ne_cons sig sigs =>
    fun '(m: ia, ias) '(m: cs, css) => constrs_wop ia cs *m constrs_types ias css
  end.

Fixpoint constrs_types_nth
         {params} {sigs : nelist (ind_def params)} (n : nat) :
  forall
    (ias : inds sigs)
    (css : constrs_defs_wop sigs),
    constrs_types ias css -> constrs_wop (netuple_nth n ias) (netuple_nth n css) :=
  match sigs as sigs, n as n return
        forall
          (ias : inds sigs)
          (css : constrs_defs_wop sigs),
          constrs_types ias css -> constrs_wop (netuple_nth n ias) (netuple_nth n css)
  with
  | ne_sing sig, 0 => fun _ _ t => t
  | ne_sing sig, _ => fun _ _ t => t
  | ne_cons _ _, 0 => fun '(m: _, _) '(m: _, _) '(m: t, _) => t
  | ne_cons _ sigs, S n => fun '(m: _, _) '(m: _, _) '(m: _, cts) => constrs_types_nth n _ _ cts
  end
.

Fixpoint ind_args_get
         {T}
         {params}
         {sigs : nelist (ind_def params)} :
  forall
    (css : inds_args sigs T)
    (is : inds sigs),
    T :=
  match sigs as sigs' return
        forall
          (css : inds_args sigs' T)
          (is : inds sigs'),
          T
  with
  | ne_sing sig => fun css is => css is
  | ne_cons sig sigs => fun css '(m: ia, is) =>
    ind_args_get (css ia) is
  end.

Definition constrs
           {params}
           {sigs : nelist (ind_def params)}
           (css : inds_args sigs (constrs_defs_wop sigs))
           (is : inds sigs) :
  Type :=
  constrs_types is (ind_args_get css is).

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

(* Set Printing Universes. *)

Definition indices_of {params} (i: ind_def params) (p_args : ArgsOf params) :=
  ArgsOf (apply_constT (ind_sig_arity (ind_def_sig i)) p_args).

Definition val_of_ind
           {params}
           {i : ind_def params}
           {p_args : ArgsOf params}
           (ia : ind_arg i)
           (i_args : indices_of i p_args)
 : Type :=
  let ia := apply_val (s:=Typeₛ) ia p_args in
  let ia := apply_curry_sort ia in
  apply_sort ia i_args
.

Definition return_predicate_type
           {params}
           {i : ind_def params}
           (p_args : ArgsOf params)
           (ia : ind_arg i)
           (s : S.Sort)
  : Type :=
    MTele_val
      (
        curry_sort Typeₛ (fun i_args => apply_sort (apply_curry_sort (apply_val (s:=Typeₛ) ia p_args)) i_args -> s)
      ).

Fixpoint zip_dep_fold {A} {F : A -> Type} {l}
  (g : forall a, F a -> Type):
    mfold_right (fun a acc => F a *m acc) unit l ->
    Type :=
  match l as l return mfold_right (fun a acc => F a *m acc) unit l -> Type with
  | mnil => fun 'tt => unit
  | mcons a l => fun '(m: fa, t) => g _ fa *m zip_dep_fold g t
  end.


Definition return_type_for
    {match_sort: S.Sort}
    {match_param_tele: MTele}
    {match_ind_def: ind_def match_param_tele}
    {match_ind : ind_arg match_ind_def}
    {match_param_args: ArgsOf match_param_tele}
    (match_return_predicate: return_predicate_type match_param_args match_ind match_sort)
    {match_indices: indices_of match_ind_def match_param_args}
    (match_val: val_of_ind match_ind match_indices) :
  S.stype_of match_sort :=
  let p := apply_val (s:=Typeₛ) match_return_predicate match_indices in
  let p := apply_curry_sort p in
  p match_val.

(* Definition constrs_wop *)
(*     (** the shape of the inductive's parameters  *) *)
(*     {match_param_tele: MTele} *)
(*     (** the shape of the inductive type's indices *) *)
(*     {match_ind_def: ind_def match_param_tele} *)
(*     (** the actual inductive type (quantifying over its parameters) *) *)
(*     {match_ind : ind_arg match_ind_def} *)
(*     (** the shape of the inductive's constructors *) *)
(*     (match_constrs_sig: constrs_def_wop (ind_sig_arity (ind_def_sig match_ind_def))) := *)
(*   (mfold_right (fun c acc => constr_def_value_wop match_ind c *m acc) unit) match_constrs_sig. *)

Definition branches_type
    {match_sort: S.Sort}
    {match_param_tele: MTele}
    {match_ind_def: ind_def match_param_tele}
    {match_ind : ind_arg match_ind_def}
    {match_constrs_sig: constrs_def_wop (ind_sig_arity (ind_def_sig match_ind_def))}
    {match_param_args: ArgsOf match_param_tele}
    (match_constrs: constrs_wop _ match_constrs_sig)
    (match_return_predicate: return_predicate_type match_param_args match_ind match_sort)
  :=
      zip_dep_fold
        (fun (csig : constr_def_wop _) (c: constr_def_value_wop _ csig) =>
           (* [csig     ≈ ∀ x .. y, Ind j .. k] *)
           (* [c : csig ≈ λ x .. y, constr] *)
           (* trying to build:
              [∀ x .. y, R j .. k (c x .. y)]
            *)
           let c := apply_val (s:=Typeₛ) c match_param_args in
           let c := apply_curry_sort c in
           (* quantify over [x .. y] *)
           MTele_val
             (s:=match_sort)
             (n:=apply_constT (constr_def_wop_tele csig) match_param_args)
             (
               curry_sort
                 match_sort
                 (fun c_args : ArgsOf (apply_constT (constr_def_wop_tele csig) match_param_args) =>
                    (* [c_args ≈ x .. y] *)
                    let c := apply_val (s:=ind_sig_sort _) c c_args in
                    let c : apply_sort _ _ := apply_curry_sort c in
                    return_type_for match_return_predicate c
                 )
             )
        )
        match_constrs.


(* Record Match_Full := *)
(*   { *)
(*     (** the shape of the inductive's parameters  *) *)
(*     match_param_tele: MTele; *)
(*     (** the shape of the inductive type's indices *) *)
(*     match_ind_def: ind_def match_param_tele; *)
(*     (** the actual inductive type (quantifying over its parameters) *) *)
(*     match_ind : ind_arg match_ind_def; *)
(*     (** the shape of the inductive's constructors *) *)
(*     match_constrs_sig: constrs_def_wop (ind_sig_arity (ind_def_sig match_ind_def)); *)
(*     (** the inductive constructors. *)
(*         the constructors are specified with explicit quantifiers for parameters. *)
(*      *) *)
(*     match_constrs: constrs_wop match_constrs_sig; *)

(*     (** the parameters of the discriminant *) *)
(*     match_param_args: ArgsOf match_param_tele; *)
(*     (** the indices of the inductive value being matched on *) *)
(*     match_indices: indices_of match_ind_def match_param_args; *)
(*     (** the value being matched on  *) *)
(*     match_val: val_of_ind match_ind match_indices; *)

(*     (** the sort of the match, i.e. the Sort of the return type. *) *)
(*     match_sort: S.Sort; *)
(*     (** the return predicate [R : ∀ j .. k, I j .. k -> Type]  *) *)
(*     match_return_predicate: return_predicate_type match_param_args match_ind match_sort; *)
(*     (** the   *) *)
(*     match_branches: branches_type match_constrs match_return_predicate; *)
(*   }. *)

(* Definition number_of_inds (m : Mind) := *)
(*   mlength (mind_spec_ind_sigs (mind_spec m)). *)
(* Definition index_of_mind m := *)
(*   msigT (fun n => BinNat.N.to_nat n < number_of_inds m). *)

Definition ind_def_of (m : Mind_Entry) : ind_def (mind_spec_params (mind_spec (mind_entry_mind m))) :=
  nth (BinNat.N.to_nat (mind_entry_index m)) (mind_spec_ind_sigs (mind_spec (mind_entry_mind m)))
.

Definition ind_arg_of m :=
  netuple_nth (BinNat.N.to_nat (mind_entry_index m)) ((mind_inds (mind_entry_mind m))).

Definition constrs_sigs_of m :
  constrs_def_wop (ind_sig_arity (ind_def_sig (ind_def_of m))) :=
  let constrs := ind_args_get (mind_spec_constr_sigs _) (mind_inds _) in
  netuple_nth (BinNat.N.to_nat (mind_entry_index m)) (constrs).

Definition constrs_of m :
  constrs_wop (ind_arg_of m) (constrs_sigs_of m) :=
  constrs_types_nth _ _ _ (mind_constrs _)
.


NonCumulative Record Match
  :=
    {
      match_mind_entry: Mind_Entry;
      (** the parameters of the discriminant *)
      match_param_args: ArgsOf (mind_spec_params (mind_spec (mind_entry_mind match_mind_entry)));
      (** the indices of the inductive value being matched on *)
      match_indices: indices_of (ind_def_of match_mind_entry) match_param_args;
      (** the value being matched on  *)
      match_val: val_of_ind (ind_arg_of match_mind_entry) match_indices;

      (** the sort of the match, i.e. the Sort of the return type. *)
      match_sort: S.Sort;
      (** the return predicate [R : ∀ j .. k, I j .. k -> Type]  *)
      match_return_predicate: return_predicate_type match_param_args (ind_arg_of match_mind_entry ) match_sort;
      (** the branches *)
      match_branches: branches_type (constrs_of match_mind_entry) match_return_predicate;
    }.


Record Case :=
    mkCase {
        case_ind : Type;
        case_val : case_ind;
        case_return : dyn;
        case_branches : mlist dyn
        }.
