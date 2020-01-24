From Coq Require Import BinNums String.
From Mtac2 Require Import Datatypes List NEList.
Import ProdNotations.
From Mtac2.intf Require Import Dyn MTele Sorts.
From Mtac2.lib Require Import Datatypes Specif.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Set Polymorphic Inductive Cumulativity.

(** Dynamically-typed representations of inductive types and matches.  *)
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

(** Statically-typed representations of inductive types and matches.  *)

Module Inductive.
  Record Sig@{p pi po i} {params : MTele@{p}} : Type :=
    {
      sort : S.Sort;
      arity : MTele_ConstT@{p pi po} MTele@{i} params;
    }.
  Arguments Sig _ : clear implicits.

  (** A set of mutually-defined inductive signatures is represented by a
      non-empty list of [Sig]s. *)
  Definition Sigs params := nelist (Sig params).

  (** An inductive Typ's definition [Def] consists of a name and a signature.
      We register the signature component [sig] as a coercion.
   *)
  Record Def@{p+} {params: MTele@{p}} : Type :=
    { name : string; sig :> Sig params }.
  Arguments Def _ : clear implicits.


  (** The full Typ of an inductive signature including its parameters. *)
  Definition Typ@{p+} {params : MTele@{p}} (i : Sig params) : Type :=
    MTele_val (
        curry_sort
          Typeₛ
          (fun a' : ArgsOf@{p} params => MTele_Sort (sort i) (apply_constT (arity i) a'))
      ).

  (** A product of values of mutually-defined inductive types.  *)
  Definition Vals_Mut {params} (sigs : Sigs params) :Type :=
    reduce mprod (map Typ sigs).

  (** A chain of implications of inductive Typ's [Typ]s leading culminating in
      [Type] [to]. *)
  Definition bind_in {params} (sigs : Sigs params) (to : Type) : Type :=
    fold_right (fun sig accu => Typ sig -> accu) to sigs.

  (** Extracting a value from [bind_in]. *)
  Fixpoint extract_bound_in
           {T}
           {params}
           {sigs : Inductive.Sigs params} :
    forall
      (css : Inductive.bind_in sigs T)
      (is : Inductive.Vals_Mut sigs),
      T :=
    match sigs as sigs return
          forall
            (css : Inductive.bind_in sigs T)
            (is : Inductive.Vals_Mut sigs),
            T
    with
    | ne_sing sig => fun css is => css is
    | ne_cons sig sigs =>
      fun css '(m: ia, is) =>
        extract_bound_in (css ia) is
    end.



  (** Given a parameter assignment, describe the type of an index assignment for
      a given inductive signature. *)
  Definition Index_Typ
             {params}
             (i: Inductive.Sig params)
             (p_args : ArgsOf params) :=
    ArgsOf (apply_constT (Inductive.arity i) p_args).

  (** The type of inhabitants of an inductive type applied to its parameters and
      indices. *)
  Definition Inhab
             {params}
             {i : Inductive.Sig params}
             {p_args : ArgsOf params}
             (ia : Inductive.Typ i)
             (i_args : Inductive.Index_Typ i p_args)
    : Type :=
    let ia := apply_val (s:=Typeₛ) ia p_args in
    let ia := apply_curry_sort ia in
    apply_sort ia i_args
  .

End Inductive.

Module Constructor.

  (** Unparametrized constructors, i.e. representations of constructors that
      exist only in a context that contains a valid parameter assignment. All
      types are expressed w.r.t. to this implicitly available parameter
      assignment.

      This representation corresponds to the output of [Check
      <some_inductive_Typ.>] where the constructors do *not* quantify over
      their parameters. *)
  Module Unpar.
    (** A constructor's definition [Def] consists of a name, a telescope of
        arguments, and an assignment of indices. *)
    Record Def {ind_mt : MTele} : Type :=
      {
        name : string;
        tele : MTele;
        indices : MTele_ConstT (ArgsOf ind_mt) tele;
      }.

    Arguments Def _ : clear implicits.

    (** The actual Typ of constructor [c] given an inductive [ind] of sort [sort_ind]. *)
    Definition Typ {ind_mt} (sort_ind : S.Sort)
               (ind : MTele_Sort sort_ind ind_mt)
               (c : Def ind_mt):
      Type :=
      MTele_val (
          curry_sort
            sort_ind
            (fun c_args =>
               let i_args := apply_const (s:=Typeₛ) (indices c) c_args in
               apply_sort ind i_args
            )
        ).

  (** A list of constructors of one inductive Typ.  *)
    Definition Defs (ind_mt : MTele) : Type :=
      mlist (Def ind_mt).

  (** A collection of lists of constructors, one list for each inductive in a
      (non-empty) list of mutually-defined inductive types. *)
    Definition Defs_Mut {params} (sigs : Inductive.Sigs params) (a : ArgsOf params) :=
      let cs := map (fun i =>
                       let ind := Inductive.arity i in
                       Defs (apply_constT ind a)
                    ) sigs
      in reduce mprod cs.

    Definition Typs {params} (sigs : Inductive.Sigs params) :=
      Inductive.bind_in sigs (MTele_val (curry_sort Typeₛ (Defs_Mut sigs))).

  End Unpar.


  (** Parametrized constructors, i.e. representations that carry with them the
      quantifiers for their parameters.

      This representation corresponds to output of [Check <some_constructor>]
      where the Typ printed contains the quantifiers of the constructor's
      parameters. *)
  Module Par.


    Record Def {params} {ind : MTele_ConstT MTele params} :=
      {
        name : string;
        tele : MTele_ConstT MTele params;
        indices : MTele_val (curry_sort Typeₛ (fun args => MTele_ConstT (ArgsOf (apply_constT ind args)) (apply_constT tele args)));
      }.
    Arguments Def {_} _.

    (** The full Typ of the constructor, including the quantifiers of its
        parameters. This function can only return a Typ relative to a __value__
        of the constructor's inductive Typ. *)
    Definition Typ
               {params}
               {i : Inductive.Sig params}
               (c : Def (Inductive.arity i))
               (ia: Inductive.Typ i)
      : Type :=
      MTele_val (
          curry_sort
            Typeₛ
            (fun p_args =>          (* packed parameters of [i] *)
               let c_inds := apply_val (s:=Typeₛ) (indices c) p_args in
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

    Definition Defs {params} (ind : MTele_ConstT MTele params) :=
      mlist (Def ind).

    Definition Defs_Mut {params} (sigs : Inductive.Sigs params) : Type :=
      let cs_defs := map (fun sig => Defs (Inductive.arity sig)) sigs
      in reduce mprod cs_defs.

    Definition Typs {params} (sigs : Inductive.Sigs params) :=
      Inductive.bind_in sigs (Defs_Mut sigs).

    (** A product of constructor values for a given inductive signature and its value.  *)
    Definition Vals {params} {sig : Inductive.Sig params}
      (cs : mlist (Def (Inductive.arity sig)))
      (ia : Inductive.Typ sig) : Type :=
      mfold_right (fun c acc => Typ c ia *m acc) unit cs.

    Fixpoint Vals_Mut {params} {sigs : Inductive.Sigs params} :
      forall
        (css : Constructor.Par.Defs_Mut sigs)
        (ias : Inductive.Vals_Mut sigs),
        Type
      :=
        match sigs as sigs return
              forall
                (css : Constructor.Par.Defs_Mut sigs)
                (ias : Inductive.Vals_Mut sigs), Type
      with
      | ne_sing sig =>
        fun cs ia => Vals cs ia
      | ne_cons sig sigs =>
        fun '(m: cs, css) '(m: ia, ias) => Vals cs ia  *m Vals_Mut css ias
      end.

    Fixpoint Vals_Mut_nth
             {params} {sigs : Inductive.Sigs params} (n : nat) :
      forall
        {css : Constructor.Par.Defs_Mut sigs}
        {ias : Inductive.Vals_Mut sigs},
        Constructor.Par.Vals_Mut css ias -> Constructor.Par.Vals (netuple_nth n css) (netuple_nth n ias) :=
      match sigs as sigs, n as n return
            forall
              (css : Constructor.Par.Defs_Mut sigs)
              (ias : Inductive.Vals_Mut sigs),
              Constructor.Par.Vals_Mut css ias -> Constructor.Par.Vals (netuple_nth n css) (netuple_nth n ias)
      with
      | ne_sing sig, 0 => fun _ _ t => t
      | ne_sing sig, _ => fun _ _ t => t
      | ne_cons _ _, 0 => fun '(m: _, _) '(m: _, _) '(m: t, _) => t
      | ne_cons _ sigs, S n => fun '(m: _, _) '(m: _, _) '(m: _, cts) => Vals_Mut_nth n cts
      end
    .

    Definition Vals_Mut_Typs
               {params}
               {sigs : Inductive.Sigs params}
               (css : Typs sigs)
               (is : Inductive.Vals_Mut sigs) :
      Type :=
      Constructor.Par.Vals_Mut (Inductive.extract_bound_in css is) is.

  End Par.
End Constructor.

Module Mutual.

  (** A representation of a set of mutually-inductive types with their
      constructors fully parametrized. *)
  Record Def :=
    {
      polymorphic: bool;
      params : MTele;
      ind_defs : nelist (Inductive.Def params);
      constr_defs : Constructor.Par.Typs (map Inductive.sig ind_defs);
    }.

  Record Val :=
    {
      def : Def;
      inds : Inductive.Vals_Mut (map Inductive.sig (ind_defs def));
      constrs : Constructor.Par.Vals_Mut_Typs (constr_defs def) (inds)
    }.

  Record Nth :=
    {
      val: Val;
      index: N;
      params_given: N;
      indices_given: N;
    }.
End Mutual.


Module Match.

  Definition return_predicate_type
             {params}
             {i : Inductive.Sig params}
             (p_args : ArgsOf params)
             (ia : Inductive.Typ i)
             (s : S.Sort)
  : Type :=
    MTele_val
      (
        curry_sort
          Typeₛ
          (fun i_args =>
             apply_sort (apply_curry_sort (apply_val (s:=Typeₛ) ia p_args)) i_args -> s
          )
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
             {match_ind_def: Inductive.Sig match_param_tele}
             {match_ind : Inductive.Typ match_ind_def}
             {match_param_args: ArgsOf match_param_tele}
             (match_return_predicate: return_predicate_type match_param_args match_ind match_sort)
             {match_indices: Inductive.Index_Typ match_ind_def match_param_args}
             (match_val: Inductive.Inhab match_ind match_indices) :
    S.stype_of match_sort :=
    let p := apply_val (s:=Typeₛ) match_return_predicate match_indices in
    let p := apply_curry_sort p in
    p match_val.

  Definition branches_type
             {match_sort: S.Sort}
             {match_param_tele: MTele}
             {match_ind_def: Inductive.Sig match_param_tele}
             {match_ind : Inductive.Typ match_ind_def}
             {match_constrs_sig: Constructor.Par.Defs (Inductive.arity match_ind_def)}
             {match_param_args: ArgsOf match_param_tele}
             (match_constrs: Constructor.Par.Vals match_constrs_sig _)
             (match_return_predicate: return_predicate_type match_param_args match_ind match_sort)
    :=
      zip_dep_fold
        (fun (csig : Constructor.Par.Def _) (c: Constructor.Par.Typ csig _) =>
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
             (n:=apply_constT (Constructor.Par.tele csig) match_param_args)
             (
               curry_sort
                 match_sort
                 (fun c_args : ArgsOf (apply_constT (Constructor.Par.tele csig) match_param_args) =>
                    (* [c_args ≈ x .. y] *)
                    let c := apply_val (s:=Inductive.sort _) c c_args in
                    let c : apply_sort _ _ := apply_curry_sort c in
                    return_type_for match_return_predicate c
                 )
             )
        )
        match_constrs.

  Definition ind_sig_of (m : Mutual.Nth) :
    Inductive.Sig (Mutual.params (Mutual.def (Mutual.val m))) :=
    nth (BinNat.N.to_nat (Mutual.index m)) (map Inductive.sig (Mutual.ind_defs (Mutual.def (Mutual.val m))))
  .

  Definition ind_arg_of m :=
    netuple_nth (BinNat.N.to_nat (Mutual.index m)) ((Mutual.inds (Mutual.val m))).

  Definition constrs_sigs_of m :
    Constructor.Par.Defs (Inductive.arity (ind_sig_of m)) :=
    let constrs := Inductive.extract_bound_in (Mutual.constr_defs _) (Mutual.inds _) in
    netuple_nth (BinNat.N.to_nat (Mutual.index m)) (constrs).

  Definition constrs_of m :
    Constructor.Par.Vals (constrs_sigs_of m) (ind_arg_of m) :=
    Constructor.Par.Vals_Mut_nth _ (Mutual.constrs _)
  .

  NonCumulative Record Val
    :=
      {
        match_mind_entry: Mutual.Nth;
        (** the parameters of the discriminant *)
        match_param_args: ArgsOf (Mutual.params (Mutual.def (Mutual.val match_mind_entry)));
        (** the indices of the inductive value being matched on *)
        match_indices: Inductive.Index_Typ (ind_sig_of match_mind_entry) match_param_args;
        (** the value being matched on  *)
        match_val: Inductive.Inhab (ind_arg_of match_mind_entry) match_indices;

        (** the sort of the match, i.e. the Sort of the return type. *)
        match_sort: S.Sort;
        (** the return predicate [R : ∀ j .. k, I j .. k -> Type]  *)
        match_return_predicate: return_predicate_type match_param_args (ind_arg_of match_mind_entry) match_sort;
        (** the branches *)
        match_branches: branches_type (constrs_of match_mind_entry) match_return_predicate;
      }.

  Definition return_type_of (m : Val) :=
    return_type_for (match_return_predicate m) (match_val m).

End Match.
