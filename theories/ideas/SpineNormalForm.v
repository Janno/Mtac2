From Mtac2 Require Import Mtac2 MFix.
From Mtac2.intf Require Import Case MTele Sorts.
From Mtac2.lib Require Import Logic Specif.

Local Close Scope tactic.
Set Universe Polymorphism.

Structure Normalizer :=
  {
    norm_type : Type;
    normalizer : forall v : norm_type, M m:{ v' : norm_type & v' =m= v }
  }.

Fixpoint extend_tele {m : MTele} : (ArgsOf m -> MTele) -> MTele :=
  match m as m return (ArgsOf m -> MTele) -> MTele with
  | mBase => fun n : (unit -> MTele) => n tt
  | mTele F =>
    fun n : (ArgsOf (mTele F) -> MTele) =>
      mTele (fun a => extend_tele (fun args => n (mexistT (fun a => ArgsOf (F a)) a args)))
  end.

Fixpoint args_extend {m : MTele} :
  forall {n : ArgsOf m -> MTele},
    ArgsOf (extend_tele n) ->
    m:{ args_m &
        ArgsOf (n args_m)
      }
  :=
    match m as m return
          forall {n : ArgsOf m -> MTele},
            ArgsOf (extend_tele n) ->
            m:{ args_m &
                ArgsOf (n args_m)
              }
    with
    | mBase => fun n args_n => mexistT _ tt args_n
    | mTele F =>
      fun n '(mexistT _ a args) =>
        let '(mexistT _ args_m args_n) := args_extend args in
        mexistT _ (mexistT _ a args_m) args_n
    end.

Fixpoint extend_args {m : MTele} : forall {n : ArgsOf m -> MTele},
  forall args_m : ArgsOf m, ArgsOf (n args_m) -> ArgsOf (extend_tele n) :=
  match m with
  | mBase => fun _ '(tt) args_n => args_n
  | mTele F => fun _ '(mexistT _ a args_m) args_n => mexistT _ a (extend_args args_m args_n)
  end
.

Section SpNF.

  Definition nth_ind (i : Mutual.Val) (n : nat) : Inductive.Def _ := NEList.nth n (Mutual.ind_defs (Mutual.def i)).

  Definition nth_ind_val (i : Mutual.Val) (n : nat) :
    _ :=
    NEList.netuple_nth n (Mutual.inds i).

  Definition SpNFTele_inner (i : Mutual.Val) (n : nat) params : MTele :=
    extend_tele (
        (fun indices =>
           mTele (fun v : Inductive.Inhab (p_args:=params) (nth_ind_val i n) indices => mBase)
        )
      ).

  Definition SpNFTele (i : Mutual.Val) n : MTele :=
    extend_tele (SpNFTele_inner i n).

  Definition SpNFType i n :=
    curry_sort
      Typeₛ
      (
        fun args : ArgsOf (SpNFTele i n) =>
          let '(mexistT _ args_param args) := args_extend args in
          let '(mexistT _ args_indices (mexistT _ arg_i _)) := args_extend args in
          m:{ i' & i' =m= arg_i }
      )
  .

  Definition nth_of (val : Mutual.Val) n :=
    {|Mutual.val := val;
      Mutual.index:= n;
      Mutual.params_given:= 0;
      Mutual.indices_given:= 0|}.

  Definition nth_type (val : Mutual.Val) n :=
    SpNFType val n.


  Fixpoint curry_sort_apply {s : S.Sort} {m : MTele} : forall {f : ArgsOf m -> s} {a : ArgsOf m}, f a -> apply_sort (curry_sort s f) a :=
    match m as m return
          forall (f : ArgsOf m -> s) (a : ArgsOf m), f a -> apply_sort (curry_sort s f) a
    with
    | mBase => fun f '(tt) t => t
    | mTele F => fun f '(mexistT _ a args) t => curry_sort_apply (m :=F a) t
    end.


  Definition zip_dep_fold_ind {P : Type -> Type}
           (A : Type) (F : A -> Type) (G : forall a : A, F a -> Type)
           (p0 : P unit)
           (pS :
              forall (l : mlist A) (H : mfold_right (fun (a : A) (acc : Type) => F a *m acc) unit l) (a : A) (X : F a),
                P (Match.zip_dep_fold G H) ->
                P (G a X *m Match.zip_dep_fold G H)
           )
           (l : mlist A) (H : mfold_right (fun (a : A) (acc : Type) => F a *m acc) unit l):
    P (Match.zip_dep_fold G H).
  Proof.
    revert l H. induction l. intros H.
    - refine p0.
    - intros. cbn. apply pS. destruct H. cbn. refine (IHl _).
  Defined.

  Definition branches_for_constrs (val : Mutual.Val) n params P :
    (forall def
            args_c
            (c : Constructor.Par.Typ def (NEList.netuple_nth n (Mutual.inds val))),
        M (Match.return_type_for P (apply_curry_sort (apply_val (apply_curry_sort (apply_val (s:=S.Type_sort) c params)) args_c)))
    ) ->
    M (Match.branches_type (match_sort:=Propₛ) (match_param_args:=params) (Constructor.Par.Vals_Mut_nth n (Mutual.constrs val)) P).
  Proof.
    intros F.
    refine (@zip_dep_fold_ind (fun x => M x) _ _ _ _ _ _ _). exact (M.ret tt).
    intros. cbn.
    refine (M.bind H0 _). intros H1.
    refine (M.bind (\nu args_c, _ : M (forall args_c, _)) _); cycle 1.
    intros. refine (M.ret (m: _,_)); cycle 1.
    exact H1.
    refine (curry_val (s:=Propₛ) _).
    intros.
    refine (curry_sort_apply (s:=Propₛ) _). red.
    apply (X0 a0).
    refine (M.bind (F _ _ _) _). intros t.
    refine (M.abs_fun args_c t).
  Defined.

  Fixpoint apply_curry_val {s m} : forall {T f a}, @apply_val s m T (curry_val f) a =m= f a :=
    match m as m return
         forall {T f a}, @apply_val s m T (curry_val f) a =m= f a
    with
    | mBase => fun _ _ 'tt => meq_refl
    | mTele F =>
      fun T f '(mexistT _ a args) =>
        let r := @apply_curry_val s _ (T a) (fun args => f (mexistT _ a args)) args in
      ltac:(destruct s; refine r)
    end
  .

  Tactic Notation "diff" uconstr(B) uconstr(T) :=
    let rec diff :=
    let T := (eval hnf in T) in
    let B := (eval hnf in B) in
    let p := constr:((m: T, B)) in
    match p with
    | (m: ?H, ?H) => fail 0 "the types are the same!"
    | (m: ?H1 ?X, ?H2 ?X) => diff H1 H2
    | (m: ?X, ?Y) => fail 0 X "different from" Y
    end in diff B T.

  Tactic Notation "cast'" open_constr(B) open_constr(t) :=
    refine (t : B) ||
    let T := type of t in
    diff B T.

  Time Definition body_for (val : Mutual.Val) (n : nat)
             (Fix : forall n, MTele_val (MTele_C Typeₛ Propₛ M (SpNFType val n)))
    :
    M (MTele_val (MTele_C Typeₛ Propₛ M (SpNFType val n))) :=
    let pred args_param :=
        curry_val
          (s:=Typeₛ)
          (fun args_indices : ArgsOf (apply_constT (Inductive.arity _) args_param) =>
             curry_sort_apply
               (s:=Typeₛ)
               (fun i => M m:{ i' & i' =m= i})
          )
    in

    branches <- (\nu args_param,
        branches_for_constrs
          val
          n
          args_param
          (pred args_param)
          (fun _ args_c c =>
             let indices := apply_val (s:=Typeₛ) (Constructor.Par.indices _) args_param in
             let indices := apply_curry_sort indices in
             let indices := apply_const (s:=Typeₛ) indices args_c in
             let inhab := apply_val (s:=Typeₛ) c args_param in
             let inhab := apply_curry_sort (s:=Typeₛ) inhab in
             let inhab := apply_val (s:=_) inhab args_c in
             let inhab := apply_curry_sort inhab in
             let arg_i : ArgsOf (mTele (fun i : Inductive.Inhab _ indices => mBase)) :=
                 mexistT _ inhab (tt : ArgsOf mBase) in
              let t := apply_val (s:=Propₛ) (Fix n) (extend_args args_param (extend_args indices arg_i)) in
              let t := apply_curry_sort t in
              (* coq does not know that [t] has the right type. The problem is
              that [mfix] expresses the type differently from what [Match.Val]
              requires. *)
              M.coerce t
          )
          >>= M.abs_fun args_param
                );

    t <- (\nu args : ArgsOf (SpNFTele val n),
                     m <-
                       (let args_param := mprojT1 (args_extend args) in
        let args := mprojT2 (args_extend args) in
        let args_indices := mprojT1 (args_extend args) in
        let args := mprojT2 (args_extend args) in
        let arg_i := mprojT1 (args) in

        ltac:(cast' (M (apply_curry_sort (apply_val (pred (mprojT1 _)) (mprojT1 _)) (mprojT1 _))) (M.build_match {|
            Match.mind_entry := nth_of val n;
            Match.param_args := args_param;
            Match.indices := args_indices;
            Match.val := arg_i;
            Match.sort := Propₛ;
            Match.return_predicate := (pred args_param);
            Match.branches := branches args_param;
          |}))
        );
        (* >>= M.abs_let arg_i _ *)
        (* >>= M.abs_let args_indices _ *)
          (* >>= M.abs_let args_param _ *)
        let m := apply_curry_sort_inv (s:=Propₛ) m in
        M.abs_fun args m
         );
    (* As above, we need to convince Coq that we can massage the types. *)
    t <- M.coerce t;
    M.ret (curry_val (s:=Propₛ) t)
  .

  Fixpoint val_to_sortP m :
    forall T, @MTele_val Propₛ m T -> @MTele_sort Propₛ m T :=
    match m as m return
          forall T, @MTele_val Propₛ m T -> @MTele_sort Propₛ m T
    with
    | mBase => fun (T : Prop) (t : T) => t
    | mTele F => fun T t x => val_to_sortP (F x) (T x) (t x)
  end.

  Definition build_normalizer_for (val : Mutual.Val) :=
    let tele := mTele (fun n => SpNFTele val n) in
    (* we are constructing a fixpoint of the following form:
       mfix F k P_k_1 .. P_k_pk I_k_1 .. I_k_ik (i : T_k P_k_1 .. P_k_pk I_k_1 .. I_k_ik) : M (m:{ i' : i' =m= i }) :=
       match k with
       | 0 => <normalize and return value of first inductive>
       | S 0 => <normalize and return value of second inductive>
       | ...
       | S _ => <normalize and return value of last inductive> (* this is also the default branch *)
       end
     *)
    branches <-
      (\nu k, \nu F,
       t <- body_for val k F;
       t <- M.abs_fun F t;
       M.abs_fun k t
      );
    let mfix_ :=
        MFixDef.mfix'
          (m := tele)
          (fun n => SpNFType val n)
          (fun F k => branches k F
          ) in
    M.ret (mexistT
            (fun val => forall n, MTele_sort (MTele_C Typeₛ Propₛ M (SpNFType val n)))
            val
            (val_to_sortP _ _ (mfix_))
          )
  .


  Definition build_normalizer (i : Type) :
    M m:{ val : Mutual.Val &
                forall n, MTele_sort (MTele_C Typeₛ Propₛ M (SpNFType val n))
        } :=
    '{| Mutual.val := val |} <- M.inspect_mind i; (* ignore everything else *)
    build_normalizer_for val.

End SpNF.

Set Printing All.
Mtac Do (M.inspect_mind nat >>= fun '{|Mutual.val := val|} => M.print_term val).

Let nat_val :=
(Mutual.Build_Val
   (Mutual.Build_Def false mBase
      (@NEList.ne_sing (Inductive.Def mBase)
         (Inductive.Build_Def mBase
            (String (Ascii.Ascii false true true true false true true false)
               (String (Ascii.Ascii true false false false false true true false)
                  (String (Ascii.Ascii false false true false true true true false) EmptyString)))
            (Inductive.Build_Sig mBase S.Type_sort mBase)))
      (fun nat : Set =>
       @mcons (@Constructor.Par.Def mBase mBase)
         (Constructor.Par.Build_Def mBase mBase
            (String (Ascii.Ascii true true true true false false true false) EmptyString) mBase tt)
         (@mcons (@Constructor.Par.Def mBase mBase)
            (Constructor.Par.Build_Def mBase mBase
               (String (Ascii.Ascii true true false false true false true false) EmptyString)
               (@mTele nat (fun _ : nat => mBase)) (fun _ : nat => tt)) (@mnil (@Constructor.Par.Def mBase mBase)))))
   nat (@mpair nat (mprod (forall _ : nat, nat) unit) O (@mpair (forall _ : nat, nat) unit S tt))).


Let x := Eval hnf in build_normalizer_for nat_val.

Timeout 30 Mtac Do (build_normalizer_for nat_val >>= M.print_term).
