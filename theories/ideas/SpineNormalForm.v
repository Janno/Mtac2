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

  Definition SpNFTyTy i n :=
    curry_sort Typeₛ
      (
        fun args : ArgsOf (SpNFTele i n) =>
          let '(mexistT _ args_param args) := args_extend args in
          let '(mexistT _ args_indices (mexistT _ arg_i _)) := args_extend args in
          Type
      ).

  Definition SpNFType i n :=
    curry_val (T:=SpNFTyTy i n)
      (s:=Typeₛ)
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


  Definition nat_ind : Mutual.Nth := ltac:(mrun (M.inspect_mind nat)).

  Definition match_on_N {P: nat -> Prop} (p0 : P 0) (pS : forall n, P (S n)) (n : nat): Match.Val :=
    {|
      Match.mind_entry := nat_ind;
      Match.param_args := tt;
      Match.indices := tt;
      Match.val := n;
      Match.sort := Propₛ;
      Match.return_predicate := P;
      Match.branches := (m: p0; pS; tt)
    |}.

  Fixpoint first_n_branch_types_acc (P : nat -> Prop) (n : nat) (acc : nat) :=
    match n with
    | 0 => P acc : Type
    | S n => P acc *m first_n_branch_types_acc P n (S acc)
    end.

  Definition first_n_branch_types (P : nat -> Prop) (n: nat) :=
    first_n_branch_types_acc P n 0.

  Require Import Fin.

  Definition bounded_pred (P : nat -> Prop) (n : nat) :=
    (forall m, m <= n -> P m) -> forall m, P m.

  Fixpoint to_nat {n} (k : Fin.t n) : nat :=
    match k in Fin.t n with
    | F1 => 0
    | FS k => S (to_nat k)
    end.

  Program Fixpoint of_nat_cert (n k : nat) : sum ({k' : Fin.t n & to_nat k' = k }) (n <= k) :=
    match n as n return
          sum ({k' : Fin.t n & to_nat k' = k }) (k >= n)
    with
    | 0 => inr (le_0_n _)
    | S n =>
      match k as k return
            sum ({k' : Fin.t (S n) & to_nat k' = k }) (k >= S n)
      with
      | 0 => inl (existT _ F1 eq_refl)
      | S k =>
        match of_nat_cert n k return _ with
        | inl (existT _ k' eq) => inl (existT _ (FS k') _)
        | inr H => inr (Le.le_n_S _ _ H)
        end
      end
    end.

  Fixpoint plus_0 (n : nat) : n+0 = n :=
    match n as n return n+0 = n with
    | 0 => eq_refl
    | S n => f_equal _ (plus_0 n)
    end.

  Fixpoint plus_S (n m : nat) : n + S m = S n + m :=
    match n with
    | 0 => eq_refl
    | S n => f_equal _ (plus_S n m)
    end.

  Fixpoint get_branch {P} (acc : nat) {n} (k : Fin.t (S n)) : first_n_branch_types_acc P n acc -> P (acc + to_nat k) :=
    match k as k in Fin.t m return
          match m with
          | S m => first_n_branch_types_acc P m acc -> P (acc + to_nat k)
          | 0 => unit
          end
    with
    | @F1 n =>
      match n as n return first_n_branch_types_acc P n acc -> P (acc + 0) with
      | 0 => fun p0 => ltac:(rewrite plus_0; refine p0)
      | S n => fun '(m: p0, _) => ltac:(rewrite plus_0; refine p0)
      end
    | @FS n k =>
      match n as n return forall k : Fin.t n, first_n_branch_types_acc P n acc -> P (acc + S (to_nat k)) with
      | 0 => Fin.case0 _
      | S n => fun k '(m: p, ps) => ltac:(rewrite plus_S; refine (get_branch _ _ _ _ ps))
      end k
    end.

  Fixpoint first_n_branches {P : nat -> Prop} (backup_plan : forall k, P k) {n} :
    first_n_branch_types P n -> forall k, P k :=
    fun bs k =>
    match of_nat_cert (S n) k with
    | inl (existT _ k' eq) =>
      match eq in _ = k return P k with
      | eq_refl => get_branch 0 _ bs
      end
    | inr _ => backup_plan _
    end
  .

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

  Definition build_normalizer (i : Type) :
    M m:{ val : Mutual.Val &
                forall n, MTele_sort (MTele_C Typeₛ Propₛ M (SpNFType val n))
        } :=
    '{| Mutual.val := val |} <- M.inspect_mind i; (* ignore everything else *)
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
    M.print_term mfix_;;
    M.ret (mexistT
            (fun val => forall n, MTele_sort (MTele_C Typeₛ Propₛ M (SpNFType val n)))
            val
            ltac:(refine (fun n => mfix_ n))
          )
  .
