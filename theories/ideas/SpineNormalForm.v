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


Fixpoint nu_args {T} {n : MTele} : (ArgsOf n -> M T) -> M T :=
  match n as n return (ArgsOf n -> M T) -> M T with
  | mBase => fun f => \nu a, f a
  | mTele F => fun f => \nu a, nu_args (n:=F a) (fun args => f (mexistT _ a args))
  end.

Fixpoint abs_fun_args {n} : forall {P : ArgsOf n -> Type} (args : ArgsOf n), P args -> M (forall args, P args) :=
  match n as n return
        forall {P : ArgsOf n -> Type} (args : ArgsOf n), P args -> M (forall args, P args)
  with
  | mBase =>
    fun P a (p : P a) =>
      M.abs_fun (P:=fun a => P a) a p
  | mTele F =>
    fun P '(mexistT _ a args) p =>
      p <- abs_fun_args (P:=fun args => P (mexistT _ a args)) args p;
      p <- M.abs_fun (P:=fun a => forall args, P (mexistT _ a args)) a p;
      M.ret (fun '(mexistT _ a args) => p a args)
  end
.

Notation "'\nu_AO' args0 .. args1 ,  t" := (nu_args (fun args0 => .. (nu_args (fun args1 => t)) ..)) (at level 200, args0 binder, args1 binder, t at level 200).

Fixpoint extend_tele {m : MTele} : (ArgsOf m -> MTele) -> MTele :=
  match m as m return (ArgsOf m -> MTele) -> MTele with
  | mBase => fun n : (sunit -> MTele) => n stt
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
    | mBase => fun n args_n => mexistT _ stt args_n
    | mTele F =>
      fun n '(mexistT _ a args) =>
        let '(mexistT _ args_m args_n) := args_extend args in
        mexistT _ (mexistT _ a args_m) args_n
    end.

Fixpoint extend_args {m : MTele} : forall {n : ArgsOf m -> MTele},
  forall args_m : ArgsOf m, ArgsOf (n args_m) -> ArgsOf (extend_tele n) :=
  match m as m return
        forall {n : ArgsOf m -> MTele},
        forall args_m : ArgsOf m, ArgsOf (n args_m) -> ArgsOf (extend_tele n)
  with
  | mBase => fun _ _ args_n => suTr (f:=fun a => (ArgsOf (_ a))) args_n
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
    | mBase => fun f _ t => suTr (f:=fun a => S.selem_of (f a)) t
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
    - intros. apply pS. destruct H. refine (IHl _).
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
    intros.
    refine (M.bind H0 _). intros H1.
    refine (M.bind (\nu_AO args_c, _) _); cycle 1.
    - intros.
      epose (H3 := curry_val (s:=Propₛ) (fun a => curry_sort_apply (s:=Propₛ) (X0 a))).
      pose (H4 := reduce (RedWhd RedAll) H3).
      refine (M.ret (m: H4,H1)).
    (* refine (curry_val (s:=Propₛ) _). *)
    (* intros. *)
    (* refine (curry_sort_apply (s:=Propₛ) _). *)
    (* refine (X0 a0). *)
    - refine (M.bind (F _ _ _) _). intros t.
      refine (abs_fun_args args_c t).
  Defined.

  (* Fixpoint apply_curry_val {s m} : forall {T f a}, @apply_val s m T (curry_val f) a =m= f a := *)
  (*   match m as m return *)
  (*        forall {T f a}, @apply_val s m T (curry_val f) a =m= f a *)
  (*   with *)
  (*   | mBase => fun _ _ _ => meq_refl *)
  (*   | mTele F => *)
  (*     fun T f '(mexistT _ a args) => *)
  (*       let r := @apply_curry_val s _ (T a) (fun args => f (mexistT _ a args)) args in *)
  (*     ltac:(destruct s; refine r) *)
  (*   end *)
  (* . *)

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

  (* Arguments M.bind _ _ & _ _. *)
  Arguments M.abs_fun _ _ _ & _.

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
               (fun i : Inductive.Inhab _ _ => M m:{ i' & i' =m= i})
          )
    in

    branches <- (\nu_AO args_param,
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
             let inhab := reduce (RedWhd (RedAll)) inhab in
             let inhab_type := reduce (RedWhd RedAll) (Inductive.Inhab _ indices) in
             let arg_i : ArgsOf (mTele (fun i : inhab_type => mBase)) :=
                 mexistT _ inhab (stt) in
              let t := apply_val (s:=Propₛ) (Fix n) (extend_args args_param (extend_args indices arg_i)) in
              let t := apply_curry_sort t in
              let t := reduce (RedWhd (RedAll)) t in
              (* coq does not know that [t] has the right type. The problem is
              that [mfix] expresses the type differently from what [Match.Val]
              requires. *)
              let A := _ in
              let B := _ in
              (* let A' := reduce RedVmCompute A in *)
              (* let B' := reduce RedVmCompute B in *)
              (* M.print_term A';; *)
              (* M.print_term B';; *)
              t <- M.coerce (A:=A) (B:=B) t;
              M.ret t

          )
          >>= abs_fun_args args_param
                );

    t <- (\nu_AO args : ArgsOf (SpNFTele val n),
                     m <-
                       (let args_param := mprojT1 (args_extend args) in
        let args := mprojT2 (args_extend args) in
        let args_indices := mprojT1 (args_extend args) in
        let args := mprojT2 (args_extend args) in
        let arg_i := mprojT1 (args) in

        let branches := reduce (RedWhd RedAll) (branches args_param) in


        ltac:(cast' (M (apply_curry_sort (apply_val (pred (mprojT1 _)) (mprojT1 _)) (mprojT1 _))) (
                      M.build_match {|
            Match.mind_entry := nth_of val n;
            Match.param_args := args_param;
            Match.indices := args_indices;
            Match.val := arg_i;
            Match.sort := Propₛ;
            Match.return_predicate := (pred args_param);
            Match.branches := branches;
          |}))
        );
        (* >>= M.abs_let arg_i _ *)
        (* >>= M.abs_let args_indices _ *)
          (* >>= M.abs_let args_param _ *)
        let m := apply_curry_sort_inv (s:=Propₛ) m in
        let m := reduce (RedWhd RedAll) m in
        abs_fun_args args m
         );
    (* As above, we need to convince Coq that we can massage the types. *)
    t <- M.coerce t;
    let t := reduce (RedWhd RedAll) (curry_val (s:=Propₛ) t) in
    M.ret (t)
  .

  (* Definition nat_ind := ltac:(mrun (M.inspect_mind nat >>= fun '{|Mutual.val := val|} => M.ret val)). *)

  (* Definition build_match (P : nat -> Prop) (p0: M (P 0)) (pS : forall n, M (P (S n))) (n : nat) : M (P n) := *)
  (*   M.build_match *)
  (*     {| *)
  (*       Match.mind_entry := nth_of nat_ind 0; *)
  (*       Match.param_args := mBase; *)
  (*       Match.indices := mBase; *)
  (*       Match.val := n; *)
  (*       Match.sort := Propₛ; *)
  (*       Match.return_predice := P; *)
  (*       Match.branches :=  *)
  (*     |}. *)

  Fixpoint val_to_sortP m :
    forall T, @MTele_val Propₛ m T -> @MTele_sort Propₛ m T :=
    match m as m return
          forall T, @MTele_val Propₛ m T -> @MTele_sort Propₛ m T
    with
    | mBase => fun (T : Prop) (t : T) => t
    | mTele F => fun T t x => val_to_sortP (F x) (T x) (t x)
  end.

  Definition build_normalizer_for (val : Mutual.Val):=
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
    (* branches <- *)
    (*   (\nu k, \nu F, *)
    (*    t <- body_for val k F; *)
    (*    t <- M.abs_fun F t; *)
    (*    M.abs_fun k t *)
    (*   ); *)
    let num_inds := NEList.length (Mutual.ind_defs (Mutual.def val)) in
    let num_inds := reduce RedVmCompute num_inds in
    (* below [i] will range from [0] to [num_inds - 1]. *)
    branches <-
      (
        mfix go (i : _) :
          M (forall k, MTele_val (MTele_C Typeₛ Propₛ M _) -> MTele_val (MTele_C Typeₛ Propₛ M (SpNFType val (i+k)))) :=
          match Peano_dec.dec_eq_nat (S i) (num_inds) with
          | or_introl eq =>
          (* It is rather tedious to prove that
             [SpNFType val (num_inds - 1 + k) = SpNFType val (num_inds - 1)]
             so we'll assert this dynamically
           *)
            \nu F,
              let i := reduce RedVmCompute (num_inds - 1) in
              t <- (body_for val i F);
              t <- M.abs_fun F t;
              M.coerce (fun k : nat => t)
          | or_intror _ =>
            M.failwith "unimplemented"
          end
      ) (0);
    let mfix_ :=
        MFixDef.mfix'
          (m := tele)
          (fun n => SpNFType val n)
          (fun F k => branches k F
          ) in
   let t := reduce (RedWhd RedAll) (val_to_sortP _ _ (mfix_)) in
    M.ret (mexistT
            (fun val => forall n, MTele_sort (MTele_C Typeₛ Propₛ M (SpNFType val n)))
            val
            (t)
          )
  .


  Definition build_normalizer (i : Type) :
    M m:{ val : Mutual.Val &
                forall n, MTele_sort (MTele_C Typeₛ Propₛ M (SpNFType val n))
        } :=
    '{| Mutual.val := val |} <- M.inspect_mind i; (* ignore everything else *)
    build_normalizer_for val.

End SpNF.

(* Set Printing All. *)
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
            (String (Ascii.Ascii true true true true false false true false) EmptyString) mBase stt)
         (@mcons (@Constructor.Par.Def mBase mBase)
            (Constructor.Par.Build_Def mBase mBase
               (String (Ascii.Ascii true true false false true false true false) EmptyString)
               (@mTele nat (fun _ : nat => mBase)) (fun _ : nat => stt)) (@mnil (@Constructor.Par.Def mBase mBase)))))
   nat (@mpair nat (mprod (forall _ : nat, nat) unit) O (@mpair (forall _ : nat, nat) unit S tt))).


Let x := Eval hnf in build_normalizer_for nat_val.

Mtac Do Set_Debug_Exceptions.
Set Unicoq Debug.
(* Set Printing All. *)
(* Set Printing Implicit. *)

Ltac what_the_stuck t :=
  (* idtac t; *)
  lazymatch t with
  (* reduction is blocked because of a fixpoint argument that doesn't reduce *)
  | (fix f x1 {struct x1} := _) ?a1 => what_the_stuck a1
  | (fix f x1 x2 {struct x1} := _) ?a1 ?a2 => what_the_stuck a1
  | (fix f x1 x2 {struct x2} := _) ?a1 ?a2 => what_the_stuck a2
  (* ... *)
  | ?f ?g =>
      (* reduction is blocked because of [f] *)
      what_the_stuck f
  | match ?v with | _ => _ end =>
    (* reduction is blocked because of [v] *)
    what_the_stuck v
  | _ =>
    (* reduction is blocked because of [t] itself *)
    idtac t
  end.

Axiom k : nat.

Check ltac:(
  let t := eval cbv in (k + 0) in
  what_the_stuck t).


Let t := Eval cbv in
(* (MTele_val (MTele_C Typeₛ Propₛ M (SpNFType nat_val (0 + k)))). *)
(NEList.netuple_nth (0 + k) (Mutual.inds nat_val)).
Let s : unit := ltac:(let t := eval unfold t in t in what_the_stuck t; refine tt).
Print s.

Mtac Do (build_normalizer_for
           nat_val >>=
           fun '(mexistT _ _ x) =>
           M.print_term x;;
           let y := reduce (RedStrong RedAll) (x 0) in
           M.print_term y;;
           M.declare dok_Definition "my_great_metaprogram" false y;;
           M.ret tt).

Set Printing Universes.
Set Printing All.

Monomorphic Definition false_test :=
       '{|Mutual.val := val|} <- M.inspect_mind (@False);
       M.print_term val;;
       build_normalizer_for
           val >>=
           fun '(mexistT _ _ x) =>
             (* M.print_term x;; *)
             (* let y := reduce (RedWhd RedAll) (x 0) in *)
             M.print_term "before_compute";;
             let y := reduce (RedVmCompute) (x 0) in
             M.print_term "after_compute";;
             M.print_term y;;
             M.print_term "before_declare";;
             M.declare dok_Definition "my_great_metaprogram_False" false y;;
             M.print_term "after_declare";;
             M.ret tt.
Print false_test.
Mtac Do false_test.

Mtac Do (
       '{|Mutual.val := val|} <- M.inspect_mind (@unit);
       build_normalizer_for
           val >>=
           fun '(mexistT _ _ x) =>
             (* M.print_term x;; *)
             let y := reduce (RedWhd RedAll) (x 0) in
             M.print_term y;;
             M.declare dok_Definition "my_great_metaprogram2" false y;;
             M.ret tt).

Mtac Do (
       '{|Mutual.val := val|} <- M.inspect_mind (@list);
       build_normalizer_for
           val >>=
           fun '(mexistT _ _ x) =>
             (* M.print_term x;; *)
             let y := reduce (RedWhd RedAll) (x 0) in
             M.print_term y;;
             M.declare dok_Definition "my_great_metaprogram2" false y;;
             M.ret tt).
