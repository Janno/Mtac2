From Mtac2 Require Import Mtac2 MFix MTeleMatch.
From Mtac2.intf Require Import MTele.
From Mtac2.lib Require Specif NEList.

Close Scope tactic_scope.

Record fn_into {T : Type} := FN_INTO
  {
    fn_into_tele : MTele;
    fn_into_type : MTele_ConstT unit fn_into_tele;
  }.
Arguments fn_into : clear implicits.
Arguments FN_INTO {_}.

Definition fn_into_of (T ind: Type) : forall (F : Type), M (fn_into ind) :=
  (mfix go (F : _) : M (fn_into ind) :=
    mtmmatch F as F return M (fn_into ind) with
  | T =u> M.ret (FN_INTO mBase tt)
  | [? S] T -> S =u>
    \nu t : T,
      '(FN_INTO m f) <- go S;
      (* [t] should not appear in the result *)
      M.ret (FN_INTO (mTele (fun i : ind => m)) (fun i : ind => f))
  | [? F] (forall (t : T), F t) =u>
      mfail "cannot reify function into type (" T ") whose type depends on a value of (" T ")"
  | [? X F] (forall (x : X), F x) =u>
    \nu x : X,
      '(FN_INTO m f) <- go (F x);
      m <- M.abs_fun x m;
      f <- M.coerce f;
      f <- M.abs_fun (P:=fun x => MTele_ConstT unit (m x)) x f;
      M.ret (FN_INTO (mTele m) f)
  end).

Definition fn_to_constr {T} (fn : string *m fn_into T): (constr_def mBase) :=
  let '(m: name, FN_INTO m i) := fn in
  let i : MTele_ConstT (ArgsOf mBase) m := i in
    {| constr_def_name := name;
     constr_def_tele := m;
     constr_def_indices := i;
    |}.

Program Definition declare_reif (T : Type) (ind_name: string) (fns : mlist (string *m dyn)) :=
  let any_name := reduce RedVmCompute (String.append ind_name "_any") in
  let any_constr : constr_def mBase :=
      {|
        constr_def_name := any_name;
        constr_def_tele := mTele (fun _ : T => mBase);
        constr_def_indices := fun _ => tt
      |}
  in
  constrs <- \nu i,
               constrs <- M.map (fun '(m: name, fn) =>
                      dcase fn as A, _ in
                      fn <- fn_into_of T i A;
                      let constr := reduce (RedWhd RedAll) (fn_to_constr (m: name, fn)) in
                      M.ret constr
                ) fns;
                let constrs := (any_constr :m: constrs) in
                M.abs_fun i constrs
  ;
  M.print_term constrs;;
  M.declare_mind
    (true)                      (* polymorphic *)
    (mBase)                     (* No parameters for now *)
    (NEList.ne_sing {|ind_def_name:= ind_name; ind_def_sig:= {|ind_sig_sort:=Typeₛ; ind_sig_arity := mBase |}|})
    (constrs)
.

Mtac Do (declare_reif nat "nats" [m: (m: "mult", Dyn mult)]).
