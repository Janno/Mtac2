From Mtac2 Require Import Mtac2 MFix MTeleMatch.
From Mtac2.intf Require Import MTele.
From Mtac2.lib Require Specif NEList List.
Import Specif.
Import ListNotations.

Close Scope tactic_scope.

Record fn_into := FN_INTO
  {
    fn_into_tele : Type -> MTele;
    fn_into_type T : MTele_ConstT unit (fn_into_tele T);
  }.
Arguments fn_into : clear implicits.

Set Universe Polymorphism.

Definition abs_fun_with {X} {T : Type} (Ps : T -> mlist Type) (x : X) (t : T) (fs : mfold_right mprod unit (Ps t)) :
  M m:{f : X -> T & mfold_right mprod unit (Ps (f x)) } :=
  t <- M.abs_fun (P:=fun _ => T) x t;
  fs <- M.coerce fs;
  M.ret (mexistT (fun f => mfold_right mprod unit (Ps (f x))) t fs)
.

Definition swap_binders {X Y T} (Ps : (X -> Y -> T) -> mlist Type) (f : X -> Y -> T) (fs : mfold_right mprod unit (Ps f)) :
  M m:{g : Y -> X -> T & mfold_right mprod unit (Ps (fun x y => g y x))} :=
  \nu x' : X, \nu y' : Y,
    let fx := reduce (RedOneStep [rl: RedBeta]) (f x') in
    let fxy := reduce (RedOneStep [rl: RedBeta]) (fx y') in
    fy <- M.abs_fun x' fxy;
    f <- M.abs_fun y' fy;
    fs <- M.coerce fs;
    M.ret (mexistT _ f fs)
.

(** [abs_below_binder] assumes that the input function [f] is in lambda-normal form. It constructs [fun b : B => G [t[y/x]]]. *)
Definition below_binder {X Y T} (Ps : (X -> T) -> mlist Type) (F : X -> Y -> T) (t : X -> Y) (fs : mfold_right mprod unit (Ps (fun x => F x (t x)))) :
  M m:{g : X -> T & mfold_right mprod unit (Ps g)} :=
  \nu_f for F as x,
    let tx := reduce (RedOneStep [rl: RedBeta]) (t x) in
    let Fx := reduce (RedOneStep [rl: RedBeta]) (F x) in
    let Fxtx := reduce (RedOneStep [rl: RedBeta]) (Fx tx) in
    Ft <- M.abs_fun x Fxtx;
    fs <- M.coerce fs;
    M.ret (mexistT _ Ft fs).

Definition tele_of_res T F :=
m:{ m : Type -> MTele & (MTele_ConstT T (m T) =m= F) *m MTele_ConstT T (m T)}.

Definition tele_of (T : Type) : forall F, F -> M (tele_of_res T F) :=
  (mfix go (F : _) : F -> M (tele_of_res T F) :=
    mtmmatch F as F return F -> M (tele_of_res T F) with
  | T =u> fun f => M.ret (mexistT _ (fun _ => mBase) (m: meq_refl, f))
  | [? S] T -> S =u> fun f =>
    \nu t : T,
      let ft := reduce (RedOneStep [rl: RedBeta]) (f t) in
      '(mexistT _ m (m: e, f)) <- go S ft;
      f <- mmatch f with | [? f] f t =n> M.ret f | _ => M.failwith "impossible" end;
      let e := reduce (RedWhd RedAll) (match e in _ =m= R return _ =m= (T -> R) with | meq_refl => meq_refl end) in
      '(mexistT _ m (m: e; f; tt)) <- below_binder (fun g => [m: (MTele_ConstT T (g T) =m= (T -> S)) : Type | MTele_ConstT T (g T)]) (fun T f => mTele (fun _ : T => f)) m (m: e; f; tt);
      M.ret (mexistT _ m (m: e, f))
  | [? F] (forall (t : T), F t) =u> fun _ =>
      mfail "cannot reify function into type (" T ") whose type depends on a value of (" T ")"
  | [? X F] (forall (x : X), F x) =u> fun f =>
    \nu x : X,
      let Fx := reduce (RedOneStep [rl: RedBeta]) (F x) in
      let fx : Fx := reduce (RedOneStep [rl: RedBeta]) (f x) in
      '(mexistT _ m (m: e, f)) <- go Fx fx;
      '(mexistT _ m (m: e; f; tt)) <- abs_fun_with (fun m => [m: (MTele_ConstT T (m T) =m= Fx) : Type | MTele_ConstT T (m T)]) x m (m: e; f; tt);
      '(mexistT _ m (m: e; f; tt)) <- swap_binders (fun m => [m: (MTele_ConstT T (m x T) =m= Fx) : Type | MTele_ConstT T (m x T)]) m (m: e; f; tt);
      e <- M.coerce (meq_refl (forall x, F x));
      f <- mmatch f with | [? f] f x =n> M.ret f | _ => M.failwith "impossible" end;
      '(mexistT _ m (m: e; f; tt)) <- below_binder (fun g => [m: (MTele_ConstT T (g T) =m= forall x, F x) : Type | MTele_ConstT T (g T)]) (fun T f => mTele f) m (m: e; f; tt);
      M.ret (mexistT _ m (m: e, f))
  end
)
.

Mtac Do (tele_of nat _ (mult) >>= M.print_term).
Mtac Do (tele_of nat _ (Nat.of_uint_acc) >>= M.print_term).

Fixpoint constantT {T} (t : T) {m} : M (MTele_ConstT T m) :=
  match m as m return M (MTele_ConstT T m) with
  | mBase => M.ret t
  | mTele F =>
    \nu_f for F as x,
      let Fx := reduce (RedOneStep [rl: RedBeta]) (F x) in
      c <- constantT (m := Fx) t;
      M.abs_fun (P:=fun x => MTele_ConstT T (F x)) x c
  end.

(* Program Definition fn_to_constrM {T T_reif F} (fn : string *m MTele): *)
(*   M (Constructor.Par.Def (params:=mBase) mBase) := *)
(*   let '(m: name, mexistT _ m (m: e, f)) := fn in *)
(*   let mT_reif := reduce (RedOneStep [rl: RedBeta]) (m T_reif) in *)
(*   i <- @constantT (ArgsOf mBase) tt (m T_reif); *)
(*   M.ret (Constructor.Par.Build_Def mBase mBase name (mT_reif) i). *)

(* Arguments Constructor.Par.Build_Def & _. *)
(* Arguments Mutual.Build_Def _ _ &. *)
(* Arguments Inductive.Build_Sig _ &. *)
(* Arguments Inductive.Build_Def _ &. *)
(* Arguments NEList.ne_sing _ & _. *)
(* Arguments Mutual.OfDef.Build_Val _ _ &. *)
(* Arguments M.declare_mind _ &. *)
(* Arguments Constructor.Par.Vals_Mut_Typs _ _ _ _ &. *)

(* Arguments Match.Build_Val _ _ _ &. *)
(* Arguments Inductive.Inhab _ _ _ _ _ &. *)

(* Program Definition functions_of T (cs : mlist (Constructor.Par.Def (params:=mBase) mBase)) := *)
(*   mfold_right (fun (c : Constructor.Par.Def (params:=mBase) mBase) acc => MTele_ConstT T (Constructor.Par.tele c) *m acc) unit cs. *)

(* Fixpoint constructors_of T T_reif (fns : mlist (string *m dyn)) : M (msigT (functions_of T)) := *)
(*   match fns with *)
(*   | (m: name, fn) :m: fns => *)
(*     dcase fn as A, a in *)
(*     '(mexistT _ (FN_INTO m fn) f) <- fn_into_of T T_reif A a; *)
(*     let fn := reduce (RedWhd RedAll) (fn_to_constr (m: name, FN_INTO m fn)) in *)
(*     '(mexistT _ fns fs) <- constructors_of T T_reif fns; *)
(*     M.ret (mexistT _ (fn:m:fns) (m: f, fs)) *)
(*   | [m:] => M.ret (mexistT _ [m:] tt) *)
(*   end *)
(* . *)

(* Definition declare_reif (T : Type) (ind_name: string) (fns : mlist (string *m dyn)) := *)
(*   let any_name := reduce RedVmCompute (String.append ind_name "_any") in *)
(*   let any_constr : Constructor.Par.Def (params:=mBase) mBase := *)
(*       {| *)
(*         Constructor.Par.name := any_name; *)
(*         Constructor.Par.tele := mTele (fun _ : T => mBase); *)
(*         Constructor.Par.indices := fun _ => tt *)
(*       |} *)
(*   in *)

(*   constrs <- \nu T_reif, *)
(*                 '(mexistT _ constrs fns) <- constructors_of T T_reif fns; *)
(*                 constrs <- M.abs_fun T_reif constrs; *)
(*                 M.ret (mexistT ()) *)
(*   ; *)
(*   let constrs T_reif := any_constr :m: constrs T_reif in *)
(*   M.print_term constrs;; *)
(*   (* '({| Mutual.OfDef.inds := T_reif; Mutual.OfDef.constrs := constrs |}) <- M.declare_mind *) *)
(*   let mind_def := *)
(*   (Mutual.Build_Def *)
(*     (true)                      (* polymorphic *) *)
(*     (mBase)                     (* No parameters for now *) *)
(*     (NEList.ne_sing *)
(*        {| Inductive.name:= ind_name; *)
(*           Inductive.sig:= *)
(*             {| *)
(*               Inductive.sort:=Typeₛ; *)
(*               Inductive.arity := mBase *)
(*             |} *)
(*        |}) *)
(*     (constrs) *)
(*   ) in *)
(*   '(Mutual.OfDef.Build_Val _ T_reif constrs as mind) <- M.declare_mind mind_def; *)
(*   M.print_term T_reif;; *)
(*   M.print_term constrs;; *)

(*   (* build the reflection function from T_reif -> T *) *)

(*   reif <- ( *)
(*     \nu t_reif : T_reif, *)
(*     body <- M.build_match ( *)
(*      Match.Build_Val *)
(*        (Mutual.Build_Nth (Mutual.OfDef.val mind) 0 0 0) *)
(*        tt *)
(*        tt *)
(*        t_reif *)
(*        Typeₛ *)
(*        (fun _ : T_reif => T) *)
(*        (m: fun t => t,_) *)
(*     ); *)
(*     M.ret tt *)
(*   ); *)

(*   M.ret tt *)
(* . *)

(* Mtac Do (declare_reif nat "nats" [m: (m: "mult", Dyn mult)]). *)
