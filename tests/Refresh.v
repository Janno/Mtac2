From Mtac2 Require Import Mtac2.
Local Close Scope tactic_scope.



Local Close Scope tactic_scope.
Inductive Inhabited (T: Type) : Prop := inhabits (t : T).
Polymorphic Inductive SpecificProp@{u} : Prop := SpecificValueP.

Definition inhabitP (T: Prop) : M (Inhabited T) :=
let value_of :=
    mfix1 go (T: Prop) : M T :=
      mmatch T in Prop as T return M T with
      | [? L R: Prop] (L * R)%type => l <- go L; r <- go R; M.ret (l, r)
      | SpecificProp => M.ret SpecificValueP
      end
in
  v <- value_of T;
  M.ret (inhabits T v).



Definition inhabit (T: Type) : M (Inhabited T) :=
let value_of :=
    mfix1 go (T: Type) : M T :=
      mmatch T in Type as T return M T with
      | [? L R] (L * R)%type => l <- go L; r <- go R; M.ret (l, r)
      | SpecificProp : Type => M.ret SpecificValueP
      end
in
  v <- value_of T;
  M.ret (inhabits T v).

Monomorphic Universes x y z.

Mtac Do inhabit (SpecificProp@{x} * SpecificProp@{y} * SpecificProp@{z}) >>= M.print_term.
Set Printing Universes.
Mtac Do inhabit (SpecificProp@{x} * SpecificProp@{y} * SpecificProp@{z}) >>= M.print_term.

Monomorphic Universes a b c.
Monomorphic Constraint a < b.
Set Unicoq Debug.
Fail Mtac Do inhabit (SpecificProp@{a} * SpecificProp@{b} * SpecificProp@{c}) >>= M.print_term.


Definition result@{x y z} :=
  ltac:(mrun (inhabit (SpecificProp@{x} * SpecificProp@{y} * SpecificProp@{z}))).
Print result.
Fail Monomorphic Constraint result.x < result.y.



Definition resultP@{x y z} :=
  ltac:(mrun (inhabitP (SpecificProp@{x} * SpecificProp@{y} * SpecificProp@{z}))).
Print resultP.
Fail Monomorphic Constraint resultP.x < resultP.y.

Definition inhabit'@{u+} (T: Type) : M (Inhabited T) :=
let value_of :=
    mfix1 go (T: Type) : M T :=
      mmatch T in Type as T return M T with
      | [? L R] (L * R)%type => l <- go L; r <- go R; M.ret (l, r)
      | SpecificProp@{u} : Type => M.ret SpecificValueP
      end
in
  v <- value_of T;
  M.ret (inhabits T v).

Unset Unicoq Debug.
Definition result'@{x y z} :=
  ltac:(mrun (inhabit' (SpecificProp@{x} * SpecificProp@{y} * SpecificProp@{z}))).
Print result'.

Fail Monomorphic Constraint result'.x < result'.y.

Polymorphic Definition value_of@{u+} :=
  mfix1 go (T: Type) : M T :=
    mmatch T in Type as T return M T with
    | [? L R] (L * R)%type => l <- go L; r <- go R; M.ret (l, r)
    | SpecificProp@{u} : Type => M.ret SpecificValueP
  end.

Polymorphic Definition value_of_unfolded :=
  Eval cbv beta iota match delta
          [value_of matcher_match_invert internal_meq_rew matcher_match M_Matcher M.mmatch'' M.mmatch']
  in value_of.

CoInductive Refresh (Out : Prop) : Prop :=
{ refresh_rec : @Refresh Out
; refresh_body :  Out -> Out
}.

Polymorphic CoFixpoint refresh_value_of@{u+} :=
  {| refresh_rec := refresh_value_of
  ;  refresh_body := fun go (T: Type) =>
        mmatch T in Type as T return M T with
        | [? L R] (L * R)%type => l <- go L; r <- go R; M.ret (l, r)
        | SpecificProp@{u} : Type => M.ret SpecificValueP
     end
  |}.

Module Attempt1.

  Polymorphic Definition refresh {A} {B: A -> Type} :
    Refresh (forall (a : A), M (B a)) -> forall a, M (B a) :=
    mfix2 go (t : Refresh (forall (a : A), M (B a))) (a : A) : M (B a) :=
      let '{|refresh_rec := rec; refresh_body := body|} := t in
      rec <- M.refresh_prim t;
      body (go rec) a.

  Polymorphic Definition value_of_fixed : forall T, M T := refresh refresh_value_of.

  Polymorphic Definition inhabit_fixed T := value_of_fixed T >>= fun x => M.ret (inhabits T x).

  Definition result_fixed@{x y z} :=
    ltac:(mrun (inhabit_fixed (SpecificProp@{x} * SpecificProp@{y} * SpecificProp@{z}))).
  (* Fails because we refresh only after tainting the initial universe set *)
  Fail Monomorphic Constraint result_fixed.x < result_fixed.y.
End Attempt1.


Polymorphic Definition refresh_init
    {A} {B: A -> Type} (t : Refresh (forall (a : A), M (B a))) : forall a, M (B a) :=
  mfix1 go (a : A) : M (B a) :=
    fresh_instance <- M.refresh_prim t;
    let '{|refresh_rec := _; refresh_body := fresh_body|} := fresh_instance in
    fresh_body go a.

Module Attempt2.

  Polymorphic Definition value_of_fixed : forall T, M T := refresh_init refresh_value_of.

  Definition inhabit_fixed T := value_of_fixed T >>= fun x => M.ret (inhabits T x).

  #[local] Set Unicoq Trace.
  Definition result_fixed@{x y z} :=
    ltac:(mrun (inhabit_fixed (SpecificProp@{x} * SpecificProp@{y} * SpecificProp@{z}))).

  Fail Fail Monomorphic Constraint result_fixed.x < result_fixed.y.
End Attempt2.


#[local] Set Polymorphic Inductive Cumulativity.
Polymorphic Inductive SpecificType@{u} : Type@{u} := SpecificValueT.

Polymorphic Inductive product {T1 T2 : Type} : Type :=
| pairing (t1 : T1) (t2 : T2)
where "T1 * T2" := (@product T1 T2) : type_scope.
Notation   "( x , y , .. , z )" := (@pairing _ _ .. (@pairing _ _ x y) .. z) : core_scope.
Arguments product : clear implicits.

Module T.


Polymorphic Definition refresh1
    {A} {B: A -> Type} (t : Refresh (forall (a : A), M (B a))) : forall a, M (B a) :=
  mfix1 go (a : A) : M (B a) :=
    fresh_instance <- M.refresh_prim t;
    let '{|refresh_rec := _; refresh_body := fresh_body|} := fresh_instance in
    fresh_body go a.

Definition inhabit'@{u+} (T: Type) : M (Inhabited T) :=
let value_of :=
    mfix1 go (T: Type) : M T :=
      mmatch T in Type as T return M T with
      | [? L R] (L * R)%type => l <- go L; r <- go R; M.ret (l, r)
      | SpecificType@{u} => M.ret SpecificValueT
      end
  in
  v <- value_of T;
  M.ret (inhabits T v).

Polymorphic CoFixpoint refresh_value_of@{u+} :=
  {| refresh_rec := refresh_value_of
  ;  refresh_body := fun go (T: Type) =>
        'tt <- M.ret tt;
        let T := reduce (RedWhd RedAll) T in
        mmatch T in Type as T return M T with
        | [? L R] (L * R)%type =n> l <- go L; r <- go R; M.ret (l, r)
        | SpecificType@{u} =n> M.ret SpecificValueT@{u}
     end
  |}.

  Polymorphic Definition value_of_fixed : forall T, M T := refresh_init refresh_value_of.

  Definition inhabit_fixed T := value_of_fixed T >>= fun x => M.ret (inhabits T x).

  (* Set Unicoq Trace. *)
  Definition result_fixed@{x y z+} :=
    ltac:(mrun (inhabit_fixed (SpecificType@{x} * SpecificType@{y} * SpecificType@{z}))).
  Definition result'@{x y z+} :=
    ltac:(mrun (inhabit' (SpecificType@{x} * SpecificType@{y} * SpecificType@{z}))).

  (* Ltac build_term n := *)
  (*   match n with *)
  (*   | O => uconstr:(SpecificType) *)
  (*   | S ?n => let r := build_term n in *)
  (*             uconstr:(product SpecificType r) *)
  (*   end. *)

  (* Definition large_term := ltac:(let t := build_term 60 in exact t). *)

  Fixpoint large_term n :=
    match n with
    | O => SpecificType
    | S n =>
      (large_term n) * SpecificType
    end%type.

  (* Time Definition result_fixed_large := *)
  Goal Inhabited (large_term 200).
    ltac:(
      let t := uconstr:(large_term 200) in
      time mrun (inhabit_fixed t)).
    Show Universes.
  Time Qed.
  Time Definition result_large' :=
    ltac:(
      let t := uconstr:(large_term 200) in
      time mrun (inhabit' t)).

  Ltac inhabit T :=
    let T := eval hnf in T in
    lazymatch T with
    | product ?L ?R =>
      let l := inhabit L in
      let r := inhabit R in
      uconstr:(pairing l r)
    | SpecificType => uconstr:(SpecificValueT)
    end.

  Definition result_ltac :=
    ltac:(
      let t := uconstr:(large_term 200) in
      time (let r := inhabit t in exact r)).

  From Ltac2 Require Import Ltac2.

  Ltac2 rec inhabit t :=
    let t := Std.eval_hnf t in
    lazy_match! t with
    | product ?tl ?tr =>
      let l := inhabit tl in
      let r := inhabit tr in
      Constr.Unsafe.make (Constr.Unsafe.App constr:(@pairing) (Array.of_list [tl; tr; l; r]))
    | SpecificType => constr:(SpecificValueT)
    end.

  Definition result_ltac2 :=
    ltac2:(
      let t := constr:(large_term 200) in
      time (let r := inhabit t in exact $r)).

  Ltac2 inhabit' t :=
    let prepairing := constr:(@pairing) in
    let prevalue := constr:(SpecificValueT) in
    let rec inhabit' t :=
    let t := Std.eval_hnf t in
    lazy_match! t with
    | product ?tl ?tr =>
      let l := inhabit' tl in
      let r := inhabit' tr in
      Constr.Unsafe.make (Constr.Unsafe.App prepairing (Array.of_list [tl; tr; l; r]))
    | SpecificType => prevalue
        end in
        inhabit t.

  Definition result_ltac2' :=
    ltac2:(
      let t := constr:(large_term 200) in
      time (let r := inhabit' t in refine r)).

End T.

Module EQ.

  #[local] Set Polymorphic Inductive Cumulativity.
  Polymorphic Inductive TestT@{u} : Prop := TestTV (T:Type@{u} -> Type@{u}).

  Set Printing All.
Polymorphic CoFixpoint refresh_value_of@{u+} : Refresh (forall T:Prop, M.t@{Set} _) :=
  {| refresh_rec := refresh_value_of
  ;  refresh_body := fun go (T: Prop) =>
        'tt <- M.ret tt;
        let T := reduce RedHNF T in
        mmatch T in Prop as T return M T with
        | [? L R : Prop] (L /\ R)%type => l <- go L; r <- go R; M.ret (conj l r)
        | TestT@{u} => M.ret (TestTV@{u} (fun x => x))
     end
  |}.

  Polymorphic Definition value_of_fixed : forall T:Prop, M T := refresh_init refresh_value_of.

  Polymorphic Definition inhabit_fixed T := value_of_fixed T >>= fun x => M.ret (inhabits T x).


  Set Printing All.
  Definition result_fixed@{x y z} :=
    ltac:(mrun (inhabit_fixed (TestT@{x} /\ TestT@{y} /\ TestT@{z}))).
  Fail Fail Monomorphic Constraint x < y.
End EQ.

Module Lower.

  Import Mtac2.lib.Specif.

  Fixpoint prod (ts : mlist Type) : Type :=
    match ts return Type with
    | mnil => unit
    | t :m: ts => t * prod ts
    end%type.

  Fixpoint prod_map {ts : mlist Type} {F} (f : forall T, T -> F T) : prod ts -> prod (mmap F ts) :=
    match ts as ts return prod ts -> prod (mmap F ts) with
    | mnil => fun u => u
    | t :m: ts => fun '(v, vs) => (f t v, prod_map f vs)
    end.

  (* Definition lub@{i o l+} : forall ts : mlist Type@{i}, M m:{ t : Type@{o} & prod (mmap (fun ty => t -> ty) ts) } := *)
  (*     (mfix1 go (ts : mlist Type@{i}) : M m:{ t : Type@{o} & prod (mmap (fun ty => t -> ty) ts) } := *)
  (*        match ts as ts return M m:{ t : Type@{o} & prod (mmap (fun ty => t -> ty) ts) } with *)
  (*        | mnil => M.ret (mexistT _ Set tt) *)
  (*        | t :m: ts => *)
  (*          '(mexistT _ lub funs) <- go ts; *)
  (*          mtry *)
  (*            M.cumul_or_fail UniCoq Type@{o} Type@{i};; *)
  (*            M.ret (mexistT (fun t : Type@{o} => prod (mmap (fun ty => t -> ty) (_ :m: ts))) lub (fun v : t => _, funs)) *)
  (*          with | [?e] e => *)
  (*            M.cumul_or_fail UniCoq Type@{i} Type@{o};; *)
  (*            M.ret (mexistT _ t (fun v : t => _, _)) *)
  (*          end *)
  (*        end *)
  (*     ) *)
  (*   . *)

End Lower.

Module Soundness.
  #[local] Set Polymorphic Inductive Cumulativity.

  Polymorphic Inductive tree@{i j} : Type@{j} :=
  | Node : tree -> tree -> tree
  | Leaf (T: Type@{i}) : tree.

  Polymorphic Definition mk_tree@{i j +} : forall (n:nat), M tree :=
    mfix1 go (n : nat) : M tree :=
      match n with
      | 0 => M.ret@{j} (Leaf Type@{i})
      | S n =>
        l <- go n;
        r <- go n;
        M.ret (Node l r)
      end.

  Monomorphic Universes k1 k2 k3 k4.
  Lemma mk_tree_test : tree.
    Show Universes.
    mrun (mk_tree@{k1 k2 k3 k4} 1).
    Show Universes.
    Show Proof.
  Qed.


  (* The code above does _not_ show the unsoundness that results from the following scenario:
     - copy initial universe instance UI_0, call the result UI_1
     - execute tactic which puts constraints C_1 on UI_1
     - recurse in a position of type [M T] where [T] is constrained by UI_1 (i.e. it cannot be larger than a certain universe)
     - copy initial universe instance UI_0, call the result UI_2
     - recurse at UI_2, ignoring the constraints on the current context.
       refresh@{R} (ref, body)@{U_0}
       (ref_f, body_f)@{U_1} <- refresh_prim  (ref, body)@{U} ->
       -> body@{U_1} (refresh@{R} (ref, body)@{U_0})
       -> ....
       -> refresh@{R} (ref, body)@{U_0}
   *)

  #[local] Unset Polymorphic Inductive Cumulativity.


  Polymorphic Definition refresh2
      {A} {B: A -> Type} {C : forall a, B a -> Type} (t : Refresh (forall (a : A) b, M (C a b))) : forall a b, M (C a b) :=
    mfix2 go (a : A) b : M (C a b) :=
      fresh_instance <- M.refresh_prim t;
      let '{|refresh_rec := _; refresh_body := fresh_body|} := fresh_instance in
      fresh_body go a b.

  Polymorphic Definition refresh3
      {A} {B: A -> Type} {C : forall a, B a -> Type} {D : forall a b (c : C a b), Type} (t : Refresh (forall a b c, M (D a b c))) : forall a b c, M (D a b c) :=
    mfix3 go (a : A) b c : M (D a b c) :=
      fresh_instance <- M.refresh_prim t;
      let '{|refresh_rec := _; refresh_body := fresh_body|} := fresh_instance in
      fresh_body go a b c.

  Arguments ptele _ _ _ &.
  Arguments pany _ _ _ &.
  Arguments mcons _ &.
  Arguments mnil _ &.
  Arguments branch_pattern _ _ _ &.



  Polymorphic CoFixpoint failing_refresh@{u1 u2 t1 t2+} : Refresh (forall (n : nat) (T1: Type@{t1}) (T2 : Type@{t2}), M.t@{u2} Type@{u1}) :=
    {| refresh_rec := failing_refresh
     ; refresh_body go (n : nat) (T1: Type@{t1}) (T2: Type@{t2}) :=
      match n with
      | 0 =>
        mmatch T1 return M.t@{u2} Type@{u1} with
        | T1 => M.print "T1";; r <- go 1 T1 T2; M.ret (T1 * r)%type
        end
      | _ =>
        mmatch T2 return M.t@{u2} Type@{u1} with
        | T2 => M.print "T1";; M.ret T2
        end
    end
    |}.

  Set Printing All.

  Eval cbv beta match iota fix delta [refresh3] in refresh3 failing_refresh.

  Polymorphic Definition failing := refresh3 failing_refresh.

  Monomorphic Universes x y.
  Monomorphic Constraint x < y.

  Definition failing_test : Type.
    Set Unicoq Debug.
    mrun (failing 0 Type@{x} Type@{y}).
    Show Proof.
    Show Universes.
    Show Proof.
  Qed.



End Soundness.