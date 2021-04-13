From Mtac2 Require Import Mtac2.
Local Close Scope tactic_scope.



Local Close Scope tactic_scope.
Inductive Inhabited (T: Type) : Prop := inhabits (t : T).
Polymorphic Inductive SpecificProp@{u} : Prop := SpecificValueP.
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

Definition result :=
  ltac:(mrun (inhabit (SpecificProp@{x} * SpecificProp@{y} * SpecificProp@{z}))).
Print result.

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

Monomorphic Universes x' y' z'.
Unset Unicoq Debug.
Definition result' :=
  ltac:(mrun (inhabit' (SpecificProp@{x'} * SpecificProp@{y'} * SpecificProp@{z'}))).
Print result'.

Polymorphic Definition value_of@{u+} :=
  mfix1 go (T: Type) : M T :=
    mmatch T in Type as T return M T with
    | [? L R] (L * R)%type => l <- go L; r <- go R; M.ret (l, r)
    | SpecificProp@{u} : Type => M.ret SpecificValueP
  end.

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

  Fail Definition result_fixed :=
    ltac:(mrun (inhabit_fixed (SpecificProp@{x'} * SpecificProp@{y'} * SpecificProp@{z'}))).
End Attempt1.


Polymorphic Definition refresh_init {A} {B: A -> Type}
  (t : Refresh (forall (a : A), M (B a))) : forall a, M (B a) :=
  let t0 := t in
  (mfix2 go (t : Refresh (forall (a : A), M (B a))) (a : A) : M (B a) :=
      t <- M.refresh_prim t0;
      let '{|refresh_rec := _; refresh_body := body|} := t in
      body (go t) a) t.

Module Attempt2.

  Polymorphic Definition value_of_fixed : forall T, M T := refresh_init refresh_value_of.

  Definition inhabit_fixed T := value_of_fixed T >>= fun x => M.ret (inhabits T x).

  #[local] Set Unicoq Trace.
  Definition result_fixed :=
    ltac:(mrun (inhabit_fixed (SpecificProp@{x'} * SpecificProp@{y'} * SpecificProp@{z'}))).
End Attempt2.

Polymorphic Inductive SpecificType@{u+} : Type := SpecificValueT.

Polymorphic Inductive product {T1 T2 : Type} : Type :=
| pairing (t1 : T1) (t2 : T2).
Arguments product : clear implicits.

Module T.


Definition inhabit'@{u+} (T: Type) : M (Inhabited T) :=
let value_of :=
    mfix1 go (T: Type) : M T :=
      mmatch T in Type as T return M T with
      | [? L R] (product L R)%type => l <- go L; r <- go R; M.ret (pairing l r)
      | SpecificType@{u _} => M.ret SpecificValueT
      end
  in
  v <- value_of T;
  M.ret (inhabits T v).

Polymorphic CoFixpoint refresh_value_of@{u+} :=
  {| refresh_rec := refresh_value_of
  ;  refresh_body := fun go (T: Type) =>
        let T := reduce RedHNF T in
        mmatch T in Type as T return M T with
        | [? L R] (product L R)%type =n> l <- go L; r <- go R; M.ret (pairing l r)
        | SpecificType@{u _} =n> M.ret SpecificValueT
     end
  |}.

  Polymorphic Definition value_of_fixed : forall T, M T := refresh_init refresh_value_of.

  Definition inhabit_fixed T := value_of_fixed T >>= fun x => M.ret (inhabits T x).

  (* Set Unicoq Trace. *)
  Definition result_fixed :=
    ltac:(mrun (inhabit_fixed (product SpecificType@{x' _} (product SpecificType@{y' _} SpecificType@{z' _})))).
  Definition result_fixed' :=
    ltac:(mrun (inhabit' (product SpecificType@{x' _} (product SpecificType@{y' _} SpecificType@{z' _})))).

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
      product SpecificType (large_term n)
    end.

  Definition result_fixed_large :=
    ltac:(
      let t := uconstr:(large_term 200) in
      time mrun (inhabit_fixed t)).
  Definition result_large' :=
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
