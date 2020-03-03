From Mtac2 Require Import Mtac2 MFix.
From Mtac2.intf Require Import Case MTele Sorts.
From Mtac2.lib Require Import Logic Specif.

Local Close Scope tactic.
Set Universe Polymorphism.


Definition equate_sig' {A} {v : A} (t : M { v' : A & v' = v }) := v.
Fail Definition broken_backtrace :=
      fix go (t : unit) {struct t} : M {t' & t' = t} :=
          \nu x,
            let Fx := _ in
            t <- M.abs_fun x Fx; _
.

(*
Cannot infer the type of x in
environment:
go : forall t : unit, M {t' : unit & t' = t}
t : unit
Raised at file "hashtbl.ml", line 506, characters 17-32
Called from file "kernel/cClosure.ml", line 522, characters 4-25
 *)

Fail Definition working_backtrace :=
      fix go (t : unit) {struct t} : M {t' & t' = t} :=
          \nu x,
            let Fx := _ in
            t <- M.abs_fun x _; _
.
(*
Cannot infer the type of x in
environment:
go : forall t : unit, M {t' : unit & t' = t}
t : unit
Raised at file "map.ml", line 135, characters 10-25
Called from file "pretyping/globEnv.ml", line 59, characters 6-32
 *)
