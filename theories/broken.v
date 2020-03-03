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

Fail Definition working_backtrace :=
      fix go (t : unit) {struct t} : M {t' & t' = t} :=
          \nu x,
            let Fx := _ in
            t <- M.abs_fun x _; _
        .
