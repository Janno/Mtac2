Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Unset Universe Minimization ToSet.

Set Printing Universes.
Set Primitive Projections.
CoInductive Refresh (Out : Prop) : Prop :=
{ refresh_rec : @Refresh Out
; refresh_body :  Out -> Out
}.


Set Universe Polymorphism. Set Polymorphic Inductive Cumulativity.
Monomorphic Definition test_Type@{a b} (t : (Type@{a})) : (Type@{b}) := t.
Monomorphic Constraint test_Type.a < test_Type.b.

Polymorphic Inductive WrapT@{+u} (A : Type@{u}) : Type@{u} := WRAP_T (a : A).
Definition test_WrapT@{a u1 b u2} (t : (WrapT@{u1} Type@{a})) : (WrapT@{u2} Type@{b}) := t.
Fail Monomorphic Constraint test_WrapT.a < test_WrapT.b.

Polymorphic Parameter x@{u1 a} : WrapT@{u1} Type@{a}.
Definition bla@{u1 a u2 b} : (WrapT@{u2} Type@{b}) := x@{u1 a}.

Monomorphic Parameter y@{u1 a} : WrapT@{u1} Type@{a}.
Monomorphic Universes u2 b.
Check y : (WrapT@{u2} Type@{b}).

Unset Cumulativity Weak Constraints.
Polymorphic Inductive WrapP (A : Type) : Prop := WRAP_P (a : A).
Monomorphic Definition test_WrapP@{a x b y} (t : (WrapP@{x} Type@{a})) : (WrapP@{y} Type@{b}) := t.
Fail Monomorphic Constraint test_WrapP.a < test_WrapP.b.
