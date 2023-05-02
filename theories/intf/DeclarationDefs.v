Set Universe Polymorphism.


(** Lifted from coq 8.6.1 Decl_kinds
    TODO: auto generate this file to avoid inconsistencies.
 *)
Inductive definition_object_kind :=
| dok_Definition
| dok_Coercion
| dok_SubClass
| dok_CanonicalStructure
| dok_Example
| dok_Fixpoint
| dok_CoFixpoint
| dok_Scheme
| dok_StructureComponent
| dok_IdentityCoercion
| dok_Instance
| dok_Method.

Inductive implicit_arguments :=
| ia_Explicit
| ia_Implicit
| ia_MaximallyImplicit.