open Environ
open Evd
open EConstr


type backtrace
val pr_backtrace : backtrace -> Pp.t


type elem_stack = (Evd.evar_map * Environ.env * CClosure.fconstr * CClosure.stack * backtrace)

type elem = (evar_map * constr)

type data_stack =
  | Val of elem_stack
  | Err of elem_stack

type data =
  | Val of elem
  | Err of elem * backtrace

val make_evar : evar_map -> env -> constr -> evar_map * constr (* used in metaCoqInterp *)

val run : (env * evar_map) -> constr -> etypes -> data

module Goal : sig
  val mkTheGoal : ?base:bool -> types -> constr -> Evd.evar_map -> Environ.env -> (Evd.evar_map * constr)
  val evar_of_goal : Evd.evar_map -> Environ.env -> constr -> Evar.t option
end

(** DEBUG **)

type ctxt = {
  env: Environ.env;
  renv: CClosure.fconstr;
  sigma: Evd.evar_map;
  nus: int;
  stack: CClosure.stack;
  backtrace: backtrace;
}

type vm = Code of CClosure.fconstr
        | Ret of CClosure.fconstr
        | Fail of CClosure.fconstr
        | Bind of (CClosure.fconstr * backtrace)
        | Try of (Evd.evar_map * CClosure.stack * backtrace * CClosure.fconstr)
        | Nu of (Names.Id.t * Environ.env * CClosure.fconstr * backtrace)
        | Rem of (Environ.env * CClosure.fconstr * bool)

(* val run_fix : ctxt -> vm list -> CClosure.fconstr -> CClosure.fconstr array -> CClosure.fconstr -> CClosure.fconstr -> CClosure.fconstr array *)

val run' : ctxt -> vm list -> data_stack

val multi_subst : evar_map -> (int * constr) list -> constr -> constr

module Hypotheses : sig
  val from_coq_list : (Environ.env * Evd.evar_map) ->
    constr -> (constr * constr option * constr) list
end
