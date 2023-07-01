open MtacNames
type arg = CClosure.fconstr

type arg_any = arg
type arg_type = arg
type arg_fun = arg
type arg_string = arg
type arg_N = arg
type arg_bool = arg
type arg_mlist = arg
type arg_case = arg

type arg_fix1_ty = arg_type
type arg_fix1_val = arg_any

type arg_fix2_ty = arg_type * arg_type
type arg_fix2_val = arg_any * arg_any

type arg_fix3_ty = arg_type * arg_type * arg_type
type arg_fix3_val = arg_any * arg_any * arg_any

type arg_fix4_ty = arg_type * arg_type * arg_type * arg_type
type arg_fix4_val = arg_any * arg_any * arg_any * arg_any

type arg_fix5_ty = arg_type * arg_type * arg_type * arg_type * arg_type
type arg_fix5_val = arg_any * arg_any * arg_any * arg_any * arg_any

type 'a mconstr_head =
  | Mret : (arg_type * arg_any) mconstr_head
  | Mbind : (arg_type * arg_type * arg_any * arg_fun) mconstr_head
  | Mmtry' : (arg_type * arg_any * arg_fun) mconstr_head
  | Mraise' : (arg_type * arg_any) mconstr_head
  | Mfix1 : (arg_fix1_ty * arg_type * arg_fun * arg_fix1_val) mconstr_head
  | Mfix2 : (arg_fix2_ty * arg_type * arg_fun * arg_fix2_val) mconstr_head
  | Mfix3 : (arg_fix3_ty * arg_type * arg_fun * arg_fix3_val) mconstr_head
  | Mfix4 : (arg_fix4_ty * arg_type * arg_fun * arg_fix4_val) mconstr_head
  | Mfix5 : (arg_fix5_ty * arg_type * arg_fun * arg_fix5_val) mconstr_head
  | Mis_var : (arg_type * arg_any) mconstr_head
  | Mnu : (arg_type * arg_type * arg_string * arg_any * arg_fun) mconstr_head
  | Mnu_let : (arg_type * arg_type * arg_type * arg_string * arg_any * arg_fun) mconstr_head
  | Mabs_fun : (arg_type * arg_fun * arg_any * arg_any) mconstr_head
  | Mabs_let : (arg_type * arg_fun * arg_any * arg_any * arg_any) mconstr_head
  | Mabs_prod_prop : (arg_type * arg_any * arg_type) mconstr_head
  | Mabs_prod_type : (arg_type * arg_any * arg_type) mconstr_head
  | Mabs_fix : (arg_type * arg_any * arg_any * arg_N) mconstr_head
  | Mget_binder_name : (arg_type * arg_any) mconstr_head
  | Mremove : (arg_type * arg_type * arg_any * arg_any) mconstr_head
  | Mgen_evar : (arg_type * arg_any) mconstr_head
  | Mis_evar : (arg_type * arg_any) mconstr_head
  | Mhash : (arg_type * arg_any * arg_N) mconstr_head
  | Msolve_typeclasses
  | Mprint : (arg_string) mconstr_head
  | Mpretty_print : (arg_type * arg_any) mconstr_head
  | Mhyps
  | Mdestcase : (arg_type * arg_any) mconstr_head
  | Mconstrs : (arg_type * arg_any) mconstr_head
  | Mmakecase : (arg_case) mconstr_head
  | Munify : (arg_type * arg_type * arg_any * arg_any * arg_any * arg_fun * arg_fun) mconstr_head
  | Munify_cumul : (arg_type * arg_type * arg_type * arg_any * arg_fun * arg_fun) mconstr_head
  | Mget_reference : (arg_string) mconstr_head
  | Mget_var : (arg_string) mconstr_head
  | Mcall_ltac : (arg_any * arg_any * arg_string * arg_mlist) mconstr_head
  | Mlist_ltac
  | Mread_line
  | Mdecompose : (arg_type * arg_any) mconstr_head
  | Msolve_typeclass : (arg_type) mconstr_head
  | Mdeclare : (arg_any * arg_string * arg_bool * arg_type * arg_any) mconstr_head
  | Mdeclare_implicits : (arg_type * arg_any * arg_mlist) mconstr_head
  | Mos_cmd : (arg_string) mconstr_head
  | Mget_debug_exceptions
  | Mset_debug_exceptions : (arg_bool) mconstr_head
  | Mget_trace
  | Mset_trace : (arg_bool) mconstr_head
  | Mdecompose_app' : (arg_type * arg_fun * arg_any * arg_any * arg_any * arg_any * arg_any * arg_any) mconstr_head
  | Mdecompose_forallT : (arg_fun * arg_type * arg_any * arg_any) mconstr_head
  | Mdecompose_forallP : (arg_fun * arg_type * arg_any * arg_any) mconstr_head
  | Mdecompose_app'' : (arg_fun * arg_fun * arg_any * arg_any) mconstr_head
  | Mnew_timer : (arg_type * arg_any) mconstr_head
  | Mstart_timer : (arg_type * arg_any * arg_bool) mconstr_head
  | Mstop_timer : (arg_type * arg_any) mconstr_head
  | Mreset_timer : (arg_type * arg_any) mconstr_head
  | Mprint_timer : (arg_type * arg_any) mconstr_head
  | Mkind_of_term : (arg_type * arg_any) mconstr_head
  | Mreplace : (arg_type * arg_type * arg_type * arg_any * arg_any * arg_any) mconstr_head
  | Mdeclare_mind : (arg_any * arg_any * arg_any) mconstr_head
  | Mexisting_instance : (arg_any * arg_any * arg_bool) mconstr_head
  | Minstantiate_evar : (arg_type * arg_type * arg_any * arg_any * arg_fun * arg_fun) mconstr_head
and mhead = | MHead : 'a mconstr_head -> mhead
and mconstr = | MConstr : 'a mconstr_head * 'a -> mconstr

let num_args_of_mconstr (type a) (mh : a mconstr_head) =
  match mh with
  | Mret -> 2
  | Mbind -> 4
  | Mmtry' -> 3
  | Mraise' -> 2
  | Mfix1 -> 2 + 2*1
  | Mfix2 -> 2 + 2*2
  | Mfix3 -> 2 + 2*3
  | Mfix4 -> 2 + 2*4
  | Mfix5 -> 2 + 2*5
  | Mis_var -> 2
  | Mnu -> 5
  | Mnu_let -> 6
  | Mabs_fun -> 4
  | Mabs_let -> 5
  | Mabs_prod_prop -> 3
  | Mabs_prod_type -> 3
  | Mabs_fix -> 4
  | Mget_binder_name -> 2
  | Mremove -> 4
  | Mgen_evar -> 2
  | Mis_evar -> 2
  | Mhash -> 3
  | Msolve_typeclasses -> 0
  | Mprint -> 1
  | Mpretty_print -> 2
  | Mhyps -> 0
  | Mdestcase -> 2
  | Mconstrs -> 2
  | Mmakecase -> 1
  | Munify -> 7
  | Munify_cumul -> 6
  | Mget_reference -> 1
  | Mget_var -> 1
  | Mcall_ltac -> 4
  | Mlist_ltac -> 0
  | Mread_line -> 0
  | Mdecompose -> 2
  | Msolve_typeclass -> 1
  | Mdeclare -> 5
  | Mdeclare_implicits -> 3
  | Mos_cmd -> 1
  | Mget_debug_exceptions -> 0
  | Mset_debug_exceptions -> 1
  | Mget_trace -> 0
  | Mset_trace -> 1
  | Mdecompose_app' -> 8
  | Mdecompose_forallT -> 4
  | Mdecompose_forallP -> 4
  | Mdecompose_app'' -> 4
  | Mnew_timer -> 2
  | Mstart_timer -> 3
  | Mstop_timer -> 2
  | Mreset_timer -> 2
  | Mprint_timer -> 2
  | Mkind_of_term -> 2
  | Mreplace -> 6
  | Mdeclare_mind -> 3
  | Mexisting_instance -> 3
  | Minstantiate_evar -> 6





module ConstructorMap = struct
  let map : mhead Names.GlobRef.Map.t lazy_t =
    lazy (

      let constant_of_string s = constant_of_string ("M.M." ^ s) in
      let name_ret = constant_of_string "ret" in
      let name_bind = constant_of_string "bind" in
      let name_try' = constant_of_string "mtry'" in
      let name_raise = constant_of_string "raise'" in
      let name_fix1 = constant_of_string "fix1" in
      let name_fix2 = constant_of_string "fix2" in
      let name_fix3 = constant_of_string "fix3" in
      let name_fix4 = constant_of_string "fix4" in
      let name_fix5 = constant_of_string "fix5" in
      let name_is_var = constant_of_string "is_var" in
      let name_nu = constant_of_string "nu" in
      let name_nu_let = constant_of_string "nu_let" in
      let name_abs_fun = constant_of_string "abs_fun" in
      let name_abs_let = constant_of_string "abs_let" in
      let name_abs_prod_prop = constant_of_string "abs_prod_prop" in
      let name_abs_prod_type = constant_of_string "abs_prod_type" in
      let name_abs_fix = constant_of_string "abs_fix" in
      let name_get_binder_name = constant_of_string "get_binder_name" in
      let name_remove = constant_of_string "remove" in
      let name_gen_evar = constant_of_string "gen_evar" in
      let name_is_evar = constant_of_string "is_evar" in
      let name_hash = constant_of_string "hash" in
      let name_solve_typeclasses = constant_of_string "solve_typeclasses" in
      let name_print = constant_of_string "print" in
      let name_pretty_print = constant_of_string "pretty_print" in
      let name_hyps = constant_of_string "hyps" in
      let name_destcase = constant_of_string "destcase" in
      let name_constrs = constant_of_string "constrs" in
      let name_makecase = constant_of_string "makecase" in
      let name_unify = constant_of_string "unify_cnt" in
      let name_unify_cumul = constant_of_string "unify_cumul_cnt" in
      let name_get_reference = constant_of_string "get_reference" in
      let name_get_var = constant_of_string "get_var" in
      let name_call_ltac = constant_of_string "call_ltac" in
      let name_list_ltac = constant_of_string "list_ltac" in
      let name_read_line = constant_of_string "read_line" in
      let name_decompose = constant_of_string "decompose" in
      let name_solve_typeclass = constant_of_string "solve_typeclass" in
      let name_declare = constant_of_string "declare" in
      let name_declare_implicits = constant_of_string "declare_implicits" in
      let name_os_cmd = constant_of_string "os_cmd" in
      let name_get_debug_ex = constant_of_string "get_debug_exceptions" in
      let name_set_debug_ex = constant_of_string "set_debug_exceptions" in
      let name_get_trace = constant_of_string "get_trace" in
      let name_set_trace = constant_of_string "set_trace" in
      let name_decompose_app = constant_of_string "is_head" in
      let name_decompose_forallT = constant_of_string "decompose_forallT" in
      let name_decompose_forallP = constant_of_string "decompose_forallP" in
      let name_decompose_app'' = constant_of_string "decompose_app''" in
      let name_new_timer = constant_of_string "new_timer" in
      let name_start_timer = constant_of_string "start_timer" in
      let name_stop_timer = constant_of_string "stop_timer" in
      let name_reset_timer = constant_of_string "reset_timer" in
      let name_print_timer = constant_of_string "print_timer" in
      let name_kind_of_term = constant_of_string "kind_of_term" in
      let name_replace = constant_of_string "replace" in
      let name_declare_mind = constant_of_string "declare_mind" in
      let name_existing_instance = constant_of_string "existing_instance" in
      let name_instantiate_evar = constant_of_string "instantiate_evar" in



      let bindings =
        [
          (name_ret, MHead Mret);
          (name_bind, MHead Mbind);
          (name_try', MHead Mmtry');
          (name_raise, MHead Mraise');
          (name_fix1, MHead Mfix1);
          (name_fix2, MHead Mfix2);
          (name_fix3, MHead Mfix3);
          (name_fix4, MHead Mfix4);
          (name_fix5, MHead Mfix5);
          (name_is_var, MHead Mis_var);
          (name_nu, MHead Mnu);
          (name_nu_let, MHead Mnu_let);
          (name_abs_fun, MHead Mabs_fun);
          (name_abs_let, MHead Mabs_let);
          (name_abs_prod_type, MHead Mabs_prod_type);
          (name_abs_prod_prop, MHead Mabs_prod_prop);
          (name_abs_fix, MHead Mabs_fix);
          (name_get_binder_name, MHead Mget_binder_name);
          (name_remove, MHead Mremove);
          (name_gen_evar, MHead Mgen_evar);
          (name_is_evar, MHead Mis_evar);
          (name_hash, MHead Mhash);
          (name_solve_typeclasses, MHead Msolve_typeclasses);
          (name_print, MHead Mprint);
          (name_pretty_print, MHead Mpretty_print);
          (name_hyps, MHead Mhyps);
          (name_destcase, MHead Mdestcase);
          (name_constrs, MHead Mconstrs);
          (name_makecase, MHead Mmakecase);
          (name_unify, MHead Munify);
          (name_unify_cumul, MHead Munify_cumul);
          (name_get_reference, MHead Mget_reference);
          (name_get_var, MHead Mget_var);
          (name_call_ltac, MHead Mcall_ltac);
          (name_list_ltac, MHead Mlist_ltac);
          (name_read_line, MHead Mread_line);
          (name_decompose, MHead Mdecompose);
          (name_solve_typeclass, MHead Msolve_typeclass);
          (name_declare, MHead Mdeclare);
          (name_declare_implicits, MHead Mdeclare_implicits);
          (name_os_cmd, MHead Mos_cmd);
          (name_get_debug_ex, MHead Mget_debug_exceptions);
          (name_set_debug_ex, MHead Mset_debug_exceptions);
          (name_get_trace, MHead Mget_trace);
          (name_set_trace, MHead Mset_trace);
          (name_decompose_app, MHead Mdecompose_app');
          (name_decompose_forallT, MHead Mdecompose_forallT);
          (name_decompose_forallP, MHead Mdecompose_forallP);
          (name_decompose_app'', MHead Mdecompose_app'');
          (name_new_timer, MHead Mnew_timer);
          (name_start_timer, MHead Mstart_timer);
          (name_stop_timer, MHead Mstop_timer);
          (name_reset_timer, MHead Mreset_timer);
          (name_print_timer, MHead Mprint_timer);
          (name_kind_of_term, MHead Mkind_of_term);
          (name_replace, MHead Mreplace);
          (name_declare_mind, MHead Mdeclare_mind);
          (name_existing_instance, MHead Mexisting_instance);
          (name_instantiate_evar, MHead Minstantiate_evar);
        ]
      in
      let bindings = List.map (fun (cst, bnd) -> Names.GlobRef.ConstRef cst, bnd) bindings in
      Names.GlobRef.Map.of_list bindings
    )
end

let mconstr_head_of h =
  Names.GlobRef.Map.find (Names.GlobRef.ConstRef h) (Lazy.force ConstructorMap.map)

let mconstr_head_opt h =
  match mconstr_head_of h with
  | mh -> Some(mh)
  | exception Not_found -> None

let mconstr_of (type a) args (h : a mconstr_head) =
  match h with
  | Mret -> MConstr (Mret,(args 0, args 1))
  | Mbind -> MConstr (Mbind, (args 0, args 1, args 2, args 3))
  | Mmtry' -> MConstr (Mmtry', (args 0, args 1, args 2))
  | Mraise' -> MConstr (Mraise', (args 0, args 1))
  | Mfix1 ->
      let n = 1 in
      let m = n+2 in
      let types = (args 0) in
      let ret = (args n) in
      let bod = (args (n+1)) in
      let vals = (args (m+0)) in
      MConstr (Mfix1, (types, ret, bod, vals))
  | Mfix2 ->
      let n = 2 in
      let m = n+2 in
      let types = (args 0, args 1) in
      let ret = (args n) in
      let bod = (args (n+1)) in
      let vals = (args (m+0), args (m+1)) in
      MConstr (Mfix2, (types, ret, bod, vals))
  | Mfix3 ->
      let n = 3 in
      let m = n+2 in
      let types = (args 0, args 1, args 2) in
      let ret = (args n) in
      let bod = (args (n+1)) in
      let vals = (args (m+0), args (m+1), args (m+2)) in
      MConstr (Mfix3, (types, ret, bod, vals))
  | Mfix4 ->
      let n = 4 in
      let m = n+2 in
      let types = (args 0, args 1, args 2, args 3) in
      let ret = (args n) in
      let bod = (args (n+1)) in
      let vals = (args (m+0), args (m+1), args (m+2), args (m+3)) in
      MConstr (Mfix4, (types, ret, bod, vals))
  | Mfix5 ->
      let n = 5 in
      let m = n+2 in
      let types = (args 0, args 1, args 2, args 3, args 4) in
      let ret = (args n) in
      let bod = (args (n+1)) in
      let vals = (args (m+0), args (m+1), args (m+2), args (m+3), args (m+4)) in
      MConstr (Mfix5, (types, ret, bod, vals))
  | Mis_var ->
      MConstr (Mis_var, (args 0, args 1))
  | Mnu ->
      MConstr (Mnu, (args 0, args 1, args 2, args 3, args 4))
  | Mnu_let ->
      MConstr (Mnu_let, (args 0, args 1, args 2, args 3, args 4, args 5))
  | Mabs_fun ->
      MConstr (Mabs_fun, (args 0, args 1, args 2, args 3))
  | Mabs_let ->
      MConstr (Mabs_let, (args 0, args 1, args 2, args 3, args 4))
  | Mabs_prod_type ->
      MConstr (Mabs_prod_type, (args 0, args 1, args 2))
  | Mabs_prod_prop ->
      MConstr (Mabs_prod_prop, (args 0, args 1, args 2))
  | Mabs_fix ->
      MConstr (Mabs_fix, (args 0, args 1, args 2, args 3))
  | Mget_binder_name ->
      MConstr (Mget_binder_name, (args 0, args 1))
  | Mremove ->
      MConstr (Mremove, (args 0, args 1, args 2, args 3))
  | Mgen_evar ->
      MConstr (Mgen_evar, (args 0, args 1))
  | Mis_evar ->
      MConstr (Mis_evar, (args 0, args 1))
  | Mhash ->
      MConstr (Mhash, (args 0, args 1, args 2))
  | Msolve_typeclasses ->
      MConstr (Msolve_typeclasses, ())
  | Mprint ->
      MConstr (Mprint, (args 0))
  | Mpretty_print ->
      MConstr (Mpretty_print, (args 0, args 1))
  | Mhyps ->
      MConstr (Mhyps, ())
  | Mdestcase ->
      MConstr (Mdestcase, (args 0, args 1))
  | Mconstrs ->
      MConstr (Mconstrs, (args 0, args 1))
  | Mmakecase ->
      MConstr (Mmakecase, (args 0))
  | Munify ->
      MConstr (Munify, (args 0, args 1, args 2, args 3, args 4, args 5, args 6))
  | Munify_cumul ->
      MConstr (Munify_cumul, (args 0, args 1, args 2, args 3, args 4, args 5))
  | Mget_reference ->
      MConstr (Mget_reference, (args 0))
  | Mget_var ->
      MConstr (Mget_var, (args 0))
  | Mcall_ltac ->
      MConstr (Mcall_ltac, (args 0, args 1, args 2, args 3))
  | Mlist_ltac ->
      MConstr (Mlist_ltac, ())
  | Mread_line ->
      MConstr (Mread_line, ())
  | Mdecompose ->
      MConstr (Mdecompose, (args 0, args 1))
  | Msolve_typeclass ->
      MConstr (Msolve_typeclass, (args 0))
  | Mdeclare ->
      MConstr (Mdeclare, (args 0, args 1, args 2, args 3, args 4))
  | Mdeclare_implicits ->
      MConstr (Mdeclare_implicits, (args 0, args 1, args 2))
  | Mos_cmd ->
      MConstr (Mos_cmd, (args 0))
  | Mget_debug_exceptions ->
      MConstr (Mget_debug_exceptions, ())
  | Mset_debug_exceptions ->
      MConstr (Mset_debug_exceptions, (args 0))
  | Mget_trace ->
      MConstr (Mget_trace, ())
  | Mset_trace ->
      MConstr (Mset_trace, (args 0))
  | Mdecompose_app' ->
      MConstr (Mdecompose_app', (args 0, args 1, args 2, args 3, args 4, args 5, args 6, args 7))
  | Mdecompose_forallT ->
      MConstr (Mdecompose_forallT, (args 0, args 1, args 2, args 3))
  | Mdecompose_forallP ->
      MConstr (Mdecompose_forallP, (args 0, args 1, args 2, args 3))
  | Mdecompose_app'' ->
      MConstr (Mdecompose_app'', (args 0, args 1, args 2, args 3))
  | Mnew_timer ->
      MConstr (Mnew_timer, (args 0, args 1))
  | Mstart_timer ->
      MConstr (Mstart_timer, (args 0, args 1, args 2))
  | Mstop_timer ->
      MConstr (Mstop_timer, (args 0, args 1))
  | Mreset_timer ->
      MConstr (Mreset_timer, (args 0, args 1))
  | Mprint_timer ->
      MConstr (Mprint_timer, (args 0, args 1))
  | Mkind_of_term ->
      MConstr (Mkind_of_term, (args 0, args 1))
  | Mreplace ->
      MConstr (Mreplace, (args 0, args 1, args 2, args 3, args 4, args 5))
  | Mdeclare_mind ->
      MConstr (Mdeclare_mind, (args 0, args 1, args 2))
  | Mexisting_instance ->
      MConstr (Mexisting_instance, (args 0, args 1, args 2))
  | Minstantiate_evar ->
      MConstr (Minstantiate_evar, (args 0, args 1, args 2, args 3, args 4, args 5))
