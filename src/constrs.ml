open Constr
open EConstr

let reduce_value = Tacred.compute

let decompose_appvect sigma c =
  match kind sigma c with
  | App (f,cl) -> (f, cl)
  | _ -> (c,[||])

module Constrs = struct
  exception Constr_not_found of string
  exception Constr_poly of string

  let glob_to_string gr = Libnames.string_of_path (Nametab.path_of_global gr)

  let mkGlobal name = lazy (Nametab.global_of_path (Libnames.path_of_string name))

  let mkConstr_of_global gr =
    let gr = Lazy.force gr in
    try of_constr @@
      UnivGen.constr_of_monomorphic_global gr
    with Not_found -> raise (Constr_not_found (glob_to_string gr))
       | Invalid_argument _ -> raise (Constr_poly (glob_to_string gr))

  let mkConstr name =
    lazy (mkConstr_of_global (mkGlobal name))

  let mkUGlobal name =
    Nametab.global_of_path (Libnames.path_of_string name)

  let mkUConstr_of_global gr sigma env =
    try fresh_global env sigma gr
    with Not_found ->
      raise (Constr_not_found (glob_to_string gr))

  let mkUConstr name sigma env = mkUConstr_of_global (mkUGlobal name) sigma env

  let isGlobal sigma r c =
    Globnames.is_global (Lazy.force r) (to_constr sigma c)

  let isConstr sigma = fun r c -> eq_constr_nounivs sigma (Lazy.force r) c

  let isUConstr r sigma env =
    is_global sigma r

end

module ConstrBuilder = struct
  open Constrs

  type t = Names.GlobRef.t Lazy.t

  let from_string (s:string) : t = lazy (Nametab.global_of_path (Libnames.path_of_string s))

  let build (s : t) = mkConstr_of_global s
  let build_app s args = mkApp (mkConstr_of_global s, args)

  let equal sigma s = isGlobal sigma s

  let from_coq s (_, sigma) cterm =
    let (head, args) = decompose_appvect sigma cterm in
    if equal sigma s head then Some args else None
end

module UConstrBuilder = struct
  open Constrs

  type t = Names.GlobRef.t Lazy.t

  let from_string (s:string) : t = lazy (Nametab.global_of_path (Libnames.path_of_string s))

  let print v = Printer.pr_global (Lazy.force v)

  let build_app s sigma env args =
    let (sigma, c) = mkUConstr_of_global (Lazy.force s) sigma env in
    (sigma, mkApp (c, args))

  let equal s = isUConstr (Lazy.force s)

  let from_coq s (env, sigma) cterm =
    let (head, args) = decompose_appvect sigma cterm in
    if equal s sigma env head then Some args else None
end

module CoqOption = struct
  open UConstrBuilder

  (* let optionBuilder = from_string "Mtac2.lib.Datatypes.moption" *)
  let noneBuilder = from_string "Mtac2.lib.Datatypes.mNone"
  let someBuilder = from_string "Mtac2.lib.Datatypes.mSome"

  (* let mkType sigma env ty = build_app optionBuilder sigma env [|ty|] *)
  let mkNone sigma env ty = build_app noneBuilder sigma env [|ty|]
  let mkSome sigma env ty t = build_app someBuilder sigma env [|ty; t|]

  exception NotAnOption

  let from_coq sigma env cterm =
    match from_coq noneBuilder (env, sigma) cterm with
    | None ->
        begin match from_coq someBuilder (env, sigma) cterm with
        | None -> raise NotAnOption
        | Some args -> Some args.(1)
        end
    | Some _ -> None

  let to_coq sigma env ty oterm =
    match oterm with
    | None -> mkNone sigma env ty
    | Some t -> mkSome sigma env ty t
end

module type ListParams = sig
  val nilname : string
  val consname : string
  val typename : string
end

module type LIST = sig
  val mkNil : Evd.evar_map -> Environ.env -> types -> Evd.evar_map * constr
  val mkCons : Evd.evar_map -> Environ.env -> types -> constr -> constr -> Evd.evar_map * constr
  val mkType : Evd.evar_map -> Environ.env -> types -> Evd.evar_map * types

  exception NotAList of constr

  val from_coq : Evd.evar_map -> Environ.env -> constr -> constr list

  (** Allows skipping an element in the conversion *)
  exception Skip
  val from_coq_conv : Evd.evar_map -> Environ.env -> (Evd.evar_map -> constr -> Evd.evar_map * 'a) -> constr -> Evd.evar_map * 'a list

  val to_coq : Evd.evar_map -> Environ.env -> types -> (Evd.evar_map -> 'a -> Evd.evar_map * constr) -> 'a list -> Evd.evar_map * constr
  val pto_coq : Environ.env -> types -> ('a -> Evd.evar_map -> Evd.evar_map * constr) -> 'a list -> Evd.evar_map -> Evd.evar_map * constr
end

module GenericList (LP : ListParams) = struct
  open UConstrBuilder

  let listBuilder = from_string LP.typename
  let nilBuilder  = from_string LP.nilname
  let consBuilder = from_string LP.consname

  let mkType sigma env ty = build_app listBuilder sigma env [|ty|]
  let mkNil sigma env ty = build_app nilBuilder sigma env [|ty|]
  let mkCons sigma env t x xs = build_app consBuilder sigma env [| t ; x ; xs |]

  exception Skip
  exception NotAList of constr
  (* given a list of terms and a convertion function fconv
     it creates a list of elements using the converstion function.
     if fconv raises Skip, that element is not included.
     if the list is ill-formed, an exception NotAList is raised. *)
  let from_coq_conv sigma env (fconv : Evd.evar_map -> constr -> Evd.evar_map * 'a) cterm =
    let rec fcc sigma cterm =
      match from_coq consBuilder (env, sigma) cterm with
      | None ->
          begin match from_coq nilBuilder (env, sigma) cterm with
          | None -> raise (NotAList cterm)
          | Some _ -> sigma, []
          end
      | Some args ->
          let (sigma, tail) = fcc sigma args.(2) in
          try
            let (sigma, h) = fconv sigma args.(1) in
            (sigma, h :: tail)
          with Skip ->
            (sigma, tail)
    in
    fcc sigma cterm

  let from_coq sigma env t =
    (* it is safe to throw away sigma here because we are not changing it *)
    snd (from_coq_conv sigma env (fun sigma (x:constr)->(sigma, x)) t)

  let to_coq sigma env ty f l =
    List.fold_right (fun e (sigma, l) -> let (sigma, t) = f sigma e in
                      mkCons sigma env ty t l)
      l
      (mkNil sigma env ty)

  let pto_coq env ty f l sigma =
    List.fold_right (fun e (sigma, l) ->
      let sigma, c = f e sigma in
      mkCons sigma env ty c l) l (mkNil sigma env ty)
end

module CoqList = GenericList (struct
    let nilname = "Mtac2.lib.Datatypes.mnil"
    let consname = "Mtac2.lib.Datatypes.mcons"
    let typename = "Mtac2.lib.Datatypes.mlist"
  end)


module type NELIST = sig
  val mkNil : Evd.evar_map -> Environ.env -> types -> constr -> Evd.evar_map * constr
  val mkCons : Evd.evar_map -> Environ.env -> types -> constr -> constr -> Evd.evar_map * constr
  val mkType : Evd.evar_map -> Environ.env -> types -> Evd.evar_map * types

  exception NotANEList of constr

  val from_coq : Evd.evar_map -> Environ.env -> constr -> constr list

  (** Allows skipping an element in the conversion *)
  exception Skip
  val from_coq_conv : Evd.evar_map -> Environ.env -> (Evd.evar_map -> constr -> Evd.evar_map * 'a) -> constr -> Evd.evar_map * 'a list

  val to_coq : Evd.evar_map -> Environ.env -> types -> (Evd.evar_map -> 'a -> Evd.evar_map * constr) -> 'a list -> Evd.evar_map * constr
end

module GenericNonEmptyList (LP : ListParams) = struct
  open UConstrBuilder

  let listBuilder = from_string LP.typename
  let nilBuilder  = from_string LP.nilname
  let consBuilder = from_string LP.consname

  let mkType sigma env ty = build_app listBuilder sigma env [|ty|]
  let mkNil sigma env t x = build_app nilBuilder sigma env [|t ; x|]
  let mkCons sigma env t x xs = build_app consBuilder sigma env [| t ; x ; xs |]

  exception Skip
  exception NotANEList of constr
  (* given a list of terms and a convertion function fconv
     it creates a list of elements using the converstion function.
     if fconv raises Skip, that element is not included.
     if the list is ill-formed, an exception NotAList is raised. *)
  let from_coq_conv sigma env (fconv : Evd.evar_map -> constr -> Evd.evar_map * 'a) cterm =
    let rec fcc sigma cterm =
      match from_coq consBuilder (env, sigma) cterm with
      | None ->
          begin match from_coq nilBuilder (env, sigma) cterm with
          | None -> raise (NotANEList cterm)
          | Some args ->
              let sigma, h = fconv sigma args.(1) in
              sigma, h :: []
          end
      | Some args ->
          let (sigma, tail) = fcc sigma args.(2) in
          try
            let (sigma, h) = fconv sigma args.(1) in
            (sigma, h :: tail)
          with Skip ->
            (sigma, tail)
    in
    fcc sigma cterm

  let from_coq sigma env t =
    (* it is safe to throw away sigma here because we are not changing it *)
    snd (from_coq_conv sigma env (fun sigma (x:constr)->(sigma, x)) t)

  let rec to_coq sigma env ty f l =
    match l with
    | [] -> failwith "List empty"
    | e :: [] -> let sigma, t = f sigma e in mkNil sigma env ty t
    | e :: l ->
        let sigma, t = f sigma e in
        let sigma, l = to_coq sigma env ty f l in
        mkCons sigma env ty t l
end

module CoqNEList = GenericNonEmptyList (struct
    let nilname = "Mtac2.lib.NEList.ne_sing"
    let consname = "Mtac2.lib.NEList.ne_cons"
    let typename = "Mtac2.lib.NEList.nelist"
  end)

module CoqEq = struct
  open UConstrBuilder

  let eqBuilder = from_string "Mtac2.lib.Logic.meq"
  let eqReflBuilder = from_string "Mtac2.lib.Logic.meq_refl"

  let mkType env sigma a x y = build_app eqBuilder env sigma [|a;x;y|]
  let mkEqRefl env sigma a x = build_app eqReflBuilder env sigma [|a;x|]
end

module CoqSig = struct
  let from_coq (env, sigma) constr =
    (* NOTE: Hightly unsafe *)
    let (_, args) = decompose_appvect sigma (Reductionops.whd_all env sigma constr) in
    args.(1)
end

module CoqPositive = struct
  open Constrs

  let xI = mkGlobal "Coq.Numbers.BinNums.xI"
  let xO = mkGlobal "Coq.Numbers.BinNums.xO"
  let xH = mkGlobal "Coq.Numbers.BinNums.xH"

  let isH sigma = isGlobal sigma xH
  let isI sigma = isGlobal sigma xI
  let isO sigma = isGlobal sigma xO

  let from_coq (env, evd) c =
    let rec fc i c =
      if isH evd c then
        1
      else
        let (s, n) = destApp evd c in
        begin
          if isI evd s then
            (fc (i+1) (n.(0)))*2 + 1
          else if isO evd s then
            (fc (i+1) (n.(0)))*2
          else
            CErrors.user_err Pp.(str "Not a positive")
        end
    in
    let c' = reduce_value env evd c in
    fc 0 c'

  let rec to_coq n =
    if n = 1 then
      mkConstr_of_global xH
    else if n mod 2 = 0 then
      mkApp(mkConstr_of_global xO, [|to_coq (n / 2)|])
    else
      mkApp(mkConstr_of_global xI, [|to_coq ((n-1)/2)|])
end

module CoqN = struct
  open Constrs
  (* let tN = Constr.mkConstr "Coq.Numbers.BinNums.N" *)
  let h0 = mkGlobal "Coq.Numbers.BinNums.N0"
  let hP = mkGlobal "Coq.Numbers.BinNums.Npos"

  let is0 sigma = isGlobal sigma h0
  let isP sigma = isGlobal sigma hP

  exception NotAnN

  let from_coq (env, evd) c =
    let fc c =
      if is0 evd c then
        0
      else
        let (s, n) = destApp evd c in
        begin
          if isP evd s then
            CoqPositive.from_coq (env, evd) (n.(0))
          else
            raise NotAnN
        end
    in
    let c' = reduce_value env evd c in
    fc c'

  let to_coq n =
    if n = 0 then
      mkConstr_of_global h0
    else
      mkApp(mkConstr_of_global hP, [|CoqPositive.to_coq n|])
end

module CoqZ = struct
  open Constrs

  let z0 =   mkGlobal "Coq.Numbers.BinNums.Z0"
  let zpos = mkGlobal "Coq.Numbers.BinNums.Zpos"
  let zneg = mkGlobal "Coq.Numbers.BinNums.Zneg"

  let to_coq n =
    if n = 0 then
      mkConstr_of_global z0
    else if n > 0 then
      mkApp(mkConstr_of_global zpos, [|CoqPositive.to_coq n|])
    else
      mkApp(mkConstr_of_global zneg, [|CoqPositive.to_coq n|])
end

module CoqBool = struct
  open ConstrBuilder

  let boolBuilder = from_string "Coq.Init.Datatypes.bool"
  let trueBuilder = from_string "Coq.Init.Datatypes.true"
  let falseBuilder = from_string "Coq.Init.Datatypes.false"

  let mkType = build boolBuilder
  let mkTrue = build trueBuilder
  let mkFalse = build falseBuilder

  exception NotABool

  let to_coq b = if b then mkTrue else mkFalse
  let from_coq sigma c =
    if equal sigma trueBuilder c then true
    else if equal sigma falseBuilder c then false
    else raise NotABool
end

module CoqAscii = struct
  open ConstrBuilder

  let asciiBuilder = from_string "Coq.Strings.Ascii.Ascii"

  let from_coq (_, sigma) c =
    let (h, args) = decompose_appvect sigma c in
    let rec from_bits n =
      if n >= Array.length args then 0
      else (if CoqBool.from_coq sigma args.(n) then 1 else 0) lsl n + from_bits (n+1)
    in
    let n = from_bits 0 in
    String.make 1 (Char.chr n)

  let to_coq c =
    let c = int_of_char c in
    let a = Array.init 8 (fun i->(c lsr i) mod 2 = 1) in
    let a = Array.map CoqBool.to_coq a in
    build_app asciiBuilder a
end

module CoqString = struct
  open ConstrBuilder

  let emptyBuilder = from_string "Coq.Strings.String.EmptyString"
  let stringBuilder = from_string "Coq.Strings.String.String"

  exception NotAString

  let from_coq (env, sigma as ctx) s =
    let rec fc s =
      let (h, args) = decompose_appvect sigma s in
      if equal sigma emptyBuilder h then ""
      else if equal sigma stringBuilder h then
        CoqAscii.from_coq ctx args.(0) ^ fc args.(1)
      else
        raise NotAString
    in
    fc (reduce_value env sigma s)

  let rec to_coq s =
    if String.length s = 0 then
      build emptyBuilder
    else
      build_app stringBuilder [|
        CoqAscii.to_coq s.[0];
        to_coq (String.sub s 1 (String.length s -1))|]
end

module CoqUnit = struct
  open ConstrBuilder

  let unitBuilder = from_string "Coq.Init.Datatypes.unit"
  let ttBuilder = from_string "Coq.Init.Datatypes.tt"

  let mkType = build unitBuilder
  let mkTT = build ttBuilder
end

module MCTactics = struct
  open UConstrBuilder

  let gTactic = from_string "Mtac2.tactics.TacticsBase.gtactic"

  (* let mkConstr s = *)
  (*   let open Nametab in let open Libnames in *)
  (*   try Universes.constr_of_global (locate (qualid_of_string s)) *)
  (*   with _ -> raise (Constr.Constr_not_found s) *)

  let mkGTactic env sigma = build_app gTactic sigma env [||]
end

module CoqPair = struct
  open UConstrBuilder

  let prodBuilder = from_string "Mtac2.lib.Datatypes.mprod"
  let pairBuilder = from_string "Mtac2.lib.Datatypes.mpair"

  let mkPair sigma env tya tyb a b = build_app pairBuilder sigma env [|tya;tyb;a;b|]

  exception NotAPair

  let mkType sigma env tya tyb = build_app prodBuilder sigma env [|tya; tyb|]

  let from_coq ctx cterm =
    match from_coq pairBuilder ctx cterm with
    | None -> raise NotAPair
    | Some args -> (args.(2), args.(3))
end

module CoqMTele = struct
  open UConstrBuilder

  let tybuilder = from_string "Mtac2.intf.MTele.MTele"
  let mBaseBuilder = from_string "Mtac2.intf.MTele.mBase"
  let mTeleBuilder = from_string "Mtac2.intf.MTele.mTele"

  exception NotAnMTele

  let mkType sigma env = build_app tybuilder sigma env [||]

  let from_coq sigma env cterm =
    match from_coq mTeleBuilder (env, sigma) cterm with
    | None ->
        begin match from_coq mBaseBuilder (env, sigma) cterm with
        | None -> raise NotAnMTele
        | Some _ -> None
        end
    | Some args -> Some (args.(0), args.(1))

  let of_rel_context sigma env (ctx : Constr.rel_context) =
    List.fold_left (fun (sigma, acc) decl ->
      let open Context.Rel.Declaration in
      match decl with
      | LocalDef _ -> failwith "Let bindings not supported in MTele."
      | LocalAssum (name, ty) ->
          let ty = EConstr.of_constr ty in
          let closure = EConstr.mkLambda (name, ty, acc) in
          build_app mTeleBuilder sigma env [|ty; closure|]
    ) (build_app mBaseBuilder sigma env [||]) ctx

  let rec fold_left sigma env f acc t  =
    match from_coq sigma env t with
    | None -> acc
    | Some ((typeX,contF)) ->
        let (name,ty,t) = destLambda sigma contF in
        let acc = f acc (name, typeX) in
        fold_left sigma env f acc t

  let rec fold_right sigma env f acc t  =
    match from_coq sigma env t with
    | None -> acc
    | Some ((typeX,contF)) ->
        let (name,ty,body) = destLambda sigma contF in
        f name ty body (fold_right sigma env f acc body)

  (* turns [[tele x .. z]] and [fun x .. z => T] into [forall x .. z, b(T)] *)
  let to_foralls sigma env tele funs b =
    let n_args, funs, binders = fold_left sigma env (fun (n,funs,acc) (name, typeX) ->
      let (name, ty, funs) = destLambda sigma funs in
      (n+1, funs, (name, ty)::acc)
    ) (0, funs, []) tele
    in
    let sigma, funs = b sigma n_args funs in
    let arity = List.fold_left (fun t (name, ty) -> EConstr.mkProd (name, ty, t)) funs binders in
    sigma, n_args, arity

  (* turns arity [forall x .. z, S] into [(S, [tele x .. z])].  *)
  let rec of_arity sigma env arity =
    match kind sigma arity with
    | Prod (name, ty, arity) ->
        let sigma, s, tele = of_arity sigma env arity in
        let body = mkLambda (name, ty, tele) in
        let sigma, t = build_app mTeleBuilder sigma env [|ty; body|] in
        sigma, s, t
    | _ -> let sigma, t = build_app mBaseBuilder sigma env [||] in sigma, arity, t
end

module CoqSigT = struct
  open UConstrBuilder
  let mexistTBuilder = from_string "Mtac2.lib.Specif.mexistT"

  exception NotAmexistT

  let from_coq sigma env cterm =
    match from_coq mexistTBuilder (env, sigma) cterm with
    | None -> raise NotAmexistT
    | Some args -> (args.(2), args.(3))

  let to_coq =
    build_app mexistTBuilder
end


module CoqArgsOf = struct
  open UConstrBuilder
  let argsofBuilder = from_string "Mtac2.intf.MTele.ArgsOf"

  let of_arguments sigma env tele args =
    let sigma, args, argsof = CoqMTele.fold_right sigma env (
      fun name ty body (sigma, args, acc) ->
        let head, args = match args with
          | [] -> failwith "Not enough arguments for telescope."
          | head :: args ->  head, args
        in
        (* the type below is only valid in a context with binder 0 of type ty *)
        let sigma, argsof_ty = build_app argsofBuilder sigma env [|body|] in
        (* and here's it's put into a lambda that adds that binder *)
        let predicate = mkLambda (name, ty, argsof_ty) in
        let sigma, argsof = CoqSigT.to_coq sigma env [|ty; predicate; head; acc|] in
        sigma, args, argsof
    ) (sigma, args, CoqUnit.mkTT) tele
    in
    sigma, argsof, args
end


module CoqSort = struct
  open UConstrBuilder

  let sType = from_string "Mtac2.intf.Sorts.S.Type_sort"
  let sProp = from_string "Mtac2.intf.Sorts.S.Prop_sort"

  let mkSType env sigma = build_app sType sigma env [||]
  let mkSProp env sigma = build_app sProp sigma env [||]

  exception NotASort

  type sort = Prop_sort | Type_sort

  let from_coq sigma env cterm =
    match from_coq sProp (env, sigma) cterm with
    | Some args -> Prop_sort
    | None ->
        match from_coq sType (env, sigma) cterm with
        | None -> raise NotASort
        | Some args -> Type_sort

  let to_coq sigma env = function
    | Prop_sort -> mkSProp env sigma
    | Type_sort -> mkSType env sigma


end

module CoqInd_Dyn = struct
  open UConstrBuilder
  let mkInd_dyn = from_string "Mtac2.intf.Case.mkInd_dyn"

  exception NotAmkInd_dyn

  let from_coq sigma env cterm =
    match from_coq mkInd_dyn (env, sigma) cterm with
    | None -> raise NotAmkInd_dyn
    | Some args -> args

  let to_coq = build_app mkInd_dyn

end

module type CoqRecord = sig
  val constructor : UConstrBuilder.t
  val ty : UConstrBuilder.t
  exception NotInConstructorNormalForm of String.t
  val mkTy : Evd.evar_map -> Environ.env -> Evd.econstr array -> Evd.evar_map * Evd.econstr
  val from_coq : Evd.evar_map -> Environ.env -> Evd.econstr -> Evd.econstr array
  val to_coq :
    Evd.evar_map ->
    Environ.env -> Evd.econstr array -> Evd.evar_map * Evd.econstr
end


module MkCoqRecord (F : sig
    val type_name : string
    val constructor_name : string
  end) : CoqRecord = struct
  open UConstrBuilder

  let ty = from_string F.type_name
  let constructor = from_string F.constructor_name

  exception NotInConstructorNormalForm of String.t

  let mkTy sigma env args =
    build_app ty sigma env args

  let from_coq sigma env cterm =
    match from_coq constructor (env, sigma) cterm with
    | None ->
        let expected = (UConstrBuilder.print constructor) in
        let found = (Printer.pr_econstr_env env sigma cterm) in
        let open Pp in
        let msg = str "Expected constructor " ++ expected ++ str " but found term " ++ found ++ str " instead" in
        let msg = Pp.string_of_ppcmds msg in
        raise (NotInConstructorNormalForm msg)
    | Some args -> args

  let to_coq =
    build_app constructor
end

module MkCoqRecordDefault (F : sig val path : string val type_name : string end) =
  MkCoqRecord (struct
    let type_name = String.concat "" [F.path; "."; F.type_name]
    let constructor_name = String.concat "" [F.path; "."; "Build_"; F.type_name]
  end)

module type CoqRecordVec = sig
  include CoqRecord
  module N : Typelevel.T
  val from_coq_vec :
    Evd.evar_map -> Environ.env -> Evd.econstr -> (N.t, Evd.econstr) Typelevel.Vector.nlist
end
open Typelevel.Nat
module type CoqRecordVec2 = sig include CoqRecordVec with type N.t = o s s end
module type CoqRecordVec3 = sig include CoqRecordVec with type N.t = o s s s end
module type CoqRecordVec4 = sig include CoqRecordVec with type N.t = o s s s s end
module type CoqRecordVec5 = sig include CoqRecordVec with type N.t = o s s s s s end
module type CoqRecordVec6 = sig include CoqRecordVec with type N.t = o s s s s s s end
module type CoqRecordVec7 = sig include CoqRecordVec with type N.t = o s s s s s s s end

(* module MkCoqRecordVec2 (R : CoqRecord) ( ) : CoqRecordVec2 = struct
 *   include R
 *   module N = struct type t = o s s let wit = S (S O) end
 *   let from_coq_vec sigma env cterm =
 *     (\* let () = Feedback.msg_debug (Printer.pr_econstr_env (Global.env()) sigma cterm) in *\)
 *     let arr = (from_coq sigma env cterm) in
 *     (\* let () = Feedback.msg_debug (Pp.pr_vertical_list (Printer.pr_econstr_env (Global.env()) sigma) (Array.to_list arr)) in *\)
 *     Typelevel.Vector.from_array N.wit arr
 * end *)
module MkCoqRecordVec3 (R : CoqRecord) ( ) : CoqRecordVec3 = struct
  include R
  module N = struct type t = o s s s let wit = S (S (S O)) end
  let from_coq_vec sigma env cterm = Typelevel.Vector.from_array N.wit (from_coq sigma env cterm)
end
module MkCoqRecordVec4 (R : CoqRecord) ( ) : CoqRecordVec4 = struct
  include R
  module N = struct type t = o s s s s let wit = S (S (S (S O))) end
  let from_coq_vec sigma env cterm = Typelevel.Vector.from_array N.wit (from_coq sigma env cterm)
end
module MkCoqRecordVec5 (R : CoqRecord) ( ) : CoqRecordVec5 = struct
  include R
  module N = struct type t = o s s s s s let wit = S (S (S (S (S O)))) end
  let from_coq_vec sigma env cterm = Typelevel.Vector.from_array N.wit (from_coq sigma env cterm)
end
module MkCoqRecordVec7 (R : CoqRecord) ( ) : CoqRecordVec7 = struct
  include R
  module N = struct type t = o s s s s s s s let wit = S (S (S (S (S (S (S O)))))) end
  let from_coq_vec sigma env cterm = Typelevel.Vector.from_array N.wit (from_coq sigma env cterm)
end

module CoqIndSigRecord = MkCoqRecordDefault (struct let path = "Mtac2.intf.Case.Inductive" let type_name = "Sig" end)
module CoqIndSig = MkCoqRecordVec3 (CoqIndSigRecord) ()

module CoqIndDefRecord = MkCoqRecordDefault (struct let path = "Mtac2.intf.Case.Inductive" let type_name = "Def" end)
module CoqIndDef = MkCoqRecordVec3 (CoqIndDefRecord) ()

module CoqConstrDefRecord = MkCoqRecordDefault (struct let path = "Mtac2.intf.Case.Constructor.Unpar" let type_name = "Def" end)
module CoqConstrDef = MkCoqRecordVec4 (CoqConstrDefRecord) ()

module CoqConstrDefWopRecord = MkCoqRecordDefault (struct let path = "Mtac2.intf.Case.Constructor.Par" let type_name = "Def" end)
module CoqConstrDefWop = MkCoqRecordVec5 (CoqConstrDefWopRecord) ()

module CoqMindSpecRecord = MkCoqRecordDefault (struct let path = "Mtac2.intf.Case.Mutual" let type_name = "Def" end)
module CoqMindSpec = MkCoqRecordVec4 (CoqMindSpecRecord) ()

module CoqMindRecord = MkCoqRecordDefault (struct let path = "Mtac2.intf.Case.Mutual" let type_name = "Val" end)
module CoqMind = MkCoqRecordVec3 (CoqMindRecord) ()

module CoqMindRecordDep = MkCoqRecordDefault (struct let path = "Mtac2.intf.Case.Mutual.OfDef" let type_name = "Val" end)
module CoqMindDep = MkCoqRecordVec3 (CoqMindRecordDep) ()

module CoqMindEntryRecord = MkCoqRecordDefault (struct let path = "Mtac2.intf.Case.Mutual" let type_name = "Nth" end)
module CoqMindEntry = MkCoqRecordVec4 (CoqMindEntryRecord) ()

module CoqMatchRecord = MkCoqRecordDefault (struct let path = "Mtac2.intf.Case.Match" let type_name = "Val" end)
module CoqMatch = MkCoqRecordVec7 (CoqMatchRecord) ()

module CoqConstr_Dyn = struct
  open UConstrBuilder
  let mkConstr_dyn = from_string "Mtac2.intf.Case.mkConstr_dyn"

  exception NotAmkConstr_dyn

  let from_coq sigma env cterm =
    match from_coq mkConstr_dyn (env, sigma) cterm with
    | None -> raise NotAmkConstr_dyn
    | Some args -> args

  let to_coq = build_app mkConstr_dyn

  let mkType sigma env = build_app (from_string "Mtac2.intf.Case.Constr_dyn") sigma env [||]

end
