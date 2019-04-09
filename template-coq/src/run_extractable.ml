open Extractable
open Plugin_core
open BasicAst

open Quoter
open Ast_quoter


let of_constr (env : Environ.env) (t : Constr.t) : Ast0.term =
  Ast_quoter.quote_term env t

let to_string : char list -> string =
  Quoted.list_to_string

let of_string : string -> char list =
  Quoted.string_to_list

let to_reduction_strategy (s : Common.reductionStrategy) =
  failwith "to_reduction_strategy"

let to_ident : char list ->  Names.Id.t =
  Ast_quoter.unquote_ident

let of_ident (id : Names.Id.t) : char list =
  of_string (Names.Id.to_string id)

let of_global_reference : Plugin_core.global_reference -> BasicAst.global_reference =
  Ast_quoter.quote_global_reference

let to_qualid (c : char list) : Libnames.qualid =
  Libnames.qualid_of_string (to_string c)

let of_qualid (q : Libnames.qualid) : char list =
  of_string (Libnames.string_of_qualid q)

let of_kername : Names.KerName.t -> char list =
  Ast_quoter.quote_kn

let to_kername (s : char list) : Names.KerName.t =
  failwith "of_kername"

(* todo(gmm): this definition adapted from quoter.ml *)
let quote_rel_decl env = function
  | Context.Rel.Declaration.LocalAssum (na, t) ->
    let t' = Ast_quoter.quote_term env t in
    Ast_quoter.quote_context_decl (Ast_quoter.quote_name na) None t'
  | Context.Rel.Declaration.LocalDef (na, b, t) ->
    let b' = Ast_quoter.quote_term env b in
    let t' = Ast_quoter.quote_term env t in
    Ast_quoter.quote_context_decl (Ast_quoter.quote_name na) (Some b') t'

(* todo(gmm): this definition adapted from quoter.ml *)
let quote_rel_context env ctx =
  let decls, env =
    List.fold_right (fun decl (ds, env) ->
        let x = quote_rel_decl env decl in
        (x :: ds, Environ.push_rel decl env))
      ctx ([],env) in
  Ast_quoter.quote_context decls

(* todo(gmm): this definition adapted from quoter.ml (the body of quote_minductive_type) *)
let of_mib (env : Environ.env) (mib : Plugin_core.mutual_inductive_body) : Ast0.mutual_inductive_body =
  let open Declarations in
  let uctx = get_abstract_inductive_universes mib.mind_universes in
  let inst = Univ.UContext.instance uctx in
  let indtys =
    (CArray.map_to_list (fun oib ->
         let ty = Inductive.type_of_inductive env ((mib,oib),inst) in
         (Context.Rel.Declaration.LocalAssum (Names.Name oib.mind_typename, ty))) mib.mind_packets)
  in
  let envind = Environ.push_rel_context (List.rev indtys) env in
  let (ls,acc) =
    List.fold_left (fun (ls,acc) oib ->
	let named_ctors =
	  CList.combine3
	    (Array.to_list oib.mind_consnames)
	    (Array.to_list oib.mind_user_lc)
	    (Array.to_list oib.mind_consnrealargs)
	in
        let indty = Inductive.type_of_inductive env ((mib,oib),inst) in
        let indty = Ast_quoter.quote_term env indty in
	let (reified_ctors,acc) =
	  List.fold_left (fun (ls,acc) (nm,ty,ar) ->
	      Tm_util.debug (fun () -> Pp.(str "opt_hnf_ctor_types:" ++ spc () ++
                                   bool !opt_hnf_ctor_types)) ;
	      let ty = if !opt_hnf_ctor_types then hnf_type envind ty else ty in
	      let ty = quote_term acc ty in
	      ((Ast_quoter.quote_ident nm, ty, Ast_quoter.quote_int ar) :: ls, acc))
	    ([],acc) named_ctors
	in
        let projs, acc =
          match mib.mind_record with
          | Some (Some (id, csts, ps)) ->
            let ctxwolet = Termops.smash_rel_context mib.mind_params_ctxt in
            let indty = Constr.mkApp (Constr.mkIndU ((assert false (* t *),0),inst),
                                      Context.Rel.to_extended_vect Constr.mkRel 0 ctxwolet) in
            let indbinder = Context.Rel.Declaration.LocalAssum (Names.Name id,indty) in
            let envpars = Environ.push_rel_context (indbinder :: ctxwolet) env in
            let ps, acc = CArray.fold_right2 (fun cst pb (ls,acc) ->
                let ty = quote_term envpars pb.proj_type in
                let kn = Names.KerName.label (Names.Constant.canonical cst) in
                let na = Ast_quoter.quote_ident (Names.Label.to_id kn) in
                ((na, ty) :: ls, acc)) csts ps ([],acc)
            in ps, acc
          | _ -> [], acc
        in
        let sf = List.map Ast_quoter.quote_sort_family oib.mind_kelim in
	(Ast_quoter.quote_ident oib.mind_typename, indty, sf, (List.rev reified_ctors), projs) :: ls, acc)
      ([],env) (Array.to_list mib.mind_packets)
  in
  let nparams = Ast_quoter.quote_int mib.mind_nparams in
  let paramsctx = quote_rel_context env mib.mind_params_ctxt in
  let uctx = quote_abstract_inductive_universes mib.mind_universes in
  let bodies = List.map Ast_quoter.mk_one_inductive_body (List.rev ls) in
  Ast_quoter.mk_mutual_inductive_body nparams paramsctx bodies uctx

let to_mie x : Plugin_core.mutual_inductive_entry =
  failwith "to_mie"

(* note(gmm): code taken from quoter.ml (quote_entry_aux) *)
let of_constant_entry (env : Environ.env) (cd : Plugin_core.constant_entry) : Ast0.constant_entry =
  let open Declarations in
  let ty = quote_term env cd.const_type in
  let body = match cd.const_body with
    | Undef _ -> None
    | Def cs -> Some (Ast_quoter.quote_term env (Mod_subst.force_constr cs))
    | OpaqueDef cs ->
      if true
      then Some (Ast_quoter.quote_term env (Opaqueproof.force_proof (Global.opaque_tables ()) cs))
      else None
  in
  let uctx = quote_constant_uctx cd.const_universes in
  Ast_quoter.quote_constant_entry (ty, body, uctx)

(* what about the overflow?
  efficiency? extract to bigint using Coq directives and convert to int here? *)
let of_nat (t : Datatypes.nat) : int =
  failwith "of_constr"

let of_cast_kind (ck: BasicAst.cast_kind) : Constr.cast_kind =
  match ck with
  | VmCast -> Constr.VMcast
  | NativeCast -> Constr.VMcast
  | Cast -> Constr.DEFAULTcast
  | RevertCast -> Constr.REVERTcast


  (* todo(gmm): determine what of these already exist. *)
let rec to_constr_ev (evm : Evd.evar_map) (t : Ast0.term) : Evd.evar_map * Constr.t =
  failwith "to_constr_ev" (*
  match t with
  | Coq_tRel x -> evm, Constr.mkRel (of_nat x + 1)
  | Coq_tVar x -> evm, Constr.mkVar (to_ident x)
  | Coq_tCast (t,c,ty) -> let evm, t = to_constr_ev evm t in
    let evm, ty = to_constr_ev evm ty in
    evm, Constr.mkCast (t, of_cast_kind c, ty)
  (* the next case is quite complex: look at Denote.unquote_universe *)
  | Coq_tSort u -> evm, Constr.mkType u
  | Coq_tProd (n,t,b) -> let evm, t = aux evm t in
    let evm, b = aux evm b in
    evm, Constr.mkProd (unquote_name n, t, b)
  | Coq_tLambda (n,t,b) -> let evm, t = aux evm t in
    let evm, b = aux evm b in
    evm, Constr.mkLambda (unquote_name n, t, b)
  | Coq_tLetIn (n,e,t,b) -> let evm, e = aux evm e in
    let evm, t = aux evm t in
    let evm, b = aux evm b in
    evm, Constr.mkLetIn (unquote_name n, e, t, b)
  | Coq_tApp (f,xs) -> let evm, f = aux evm f in
    let evm, xs = map_evm aux evm xs in
    evm, Constr.mkApp (f, Array.of_list xs)
  | Coq_tConst (s,u) ->
    let s = unquote_kn s in
    let evm, u = unquote_universe_instance evm u in
    (try
       match Nametab.locate s with
       | Globnames.ConstRef c -> evm, Constr.mkConstU (c, u)
       | Globnames.IndRef _ -> CErrors.user_err (str"The constant " ++ Libnames.pr_qualid s ++ str" is an inductive, use tInd.")
       | Globnames.VarRef _ -> CErrors.user_err (str"The constant " ++ Libnames.pr_qualid s ++ str" is a variable, use tVar.")
       | Globnames.ConstructRef _ -> CErrors.user_err (str"The constant " ++ Libnames.pr_qualid s ++ str" is a constructor, use tConstructor.")
     with
       Not_found -> CErrors.user_err (str"Constant not found: " ++ Libnames.pr_qualid s))
  | Coq_tConstruct (i,idx,u) ->
    let ind = unquote_inductive i in
    let evm, u = unquote_universe_instance evm u in
    evm, Constr.mkConstructU ((ind, unquote_nat idx + 1), u)
  | Coq_tInd (i, u) ->
    let i = unquote_inductive i in
    let evm, u = unquote_universe_instance evm u in
    evm, Constr.mkIndU (i, u)
  | Coq_tCase ((i, _), ty, d, brs) ->
    let ind = unquote_inductive i in
    let evm, ty = aux evm ty in
    let evm, d = aux evm d in
    let evm, brs = map_evm aux evm (List.map snd brs) in
    (* todo: reify better case_info *)
    let ci = Inductiveops.make_case_info (Global.env ()) ind Constr.RegularStyle in
    evm, Constr.mkCase (ci, ty, d, Array.of_list brs)
  | Coq_tFix (lbd, i) ->
    let (names,types,bodies,rargs) = (List.map (fun p->p.adname) lbd,  List.map (fun p->p.adtype) lbd, List.map (fun p->p.adbody) lbd,
                                      List.map (fun p->p.rarg) lbd) in
    let evm, types = map_evm aux evm types in
    let evm, bodies = map_evm aux evm bodies in
    let (names,rargs) = (List.map unquote_name names, List.map unquote_nat rargs) in
    let la = Array.of_list in
    evm, Constr.mkFix ((la rargs,unquote_nat i), (la names, la types, la bodies))
  | Coq_tCoFix (lbd, i) ->
    let (names,types,bodies,rargs) = (List.map (fun p->p.adname) lbd,  List.map (fun p->p.adtype) lbd, List.map (fun p->p.adbody) lbd,
                                      List.map (fun p->p.rarg) lbd) in
    let evm, types = map_evm aux evm types in
    let evm, bodies = map_evm aux evm bodies in
    let (names,rargs) = (List.map unquote_name names, List.map unquote_nat rargs) in
    let la = Array.of_list in
    evm, Constr.mkCoFix (unquote_nat i, (la names, la types, la bodies))
  | Coq_tProj (proj,t) ->
    let (ind, _, narg) = unquote_proj proj in (* todo: is narg the correct projection? *)
    let ind' = unquote_inductive ind in
    let projs = Recordops.lookup_projections ind' in
    let evm, t = aux evm t in
    (match List.nth projs (unquote_nat narg) with
     | Some p -> evm, Constr.mkProj (Names.Projection.make p false, t)
     | None -> bad_term trm)
  | _ ->  not_supported_verb trm "big_case"
*)
let to_constr (t : Ast0.term) : Constr.t =
  snd (to_constr_ev Evd.empty t)

let tmOfConstr (t : Constr.t) : Ast0.term tm =
  Plugin_core.with_env_evm (fun env _ -> tmReturn (of_constr env t))

let tmOfMib (t : Plugin_core.mutual_inductive_body) : Ast0.mutual_inductive_body tm =
  Plugin_core.with_env_evm (fun env _ -> tmReturn (of_mib env t))

let tmOfConstantEntry (t : Plugin_core.constant_entry) : Ast0.constant_entry tm =
  Plugin_core.with_env_evm (fun env _ -> tmReturn (of_constant_entry env t))

let rec interp_tm (t : 'a coq_TM) : 'a tm =
  match t with
  | Coq_tmReturn x -> tmReturn x
  | Coq_tmBind (c, k) -> tmBind (interp_tm c) (fun x -> interp_tm (k x))
  | Coq_tmPrint t -> Obj.magic (tmPrint (to_constr t))
  | Coq_tmMsg msg -> Obj.magic (tmMsg (to_string msg))
  | Coq_tmFail err -> tmFail (to_string err)
  | Coq_tmEval (r,t) ->
    tmBind (tmEval (to_reduction_strategy r) (to_constr t))
           (fun x -> Obj.magic (tmOfConstr x))
  | Coq_tmDefinition (nm, typ, trm) ->
    let typ =
      match typ with
        None -> None
      | Some typ -> Some (to_constr typ)
    in
    tmMap (fun x -> Obj.magic (of_kername x))
          (tmDefinition (to_ident nm) typ (to_constr trm))
  | Coq_tmAxiom (nm, typ) ->
    tmMap (fun x -> Obj.magic (of_kername x))
          (tmAxiom (to_ident nm) (to_constr typ))
  | Coq_tmLemma (nm, typ) ->
    tmMap (fun x -> Obj.magic (of_kername x))
          (tmLemma (to_ident nm) (to_constr typ))
  | Coq_tmFreshName nm ->
    tmMap (fun x -> Obj.magic (of_ident x))
          (tmFreshName (to_ident nm))
  | Coq_tmAbout id ->
    tmMap (function
             None -> Obj.magic None
           | Some gr -> Obj.magic (Some (of_global_reference gr)))
          (tmAbout (to_qualid id))
  | Coq_tmCurrentModPath ->
    tmMap (fun mp -> Obj.magic (of_string (Names.ModPath.to_string mp)))
          tmCurrentModPath
  | Coq_tmQuoteInductive kn ->
    tmMap (function
             None -> Obj.magic None
           | Some mib -> Obj.magic (tmMap (fun x -> Some x) (tmOfMib mib)))
          (tmQuoteInductive (to_kername kn))
  | Coq_tmQuoteUniverses ->
    tmMap (fun x -> failwith "tmQuoteUniverses") tmQuoteUniverses
  | Coq_tmQuoteConstant (kn, b) ->
    tmMap (fun x -> Obj.magic (tmOfConstantEntry x))
          (tmQuoteConstant (to_kername kn) b)
  | Coq_tmInductive i ->
    tmMap (fun _ -> Obj.magic ()) (tmInductive (to_mie i))
  | Coq_tmExistingInstance k ->
    Obj.magic (tmExistingInstance (to_kername k))
  | Coq_tmInferInstance t ->
    tmBind (tmInferInstance (to_constr t))
      (function
          None -> Obj.magic None
        | Some inst -> Obj.magic (tmMap (fun x -> Some x) (tmOfConstr inst)))

let run_vernac (c : 'a coq_TM) : unit =
  Plugin_core.run_vernac (interp_tm (Obj.magic c))
