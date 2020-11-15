open Names
open Entries
open Declarations
open Pp

open Tm_util
open Reification

let cast_prop = ref (false)

(* whether Set Template Cast Propositions is on, as needed for erasure in Certicoq *)
let is_cast_prop () = !cast_prop


let toDecl (old: Name.t Context.binder_annot * ((Constr.constr) option) * Constr.constr) : Constr.rel_declaration =
  let (name,value,typ) = old in
  match value with
  | Some value -> Context.Rel.Declaration.LocalDef (name,value,typ)
  | None -> Context.Rel.Declaration.LocalAssum (name,typ)

let getType env (t:Constr.t) : Constr.t =
    EConstr.to_constr Evd.empty (Retyping.get_type_of env Evd.empty (EConstr.of_constr t))

(* TODO: remove? *)
let opt_hnf_ctor_types = ref false

let hnf_type env ty =
  let rec hnf_type continue ty =
    match Constr.kind ty with
      Constr.Prod (n,t,b) -> Constr.mkProd (n,t,hnf_type true b)
    | Constr.LetIn _
      | Constr.Cast _
      | Constr.App _ when continue ->
       hnf_type false (Reduction.whd_all env ty)
    | _ -> ty
  in
  hnf_type true ty



module type BaseQuoter =
sig
  include Reification

  val mkRel : quoted_int -> t
  val mkVar : quoted_ident -> t
  val mkEvar : quoted_int -> t array -> t
  val mkSort : quoted_sort -> t
  val mkCast : t -> quoted_cast_kind -> t -> t
  val mkProd : quoted_aname -> t -> t -> t
  val mkLambda : quoted_aname -> t -> t -> t
  val mkLetIn : quoted_aname -> t -> t -> t -> t
  val mkApp : t -> t array -> t
  val mkConst : quoted_kernel_name -> quoted_univ_instance -> t
  val mkInd : quoted_inductive -> quoted_univ_instance -> t
  val mkConstruct : quoted_inductive * quoted_int -> quoted_univ_instance -> t
  val mkCase : (quoted_inductive * quoted_int * quoted_relevance) -> quoted_int list -> t -> t -> t list -> t
  val mkProj : quoted_proj -> t -> t
  val mkFix : (quoted_int array * quoted_int) * (quoted_aname array * t array * t array) -> t
  val mkCoFix : quoted_int * (quoted_aname array * t array * t array) -> t

  val mkBindAnn : quoted_name -> quoted_relevance -> quoted_aname
  val mkName : quoted_ident -> quoted_name
  val mkAnon : unit -> quoted_name

  val quote_ident : Id.t -> quoted_ident
  val quote_name : Name.t -> quoted_name
  val quote_aname : Name.t Context.binder_annot -> quoted_aname
  val quote_relevance : Sorts.relevance -> quoted_relevance
  val quote_int : int -> quoted_int
  val quote_bool : bool -> quoted_bool
  val quote_sort : Sorts.t -> quoted_sort
  val quote_sort_family : Sorts.family -> quoted_sort_family
  val quote_cast_kind : Constr.cast_kind -> quoted_cast_kind
  val quote_kn : KerName.t -> quoted_kernel_name
  val quote_inductive : quoted_kernel_name * quoted_int -> quoted_inductive
  val quote_proj : quoted_inductive -> quoted_int -> quoted_int -> quoted_proj

  val quote_constraint_type : Univ.constraint_type -> quoted_constraint_type
  val quote_univ_constraint : Univ.univ_constraint -> quoted_univ_constraint
  val quote_univ_instance : Univ.Instance.t -> quoted_univ_instance
  val quote_univ_constraints : Univ.Constraint.t -> quoted_univ_constraints
  val quote_univ_context : Univ.UContext.t -> quoted_univ_context
  val quote_univ_contextset : Univ.ContextSet.t -> quoted_univ_contextset
  val quote_variance : Univ.Variance.t -> quoted_variance
  val quote_abstract_univ_context : Univ.AUContext.t -> quoted_abstract_univ_context

  val mkMonomorphic_entry : quoted_univ_contextset -> quoted_universes_entry
  val mkPolymorphic_entry : quoted_name list -> quoted_univ_context -> quoted_universes_entry

  val mkMonomorphic_ctx : quoted_univ_contextset -> quoted_universes_decl
  val mkPolymorphic_ctx : quoted_abstract_univ_context -> quoted_universes_decl

  val quote_mind_finiteness : Declarations.recursivity_kind -> quoted_mind_finiteness
  val quote_mutual_inductive_entry :
    quoted_mind_finiteness * quoted_context (* params *) * quoted_ind_entry list *
    quoted_universes_entry * quoted_variance list option ->
    quoted_mind_entry

  val quote_definition_entry : t option -> t -> quoted_universes_entry -> quoted_definition_entry
  val quote_parameter_entry : t -> quoted_universes_entry -> quoted_parameter_entry
  val quote_constant_entry : (quoted_definition_entry, quoted_parameter_entry) sum -> quoted_constant_entry

  (* val quote_entry : (quoted_constant_entry, quoted_mind_entry) sum option > quoted_entry *)

  val quote_context_decl : quoted_aname -> t option -> t -> quoted_context_decl
  val quote_context : quoted_context_decl list -> quoted_context

  val mk_one_inductive_body : quoted_ident * t (* ind type *) * quoted_sort_family
                                 * (quoted_ident * t (* constr type *) * quoted_int) list
                                 * (quoted_ident * t (* projection type *)) list
                                 * quoted_relevance 
                                 -> quoted_one_inductive_body

  val mk_mutual_inductive_body :
    quoted_mind_finiteness
    -> quoted_int (* number of params (no lets) *)
    -> quoted_context (* parameters context with lets *)
    -> quoted_one_inductive_body list
    -> quoted_universes_decl
    -> quoted_variance list option
    -> quoted_mutual_inductive_body

  val mk_constant_body : t (* type *) -> t option (* body *) -> quoted_universes_decl -> quoted_constant_body

  val mk_inductive_decl : quoted_mutual_inductive_body -> quoted_global_decl

  val mk_constant_decl : quoted_constant_body -> quoted_global_decl

  val empty_global_declarations : unit -> quoted_global_env
  val add_global_decl : quoted_kernel_name -> quoted_global_decl -> quoted_global_env -> quoted_global_env

  val mk_program : quoted_global_env -> t -> quoted_program
end



module Quoter (Q : BaseQuoter) =
struct

  let push_rel decl (in_prop, env) = (in_prop, Environ.push_rel decl env)
  let push_rel_context ctx (in_prop, env) = (in_prop, Environ.push_rel_context ctx env)

  let get_abstract_inductive_universes iu =
    match iu with
    | Declarations.Monomorphic ctx -> Univ.ContextSet.to_context ctx
    | Polymorphic ctx -> Univ.AUContext.repr ctx

  let quote_universes_entry = function
    | Monomorphic_entry ctx -> Q.mkMonomorphic_entry (Q.quote_univ_contextset ctx)
    | Polymorphic_entry (names, ctx) -> 
      Q.mkPolymorphic_entry (CArray.map_to_list Q.quote_name names) (Q.quote_univ_context ctx)

  let quote_universes_decl = function
    | Monomorphic ctx -> Q.mkMonomorphic_ctx (Q.quote_univ_contextset ctx)
    | Polymorphic ctx -> Q.mkPolymorphic_ctx (Q.quote_abstract_univ_context ctx)

  let quote_inductive' (ind, i) : Q.quoted_inductive =
    Q.quote_inductive (Q.quote_kn (Names.MutInd.canonical ind), Q.quote_int i)
    
  let quote_rel_decl quote_term acc env = function
      | Context.Rel.Declaration.LocalAssum (na, t) ->
        let t', acc = quote_term acc env t in
        (Q.quote_context_decl (Q.quote_aname na) None t', acc)
      | Context.Rel.Declaration.LocalDef (na, b, t) ->
        let b', acc = quote_term acc env b in
        let t', acc = quote_term acc env t in
        (Q.quote_context_decl (Q.quote_aname na) (Some b') t', acc)
  
  let quote_rel_context quote_term acc env ctx =
      let decls, env, acc =
        List.fold_right (fun decl (ds, env, acc) ->
            let x, acc = quote_rel_decl quote_term acc env decl in
            (x :: ds, push_rel decl env, acc))
          ctx ([],env,acc) in
      Q.quote_context decls, acc

  let quote_binder b = 
    Q.quote_aname b

  let quote_term_remember
      (add_constant : KerName.t -> 'a -> 'a)
      (add_inductive : Names.inductive -> 'a -> 'a) =
    let rec quote_term (acc : 'a) env trm =
      let aux acc env trm =
      match Constr.kind trm with
	    | Constr.Rel i -> (Q.mkRel (Q.quote_int (i - 1)), acc)
      | Constr.Var v -> (Q.mkVar (Q.quote_ident v), acc)
      | Constr.Evar (n,args) ->
	      let (acc,args') =
      	  CArray.fold_left_map (fun acc x ->
	        let (x,acc) = quote_term acc env x in acc,x)
          acc args 
        in
         (Q.mkEvar (Q.quote_int (Evar.repr n)) args', acc)
      | Constr.Sort s -> (Q.mkSort (Q.quote_sort s), acc)
      | Constr.Cast (c,k,t) ->
	      let (c',acc) = quote_term acc env c in
	      let (t',acc) = quote_term acc env t in
        let k' = Q.quote_cast_kind k in
        (Q.mkCast c' k' t', acc)

      | Constr.Prod (n,t,b) ->
	      let (t',acc) = quote_term acc env t in
        let env = push_rel (toDecl (n, None, t)) env in
        let (b',acc) = quote_term acc env b in
        (Q.mkProd (Q.quote_aname n) t' b', acc)

      | Constr.Lambda (n,t,b) ->
	      let (t',acc) = quote_term acc env t in
              let (b',acc) = quote_term acc (push_rel (toDecl (n, None, t)) env) b in
        (Q.mkLambda (Q.quote_aname n) t' b', acc)

      | Constr.LetIn (n,e,t,b) ->
	      let (e',acc) = quote_term acc env e in
	      let (t',acc) = quote_term acc env t in
	      let (b',acc) = quote_term acc (push_rel (toDecl (n, Some e, t)) env) b in
      	(Q.mkLetIn (Q.quote_aname n) e' t' b', acc)

      | Constr.App (f,xs) ->
        let (f',acc) = quote_term acc env f in
        let (acc,xs') =
          CArray.fold_left_map (fun acc x ->
            let (x,acc) = quote_term acc env x in acc,x)
            acc xs in
        (Q.mkApp f' xs', acc)

      | Constr.Const (c,pu) ->
        let kn = Constant.canonical c in
	(Q.mkConst (Q.quote_kn kn) (Q.quote_univ_instance pu), add_constant kn acc)

      | Constr.Construct ((mind,c),pu) ->
         (Q.mkConstruct (quote_inductive' mind, Q.quote_int (c - 1)) (Q.quote_univ_instance pu),
          add_inductive mind acc)

      | Constr.Ind (mind,pu) ->
         (Q.mkInd (quote_inductive' mind) (Q.quote_univ_instance pu),
          add_inductive mind acc)

      | Constr.Case (ci,typeInfo,discriminant,e) ->
         let ind = Q.quote_inductive (Q.quote_kn (Names.MutInd.canonical (fst ci.Constr.ci_ind)),
                                      Q.quote_int (snd ci.Constr.ci_ind)) in
         let npar = Q.quote_int ci.Constr.ci_npar in
         let (qtypeInfo,acc) = quote_term acc env typeInfo in
	       let (qdiscriminant,acc) = quote_term acc env discriminant in
         let (branches,nargs,acc) =
           CArray.fold_left2 (fun (xs,nargs,acc) x narg ->
               let (x,acc) = quote_term acc env x in
               let narg = Q.quote_int narg in
               (x :: xs, narg :: nargs, acc))
             ([],[],acc) e ci.Constr.ci_cstr_nargs in
         let q_relevance = Q.quote_relevance ci.Constr.ci_relevance in
         (Q.mkCase (ind, npar, q_relevance) (List.rev nargs) qtypeInfo qdiscriminant (List.rev branches), acc)

      | Constr.Fix fp -> quote_fixpoint acc env fp
      | Constr.CoFix fp -> quote_cofixpoint acc env fp
      | Constr.Proj (p,c) ->
         let ind = quote_inductive' (Projection.inductive p) in
         let pars = Q.quote_int (Projection.npars p) in
         let arg  = Q.quote_int (Projection.arg p)   in
         let p' = Q.quote_proj ind pars arg in
         let t', acc = quote_term acc env c in
         (Q.mkProj p' t', add_inductive (Projection.inductive p) acc)
      | Constr.Meta _ -> failwith "Meta not supported by TemplateCoq"
      | Constr.Int _ -> failwith "Native integers not supported by TemplateCoq"
      | Constr.Float _ -> failwith "Native floating point numbers not supported by TemplateCoq"
      in
      let in_prop, env' = env in
      if is_cast_prop () && not in_prop then
        let ty =
          let trm = EConstr.of_constr trm in
          try Retyping.get_type_of env' Evd.empty trm
          with e ->
            Feedback.msg_debug (str"Anomaly trying to get the type of: " ++
                                Printer.pr_econstr_env (snd env) Evd.empty trm);
            raise e
        in
        let sf =
          try Retyping.get_sort_family_of env' Evd.empty ty
          with e ->
            Feedback.msg_debug (str"Anomaly trying to get the sort of: " ++
                                Printer.pr_econstr_env (snd env) Evd.empty ty);
            raise e
        in
        if sf == Term.InProp then
          aux acc (true, env')
              (Constr.mkCast (trm, Constr.DEFAULTcast,
                            Constr.mkCast (EConstr.to_constr Evd.empty ty, Constr.DEFAULTcast, Constr.mkProp)))
        else aux acc env trm
      else aux acc env trm
    and quote_recdecl (acc : 'a) env b (ns,ts,ds) =
      let ctxt =
        CArray.map2_i (fun i na t -> (Context.Rel.Declaration.LocalAssum (na, Vars.lift i t))) ns ts in
      let envfix = push_rel_context (CArray.rev_to_list ctxt) env in
      let ns' = Array.map quote_binder ns in
      let b' = Q.quote_int b in
      let acc, ts' =
        CArray.fold_left_map (fun acc t -> let x,acc = quote_term acc env t in acc, x) acc ts in
      let acc, ds' =
        CArray.fold_left_map (fun acc t -> let x,y = quote_term acc envfix t in y, x) acc ds in
      ((b',(ns',ts',ds')), acc)
    and quote_fixpoint acc env ((a,b),decl) =
      let a' = Array.map Q.quote_int a in
      let (b',decl'),acc = quote_recdecl acc env b decl in
      (Q.mkFix ((a',b'),decl'), acc)
    and quote_cofixpoint acc env (a,decl) =
      let (a',decl'),acc = quote_recdecl acc env a decl in
      (Q.mkCoFix (a',decl'), acc)
    and quote_minductive_type (acc : 'a) env (t : MutInd.t) =
      let mib = Environ.lookup_mind t (snd env) in
      let uctx = get_abstract_inductive_universes mib.Declarations.mind_universes in
      let inst = Univ.UContext.instance uctx in
      let indtys =
        (CArray.map_to_list (fun oib ->
           let ty = Inductive.type_of_inductive (snd env) ((mib,oib),inst) in
           (Context.Rel.Declaration.LocalAssum (Context.annotR (Names.Name oib.mind_typename), ty))) mib.mind_packets)
      in
      let envind = push_rel_context (List.rev indtys) env in
      let ref_name = Q.quote_kn (MutInd.canonical t) in
      let (ls,acc) =
	List.fold_left (fun (ls,acc) oib ->
	  let named_ctors =
	    CList.combine3
	      (Array.to_list oib.mind_consnames)
	      (Array.to_list oib.mind_user_lc)
	      (Array.to_list oib.mind_consnrealargs)
	  in
          let indty = Inductive.type_of_inductive (snd env) ((mib,oib),inst) in
          let indty, acc = quote_term acc env indty in
	  let (reified_ctors,acc) =
	    List.fold_left (fun (ls,acc) (nm,ty,ar) ->
	      debug (fun () -> Pp.(str "opt_hnf_ctor_types:" ++ spc () ++
                            bool !opt_hnf_ctor_types)) ;
	      let ty = if !opt_hnf_ctor_types then hnf_type (snd envind) ty else ty in
	      let (ty,acc) = quote_term acc envind ty in
	      ((Q.quote_ident nm, ty, Q.quote_int ar) :: ls, acc))
	      ([],acc) named_ctors
	  in
          let projs, acc =
            match mib.Declarations.mind_record with
            | PrimRecord [|id, csts, relevance, ps|] ->  (* TODO handle mutual records *)
               let ctxwolet = Termops.smash_rel_context mib.mind_params_ctxt in
               let indty = Constr.mkApp (Constr.mkIndU ((t,0),inst),
                                       Context.Rel.to_extended_vect Constr.mkRel 0 ctxwolet) in
               let indbinder = Context.Rel.Declaration.LocalAssum (Context.annotR (Names.Name id),indty) in
               let envpars = push_rel_context (indbinder :: ctxwolet) env in
               let ps, acc = CArray.fold_right2 (fun cst pb (ls,acc) ->
                 let (ty, acc) = quote_term acc envpars pb in
                 let na = Q.quote_ident (Names.Label.to_id cst) in
                 ((na, ty) :: ls, acc)) csts ps ([],acc)
               in ps, acc
            | _ -> [], acc
          in
          let sf = Q.quote_sort_family oib.Declarations.mind_kelim in
	  (Q.quote_ident oib.mind_typename, indty, sf, (List.rev reified_ctors), projs, Q.quote_relevance oib.mind_relevance) :: ls, acc)
	  ([],acc) (Array.to_list mib.mind_packets)
      in
      let nparams = Q.quote_int mib.Declarations.mind_nparams in
      let paramsctx, acc = quote_rel_context quote_term acc env mib.Declarations.mind_params_ctxt in
      let uctx = quote_universes_decl mib.Declarations.mind_universes in
      let var = Option.map (CArray.map_to_list Q.quote_variance) mib.Declarations.mind_variance in
      let bodies = List.map Q.mk_one_inductive_body (List.rev ls) in
      let finite = Q.quote_mind_finiteness mib.Declarations.mind_finite in
      let mind = Q.mk_mutual_inductive_body finite nparams paramsctx bodies uctx var in
      ref_name, Q.mk_inductive_decl mind, acc
    in ((fun acc env -> quote_term acc (false, env)),
        (fun acc env -> quote_minductive_type acc (false, env)))

  let quote_term env trm =
    let (fn,_) = quote_term_remember (fun _ () -> ()) (fun _ () -> ()) in
    fst (fn () env trm)

  let quote_mind_decl env trm =
    let (_,fn) = quote_term_remember (fun _ () -> ()) (fun _ () -> ()) in
    let (_, indd, _) = fn () env trm in indd

  type defType =
    Ind of Names.inductive
  | Const of KerName.t

  let quote_term_rec bypass env trm =
    let visited_terms = ref Names.KNset.empty in
    let visited_types = ref Mindset.empty in
    let constants = ref [] in
    let add quote_term quote_type trm acc =
      match trm with
      | Ind (mi,idx) ->
	let t = mi in
	if Mindset.mem t !visited_types then ()
	else
	  begin
	    visited_types := Mindset.add t !visited_types ;
	    let (kn,d,acc) =
              try quote_type acc env mi
              with e ->
                Feedback.msg_debug (str"Exception raised while checking " ++ MutInd.print mi);
                raise e
            in
	    constants := (kn,d) :: !constants
	  end
      | Const kn ->
	if Names.KNset.mem kn !visited_terms then ()
	else
	  begin
	    visited_terms := Names.KNset.add kn !visited_terms ;
      let c = Names.Constant.make kn kn in
	    let cd = Environ.lookup_constant c env in
      let body = match cd.const_body with
        | Undef _ -> None
        | Primitive _ -> CErrors.user_err Pp.(str "Primitives are unsupported by TemplateCoq")
	      | Def cs -> Some (Mod_subst.force_constr cs)
	      | OpaqueDef lc ->
          if bypass then
          let c, univs = Opaqueproof.force_proof Library.indirect_accessor (Environ.opaque_tables env) lc in
          let () = match univs with
          | Opaqueproof.PrivateMonomorphic () -> ()
          | Opaqueproof.PrivatePolymorphic (n, csts) -> if not (Univ.ContextSet.is_empty csts && Int.equal n 0) then 
            CErrors.user_err Pp.(str "Private polymorphic universes not supported by TemplateCoq")
          in Some c
          else None
        in
        let tm, acc =
          match body with
          | None -> None, acc
          | Some tm -> try let (tm, acc) = quote_term acc (Global.env ()) tm in
                            (Some tm, acc)
                        with e ->
                          Feedback.msg_debug (str"Exception raised while checking body of " ++ KerName.print kn);
              raise e
        in
        let uctx = quote_universes_decl cd.const_universes in
        let ty, acc =
          let ty = cd.const_type
                      (*CHANGE :  template polymorphism for definitions was removed.
                      See: https://github.com/coq/coq/commit/d9530632321c0b470ece6337cda2cf54d02d61eb *)
            (* match cd.const_type with
        * | RegularArity ty -> ty
        * | TemplateArity (ctx,ar) ->
              *    Constr.it_mkProd_or_LetIn (Constr.mkSort (Sorts.Type ar.template_level)) ctx *)
          in
          (try quote_term acc (Global.env ()) ty
            with e ->
              Feedback.msg_debug (str"Exception raised while checking type of " ++ KerName.print kn);
              raise e)
        in
        let cst_bdy = Q.mk_constant_body ty tm uctx in
        let decl = Q.mk_constant_decl cst_bdy in            
        constants := (Q.quote_kn kn, decl) :: !constants
	  end
    in
    let (quote_rem,quote_typ) =
      let a = ref (fun _ _ _ -> assert false) in
      let b = ref (fun _ _ _ -> assert false) in
      let (x,y) =
	quote_term_remember (fun x () -> add !a !b (Const x) ())
	                    (fun y () -> add !a !b (Ind y) ())
      in
      a := x ;
      b := y ;
      (x,y)
    in
    let (tm, _) = quote_rem () env trm in
    let decls =  List.fold_right (fun (kn, d) acc -> Q.add_global_decl kn d acc)  !constants (Q.empty_global_declarations ()) in
    Q.mk_program decls tm

  let quote_rel_context env ctx = 
    fst (quote_rel_context (fun acc env t -> (quote_term (snd env) t, acc)) () ((), env) ctx)

  let quote_one_ind envA envC (mi:Entries.one_inductive_entry) =
    let iname = Q.quote_ident mi.mind_entry_typename  in
    let arity = quote_term envA mi.mind_entry_arity in
    let templatePoly = Q.quote_bool mi.mind_entry_template in
    let consnames = List.map Q.quote_ident (mi.mind_entry_consnames) in
    let constypes = List.map (quote_term envC) (mi.mind_entry_lc) in
    (iname, arity, templatePoly, consnames, constypes)

  let quote_mind_params env (params: Constr.rel_context) =
    let qparams = quote_rel_context env params in
    (Environ.push_rel_context params env, qparams)

  let mind_params_as_types ((env,t):Environ.env*Constr.t) (params:Constr.rel_context) :
        Environ.env*Constr.t =
    (env, Term.it_mkProd_or_LetIn t params)

  (* CHANGE: this is the only way (ugly) I found to construct [absrt_info] with empty fields,
since  [absrt_info] is a private type *)
  let empty_segment = Lib.section_segment_of_reference (Names.GlobRef.VarRef (Names.Id.of_string "blah"))
(*
  let quote_mut_ind env (mi:Declarations.mutual_inductive_body) =
   let t= Discharge.process_inductive empty_segment (Names.Cmap.empty,Names.Mindmap.empty) mi in
    let mf = Q.quote_mind_finiteness t.mind_entry_finite in
    let mp = (snd (quote_mind_params env (t.mind_entry_params))) in
    (* before quoting the types of constructors, we need to enrich the environment with the inductives *)
    let one_arities =
      List.map
        (fun x -> (x.mind_entry_typename,
                   snd (mind_params_as_types (env,x.mind_entry_arity) (t.mind_entry_params))))
        t.mind_entry_inds in
    (* env for quoting constructors of inductives. First push inductices, then params *)
    let envC = List.fold_left (fun env p -> Environ.push_rel (toDecl (Context.annotR (Names.Name (fst p)), None, snd p)) env) env (one_arities) in
    let envC = Environ.push_rel_context t.mind_entry_params envC in
    (* env for quoting arities of inductives -- just push the params *)
    let envA = Environ.push_rel_context t.mind_entry_params env in
    let is = List.map (quote_one_ind envA envC) t.mind_entry_inds in
    let uctx = quote_universes_entry t.mind_entry_universes in
    let variance = Option.map (CArray.map_to_list Q.quote_variance) t.mind_entry_variance in
    Q.quote_mutual_inductive_entry (mf, mp, is, uctx, variance) *)

  let quote_constant_body_aux bypass env evm (cd : Opaqueproof.opaque constant_body) =
    let ty = quote_term env cd.const_type in
    let body =
      match cd.const_body with
      | Undef _ -> None
      | Def cs -> Some (quote_term env (Mod_subst.force_constr cs))
      | OpaqueDef cs ->
        if bypass
        then Some (quote_term env (fst (Opaqueproof.force_proof Library.indirect_accessor (Environ.opaque_tables env) cs)))
        else None
      | Primitive _ -> failwith "Primitive types not supported by TemplateCoq"
    in
    (ty, body)

  let quote_constant_body bypass env evm cd =
    let ty, body = quote_constant_body_aux bypass env evm cd in
    Q.mk_constant_body ty body (quote_universes_decl cd.const_universes)

  let quote_constant_entry bypass env evm cd =
    let (ty, body) = quote_constant_body_aux bypass env evm cd in
    let uctx = match cd.const_universes with
      | Polymorphic auctx -> 
        Polymorphic_entry (Univ.AUContext.names auctx, Univ.AUContext.repr auctx)
      | Monomorphic ctx -> Monomorphic_entry ctx
    in
    let univs = quote_universes_entry uctx in
    match body with
    | None -> Q.quote_constant_entry (Right (Q.quote_parameter_entry ty univs))
    | Some body -> Q.quote_constant_entry (Left (Q.quote_definition_entry (Some ty) body univs))

  (* let quote_entry_aux bypass env evm (name:string) =
    let (dp, nm) = split_name name in
    match Nametab.locate (Libnames.make_qualid dp nm) with
    | Globnames.ConstRef c ->
      let cd = Environ.lookup_constant c env in
      (*CHANGE :  template polymorphism for definitions was removed.
                  See: https://github.com/coq/coq/commit/d9530632321c0b470ece6337cda2cf54d02d61eb *)
      Q.quote_entry (Left (quote_constant_entry bypass env evm cd))
    | Globnames.IndRef ni ->
      let c = Environ.lookup_mind (fst ni) env in (* FIX: For efficienctly, we should also export (snd ni)*)
      let miq = quote_mut_ind env c in
      Q.quote_entry (Right miq)
    | Globnames.ConstructRef _ -> raise Not_found (* FIX?: return the enclusing mutual inductive *)
    | Globnames.VarRef _ -> raise Not_found


  let quote_entry_of bypass env evm t =
    try Some (quote_entry_aux bypass env evm t)
    with Not_found -> None *)

  let quote_ugraph (g : UGraph.t) =
    Q.quote_univ_constraints (fst (UGraph.constraints_of_universes g))
end
