open CErrors
open Univ
open Entries
open Names
open Redops
open Genredexpr
open Pp (* this adds the ++ to the current scope *)

open Tm_util
open Quoter
open Denote
open Constr_quoter
open Template_monad
open Constr_denoter

open CoqLiveDenoter
open TemplateCoqQuoter


let unquote_reduction_strategy env evm trm (* of type reductionStrategy *) : Redexpr.red_expr =
  let (trm, args) = app_full trm [] in
  (* from g_tactic.ml4 *)
  let default_flags = Redops.make_red_flag [FBeta;FMatch;FFix;FCofix;FZeta;FDeltaBut []] in
  if constr_equall trm tcbv then Cbv default_flags
  else if constr_equall trm tcbn then Cbn default_flags
  else if constr_equall trm thnf then Hnf
  else if constr_equall trm tall then Cbv all_flags
  else if constr_equall trm tlazy then Lazy all_flags
  else if constr_equall trm tunfold then
    match args with
    | name (* to unfold *) :: _ ->
       let name = reduce_all env evm name in
       let name = unquote_kn name in
       (try Unfold [Locus.AllOccurrences, Tacred.evaluable_of_global_reference env (Nametab.locate name)]
        with
        | _ -> CErrors.user_err (str "Constant not found or not a constant: " ++ Libnames.pr_qualid name))
    | _ -> bad_term_verb trm "unquote_reduction_strategy"
  else not_supported_verb trm "unquote_reduction_strategy"

let denote_local_entry evm trm =
  let (h,args) = app_full trm [] in
  match args with
    x :: [] ->
    if constr_equall h tLocalDef then
      let evm, x = denote_term evm x in
      evm, Entries.LocalDefEntry x
    else if  constr_equall h tLocalAssum then
      let evm, x = denote_term evm x in
      evm, Entries.LocalAssumEntry x
    else
      not_supported_verb trm "denote_local_entry"
  | _ -> bad_term_verb trm "denote_local_entry"


let denote_mind_entry_finite trm =
  let (h,args) = app_full trm [] in
  match args with
    [] ->
    if constr_equall h cFinite then Declarations.Finite
    else if  constr_equall h cCoFinite then Declarations.CoFinite
    else if  constr_equall h cBiFinite then Declarations.BiFinite
    else not_supported_verb trm "denote_mind_entry_finite"
  | _ -> bad_term_verb trm "denote_mind_entry_finite"


let unquote_map_option f trm =
  let (h,args) = app_full trm [] in
  if constr_equall h cSome then
    match args with
      _ :: x :: [] -> Some (f x)
    | _ -> bad_term trm
  else if constr_equall h cNone then
    match args with
      _ :: [] -> None
    | _ -> bad_term trm
  else
    not_supported_verb trm "unquote_map_option"

let unquote_option = unquote_map_option (fun x -> x)



let unquote_constraint_type trm (* of type constraint_type *) : constraint_type =
  let (h,args) = app_full trm [] in
  match args with
    [] ->
    if constr_equall h tunivLt then Univ.Lt
    else if constr_equall h tunivLe then Univ.Le
    else if constr_equall h tunivEq then Univ.Eq
    else not_supported_verb trm "unquote_constraint_type"
  | _ -> bad_term_verb trm "unquote_constraint_type"


let unquote_univ_constraint evm c (* of type univ_constraint *) : _ * univ_constraint =
  let c, l2 = unquote_pair c in
  let l1, c = unquote_pair c in
  let evm, l1 = unquote_level evm l1 in
  let evm, l2 = unquote_level evm l2 in
  let c = unquote_constraint_type c in
  evm, (l1, c, l2)


(* set given by MSets.MSetWeakList.Make *)
let unquote_set trm =
  let (h, args) = app_full trm [] in
  (* h supposed to be Mkt, the constructor of the record *)
  match args with
  | list :: ok :: [] -> unquote_list list
  | _ -> not_supported_verb trm "unquote_set"


let unquote_constraints evm c (* of type constraints *) : _ * Constraint.t =
  let c = unquote_set c in
  List.fold_left (fun (evm, set) c -> let evm, c = unquote_univ_constraint evm c in evm, Constraint.add c set)
                 (evm, Constraint.empty) c


let denote_variance trm (* of type Variance *) : Variance.t =
  if constr_equall trm cIrrelevant then Variance.Irrelevant
  else if constr_equall trm cCovariant then Variance.Covariant
  else if constr_equall trm cInvariant then Variance.Invariant
  else not_supported_verb trm "denote_variance"


let denote_ucontext evm trm (* of type UContext.t *) : _ * UContext.t =
  let i, c = unquote_pair trm in
  let evm, i = unquote_universe_instance evm i in
  let evm, c = unquote_constraints evm c in
  evm, Univ.UContext.make (i, c)

let unquote_levelset evm c (* of type LevelSet.t *) : _ * LSet.t =
  let c = unquote_set c in
  List.fold_left (fun (evm, set) c -> let evm, c = unquote_level evm c in evm, LSet.add c set)
                 (evm, LSet.empty) c

let denote_ucontextset evm trm (* of type ContextSet.t *) : _ * ContextSet.t =
  let i, c = unquote_pair trm in
  let evm, i = unquote_levelset evm i in
  let evm, c = unquote_constraints evm c in
  evm, (i, c)

let denote_aucontext evm trm (* of type AUContext.t *) : _ * AUContext.t =
  let i, c = unquote_pair trm in
  let l = unquote_list i in
  let l = List.mapi (fun i l -> Level.var i) l in
  let l = Instance.of_array (Array.of_list l) in
  let evm, c = unquote_constraints evm c in
  evm, snd (abstract_universes (UContext.make (l, c)))


let denote_cumulativity_info evm trm (* of type CumulativityInfo *) : _ * CumulativityInfo.t =
  let uctx, variances = unquote_pair trm in
  let evm, uctx = denote_aucontext evm uctx in
  let uctx = AUContext.repr uctx in
  let variances = List.map denote_variance (unquote_list variances) in
  evm, CumulativityInfo.make (uctx, Array.of_list variances)

(* todo : stick to Coq implem *)
type universe_context_type =
  | Monomorphic_uctx of Univ.ContextSet.t
  | Polymorphic_uctx of Univ.AUContext.t
  | Cumulative_uctx of Univ.CumulativityInfo.t

let to_entry_inductive_universes = function
  | Monomorphic_uctx ctx -> Monomorphic_ind_entry ctx
  | Polymorphic_uctx ctx -> Polymorphic_ind_entry (AUContext.repr ctx)
  | Cumulative_uctx ctx -> Cumulative_ind_entry ctx

let denote_universes_decl evm trm (* of type universes_decl *) : _ * universe_context_type =
  let (h, args) = app_full trm [] in
  match args with
  | ctx :: [] -> if constr_equall h cMonomorphic_ctx then
                   let evm, ctx = denote_ucontextset evm ctx in
                   evm, Monomorphic_uctx ctx
                 else if constr_equall h cPolymorphic_ctx then
                   let evm, ctx = denote_aucontext evm ctx in
                   evm, Polymorphic_uctx ctx
                 else if constr_equall h cCumulative_ctx then
                   let evm, ctx = denote_cumulativity_info evm ctx in
                   evm, Cumulative_uctx ctx
                 else
                   not_supported_verb trm "denote_universe_context"
  | _ -> bad_term_verb trm "denote_universe_context"



let unquote_one_inductive_entry evm trm (* of type one_inductive_entry *) : _ * Entries.one_inductive_entry =
  let (h,args) = app_full trm [] in
  if constr_equall h tBuild_one_inductive_entry then
    match args with
    | id::ar::template::cnames::ctms::[] ->
       let id = unquote_ident id in
       let evm, ar = denote_term evm ar in
       let template = unquote_bool template in
       let cnames = List.map unquote_ident (unquote_list cnames) in
       let evm, ctms = map_evm denote_term evm (unquote_list ctms) in
       evm, { mind_entry_typename = id ;
              mind_entry_arity = ar;
              mind_entry_template = template;
              mind_entry_consnames = cnames;
              mind_entry_lc = ctms }
    | _ -> bad_term_verb trm "unquote_one_inductive_entry"
  else
    not_supported_verb trm "unquote_one_inductive_entry"

let map_option f o =
  match o with
  | Some x -> Some (f x)
  | None -> None          
  
let unquote_mutual_inductive_entry evm trm (* of type mutual_inductive_entry *) : _ * Entries.mutual_inductive_entry =
  let (h,args) = app_full trm [] in
  if constr_equall h tBuild_mutual_inductive_entry then
    match args with
    | record::finite::params::inds::univs::priv::[] ->
       let record = map_option (map_option (fun x -> [|x|])) (unquote_map_option (unquote_map_option unquote_ident) record) in
       let finite = denote_mind_entry_finite finite in
       let evm, params = map_evm (fun evm p -> let (l,r) = unquote_pair p in
                                               let evm, e = denote_local_entry evm r in
                                               evm, (unquote_ident l, e))
                                 evm (unquote_list params) in
       let evm, inds = map_evm unquote_one_inductive_entry evm (unquote_list inds) in
       let evm, univs = denote_universes_decl evm univs in
       let priv = unquote_map_option unquote_bool priv in
       evm, { mind_entry_record = record;
              mind_entry_finite = finite;
              mind_entry_params = params;
              mind_entry_inds = inds;
              mind_entry_universes = to_entry_inductive_universes univs;
              mind_entry_private = priv }
    | _ -> bad_term_verb trm "unquote_mutual_inductive_entry"
  else
    not_supported_verb trm "unquote_mutual_inductive_entry"


let declare_inductive (env: Environ.env) (evm: Evd.evar_map) (mind: Constr.t) : unit =
  let mind = reduce_all env evm mind in
  let evm, mind = unquote_mutual_inductive_entry evm mind in
  ignore (ComInductive.declare_mutual_inductive_with_eliminations mind Names.Id.Map.empty [])

let not_in_tactic s =
  CErrors.user_err  (str ("You can not use " ^ s ^ " in a tactic."))

let rec run_template_program_rec ?(intactic=false) (k : Environ.env * Evd.evar_map * Constr.t -> unit) env ((evm, pgm) : Evd.evar_map * Constr.t) : unit =
  let (kind, universes) = next_action env evm pgm in
  match kind with
    TmReturn h ->
    let (evm, _) = Typing.type_of env evm (EConstr.of_constr h) in
    k (env, evm, h)
  | TmBind (a,f) ->
     run_template_program_rec ~intactic:intactic (fun (env, evm, ar) -> run_template_program_rec ~intactic:intactic k env (evm, Constr.mkApp (f, [|ar|]))) env (evm, a)
  | TmVariable (name, typ) ->
    if intactic 
    then not_in_tactic "tmVariable"
    else
      let name = unquote_ident (reduce_all env evm name) in
      let typ = Constrextern.extern_constr true env evm (EConstr.of_constr typ) in
      (if ComAssumption.do_assumptions (Discharge, false, Definitional) Declaremods.NoInline [(false, ([(CAst.make name, None)], typ))] then () else ());
      let env = Global.env() in
      k (env, evm, Lazy.force unit_tt)
  | TmDefinition (opaque,name,s,typ,body) ->
    if intactic
    then not_in_tactic "tmDefinition"
    else
      let name = unquote_ident (reduce_all env evm name) in
      let opaque = unquote_bool (reduce_all env evm opaque) in
      let evm, typ = (match unquote_option s with Some s -> let red = unquote_reduction_strategy env evm s in reduce env evm red typ | None -> evm, typ) in
      let univs =
        if Flags.is_universe_polymorphism () then Polymorphic_const_entry (Evd.to_universe_context evm)
        else Monomorphic_const_entry (Evd.universe_context_set evm) in
      let n = Declare.declare_definition ~kind:Decl_kinds.Definition ~opaque name ~types:typ (body, univs) in
      let env = Global.env () in
      k (env, evm, Constr.mkConst n)
  | TmDefinitionTerm (opaque, name, typ, body) ->
    if intactic
    then not_in_tactic "tmDefinition"
    else
      let name = unquote_ident (reduce_all env evm name) in
      let opaque = unquote_bool (reduce_all env evm opaque) in
      let evm,body = denote_term evm (reduce_all env evm body) in
      let evm,typ =
        match unquote_option typ with
        | None -> (evm, None)
        | Some t ->
          let (evm, t) = denote_term evm (reduce_all env evm t) in
          (evm, Some t)
      in
      let poly = Flags.is_universe_polymorphism () in
      Plugin_core.run (Plugin_core.tmDefinition name ~poly ~opaque typ body) env evm
        (fun env evm res -> k (env, evm, quote_kn res))
  | TmLemmaTerm (name, typ) ->
    let ident = unquote_ident (reduce_all env evm name) in
    let evm,typ = denote_term evm (reduce_all env evm typ) in
    let poly = Flags.is_universe_polymorphism () in
    Plugin_core.run (Plugin_core.tmLemma ident ~poly typ) env evm
      (fun env evm kn -> k (env, evm, quote_kn kn))

  | TmAxiom (name,s,typ) ->
    if intactic
    then not_in_tactic "tmAxiom"
    else
      let name = unquote_ident (reduce_all env evm name) in
      let evm, typ = (match unquote_option s with Some s -> let red = unquote_reduction_strategy env evm s in reduce env evm red typ | None -> evm, typ) in
      let param = Entries.ParameterEntry (None, (typ, Monomorphic_const_entry (Evd.universe_context_set evm)), None) in
      let n = Declare.declare_constant name (param, Decl_kinds.IsDefinition Decl_kinds.Definition) in
      let env = Global.env () in
      k (env, evm, Constr.mkConst n)
  | TmAxiomTerm (name,typ) ->
    if intactic
    then not_in_tactic "tmAxiom"
    else
      let name = unquote_ident (reduce_all env evm name) in
      let evm,typ = denote_term evm (reduce_all env evm typ) in
      let poly = Flags.is_universe_polymorphism () in
      Plugin_core.run (Plugin_core.tmAxiom name ~poly typ) env evm
        (fun a b c -> k (a,b,quote_kn c))

  | TmLemma (name,typ) ->
    let name = reduce_all env evm name in
    let poly = Flags.is_universe_polymorphism () in
    let kind = (Decl_kinds.Global, poly, Decl_kinds.Definition) in
    let hole = CAst.make (Constrexpr.CHole (None, Misctypes.IntroAnonymous, None)) in
    let evm, (c, _) = Constrintern.interp_casted_constr_evars_impls env evm hole (EConstr.of_constr typ) in
    let ident = unquote_ident name in
    Obligations.check_evars env evm;
       let obls, _, c, cty = Obligations.eterm_obligations env ident evm 0 (EConstr.to_constr evm c) typ in
       (* let evm = Evd.minimize_universes evm in *)
       let ctx = Evd.evar_universe_context evm in
       let hook = Lemmas.mk_hook (fun _ gr _ -> let env = Global.env () in
                                                let evm = Evd.from_env env in
                                                let evm, t = Evd.fresh_global env evm gr in k (env, evm, EConstr.to_constr evm t)) in  (* todo better *)
       ignore (Obligations.add_definition ident ~term:c cty ctx ~kind ~hook obls)
    (* let kind = Decl_kinds.(Global, Flags.use_polymorphic_flag (), DefinitionBody Definition) in *)
    (* Lemmas.start_proof (unquote_ident name) kind evm (EConstr.of_constr typ) *)
    (* (Lemmas.mk_hook (fun _ gr -> *)
    (* let evm, t = Evd.fresh_global env evm gr in k (env, evm, t) *)
    (* k (env, evm, unit_tt) *)
    (* )); *)

  | TmQuote (false, trm) ->
    (* user should do the reduction (using tmEval) if they want *)
    let qt = TermReify.quote_term env trm
    in k (env, evm, qt)
  | TmQuote (true, trm) ->
    let qt = TermReify.quote_term_rec env trm in
    k (env, evm, qt)
  | TmQuoteInd (name, strict) ->
       let name = unquote_string (reduce_all env evm name) in
       let (dp, nm) = Quoted.split_name name in
       (match Nametab.locate (Libnames.make_qualid dp nm) with
        | Globnames.IndRef (ind, _) ->
          let _ =
            let kn = Names.KerName.to_string (Names.MutInd.canonical ind) in
            if strict && kn <> name then
              CErrors.user_err (str "strict mode not canonical: \"" ++ str name ++ str "\" <> \"" ++ str kn ++ str "\"")
            else ()
          in
          let t = TermReify.quote_mind_decl env ind in
          let _, args = Constr.destApp t in
          (match args with
           | [|kn; decl|] ->
             k (env, evm, decl)
           | _ -> bad_term_verb t "anomaly in quoting of inductive types")
        (* quote_mut_ind produce an entry rather than a decl *)
        (* let c = Environ.lookup_mind (fst ni) env in (\* FIX: For efficienctly, we should also export (snd ni)*\) *)
        (* TermReify.quote_mut_ind env c *)
        | _ -> CErrors.user_err (str name ++ str " does not seem to be an inductive."))
  | TmQuoteConst (name, bypass, strict) ->
    begin
       let name = unquote_string (reduce_all env evm name) in
       let bypass = unquote_bool (reduce_all env evm bypass) in
       let cmd =
         let open Plugin_core in
         tmBind (tmAboutString name)
           (function
               None -> tmFail (str "not found: " ++ str name)
             | Some (Globnames.ConstRef cnst) ->
               let kn = KerName.to_string (Names.Constant.canonical cnst) in
               if strict && kn <> name then
                 tmFail (str "strict mode not canonical: \"" ++ str name ++ str "\" <> \"" ++ str kn ++ str "\"")
               else
                 with_env_evm (fun env evm ->
                     let cd = Environ.lookup_constant cnst env in
                     tmReturn (TermReify.quote_constant_body bypass env evm cd))
             | Some _ ->
               tmFail (str "\"" ++ str name ++ str "\" does not refer to a constant"))
       in
       Plugin_core.run cmd env evm (fun a b c -> k (a,b, quote_constant_entry c))
     end
  | TmQuoteUnivs ->
    let univs = Environ.universes env in
    k (env, evm, TermReify.quote_ugraph univs)
  | TmPrint trm ->
    Feedback.msg_info (Printer.pr_constr_env env evm trm);
    k (env, evm, Lazy.force unit_tt)
  | TmMsg msg ->
     let msg = unquote_string (reduce_all env evm msg) in
     Plugin_core.run (Plugin_core.tmMsg msg) env evm
      (fun env evm _ -> k (env, evm, Lazy.force unit_tt))
  | TmFail trm ->
    let err = unquote_string (reduce_all env evm trm) in
    CErrors.user_err (str err)
  | TmAbout id ->
    let id = Libnames.qualid_of_string (unquote_string id) in
    Plugin_core.run (Plugin_core.tmAbout id) env evm
      (fun env evm -> function
           None -> k (env, evm, constr_mkAppl (cNone, [|tglobal_reference|]))
         | Some gr ->
           let qgr = quote_global_reference gr in
           let opt = constr_mkApp (cSome , [|Lazy.force tglobal_reference ; qgr|]) in
           k (env, evm, opt))
  | TmCurrentModPath ->
    let mp = Lib.current_mp () in
    (* let dp' = Lib.cwd () in (* different on sections ? *) *)
    let s = quote_string (Names.ModPath.to_string mp) in
    k (env, evm, s)
  | TmEval (s, trm) ->
    let red = unquote_reduction_strategy env evm (reduce_all env evm s) in
    let (evm, trm) = reduce env evm red trm
    in k (env, evm, trm)
  | TmEvalTerm (s,trm) ->
    let red = unquote_reduction_strategy env evm (reduce_all env evm s) in
    let evm,trm = denote_term evm (reduce_all env evm trm) in
    Plugin_core.run (Plugin_core.tmEval red trm) env evm
      (fun env evm trm -> k (env, evm, TermReify.quote_term env trm))
  | TmMkInductive mind ->
    declare_inductive env evm mind;
    let env = Global.env () in
    k (env, evm, Lazy.force unit_tt)
  | TmUnquote t ->
    begin
       try
         let t = reduce_all env evm t in
         let evm, t' = denote_term evm t in
         let typ = Retyping.get_type_of env evm (EConstr.of_constr t') in
         let evm, typ = Evarsolve.refresh_universes (Some false) env evm typ in
         let make_typed_term typ term evm =
           match Lazy.force texistT_typed_term with
           | ConstructRef ctor ->
              let (evm,c) = Evarutil.new_global evm (Lazy.force texistT_typed_term) in
              let term = Constr.mkApp
               (EConstr.to_constr evm c, [|typ; t'|]) in
             let evm, _ = Typing.type_of env evm (EConstr.of_constr term) in
               (env, evm, term)
           | _ -> anomaly (str "texistT_typed_term does not refer to a constructor")
         in
           k (make_typed_term (EConstr.to_constr evm typ) t' evm)
        with Reduction.NotArity -> CErrors.user_err (str "unquoting ill-typed term")
      end
  | TmUnquoteTyped (typ, t) ->
       let evm, t' = denote_term evm (reduce_all env evm t) in
       let evdref = ref evm in
       (* let t' = Typing.e_solve_evars env evdref (EConstr.of_constr t') in *)
       Typing.e_check env evdref (EConstr.of_constr t') (EConstr.of_constr typ);
       let evm = !evdref in
       k (env, evm, t')
  | TmFreshName name ->
    let name' = Namegen.next_ident_away_from (unquote_ident name) (fun id -> Nametab.exists_cci (Lib.make_path id)) in
    k (env, evm, quote_ident name')
  | TmExistingInstance name ->
     Classes.existing_instance true (Libnames.qualid_of_ident (unquote_ident name)) None;
     k (env, evm, Lazy.force unit_tt)
  | TmInferInstance (s, typ) ->
    begin
      let evm, typ =
        match unquote_option s with
          Some s ->
          let red = unquote_reduction_strategy env evm s in
          reduce env evm red typ
        | None -> evm, typ in
      try
        let (evm,t) = Typeclasses.resolve_one_typeclass env evm (EConstr.of_constr typ) in
        k (env, evm, constr_mkApp (cSome, [| typ; EConstr.to_constr evm t|]))
      with
        Not_found -> k (env, evm, constr_mkApp (cNone, [|typ|]))
    end
  | TmInferInstanceTerm typ ->
    let evm,typ = denote_term evm (reduce_all env evm typ) in
    Plugin_core.run (Plugin_core.tmInferInstance typ) env evm
      (fun env evm -> function
           None -> k (env, evm, constr_mkAppl (cNone, [| tTerm|]))
         | Some trm ->
           let qtrm = TermReify.quote_term env trm in
           k (env, evm, constr_mkApp (cSome, [| Lazy.force tTerm; qtrm |])))
  | TmPrintTerm trm ->
    let evm,trm = denote_term evm (reduce_all env evm trm) in
    Plugin_core.run (Plugin_core.tmPrint trm) env evm
      (fun env evm _ -> k (env, evm, Lazy.force unit_tt))
