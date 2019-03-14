open CErrors
open Univ
open Entries
open Names
open Redops
open Genredexpr
open Pp (* this adds the ++ to the current scope *)

open Tm_util
open Quoter
open Constr_quoter
open TemplateCoqQuoter
open Template_monad
open Denote

let unquote_reduction_strategy env evm trm (* of type reductionStrategy *) : Redexpr.red_expr =
  let (trm, args) = app_full trm [] in
  (* from g_tactic.ml4 *)
  let default_flags = Redops.make_red_flag [FBeta;FMatch;FFix;FCofix;FZeta;FDeltaBut []] in
  if Constr.equal trm tcbv then Cbv default_flags
  else if Constr.equal trm tcbn then Cbn default_flags
  else if Constr.equal trm thnf then Hnf
  else if Constr.equal trm tall then Cbv all_flags
  else if Constr.equal trm tlazy then Lazy all_flags
  else if Constr.equal trm tunfold then
    match args with
    | name (* to unfold *) :: _ ->
       let name = reduce_all env evm name in
       let name = unquote_ident name in
       (try Unfold [Locus.AllOccurrences, Tacred.evaluable_of_global_reference env (Nametab.global (CAst.make (Libnames.Qualid (Libnames.qualid_of_ident name))))]
        with
        | _ -> CErrors.user_err (str "Constant not found or not a constant: " ++ Pp.str (Names.Id.to_string name)))
    | _ -> bad_term_verb trm "unquote_reduction_strategy"
  else not_supported_verb trm "unquote_reduction_strategy"



let denote_local_entry evm trm =
  let (h,args) = app_full trm [] in
  match args with
    x :: [] ->
    if Constr.equal h tLocalDef then
      let evm, x = denote_term evm x in
      evm, Entries.LocalDefEntry x
    else if  Constr.equal h tLocalAssum then
      let evm, x = denote_term evm x in
      evm, Entries.LocalAssumEntry x
    else
      not_supported_verb trm "denote_local_entry"
  | _ -> bad_term_verb trm "denote_local_entry"

let denote_mind_entry_finite trm =
  let (h,args) = app_full trm [] in
  match args with
    [] ->
    if Constr.equal h cFinite then Declarations.Finite
    else if  Constr.equal h cCoFinite then Declarations.CoFinite
    else if  Constr.equal h cBiFinite then Declarations.BiFinite
    else not_supported_verb trm "denote_mind_entry_finite"
  | _ -> bad_term_verb trm "denote_mind_entry_finite"



let unquote_map_option f trm =
  let (h,args) = app_full trm [] in
  if Constr.equal h cSome then
    match args with
      _ :: x :: [] -> Some (f x)
    | _ -> bad_term trm
  else if Constr.equal h cNone then
    match args with
      _ :: [] -> None
    | _ -> bad_term trm
  else
    not_supported_verb trm "unquote_map_option"

let denote_option = unquote_map_option (fun x -> x)



let unquote_constraint_type trm (* of type constraint_type *) : constraint_type =
  let (h,args) = app_full trm [] in
  match args with
    [] ->
    if Constr.equal h tunivLt then Univ.Lt
    else if Constr.equal h tunivLe then Univ.Le
    else if Constr.equal h tunivEq then Univ.Eq
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
  if Constr.equal trm cIrrelevant then Variance.Irrelevant
  else if Constr.equal trm cCovariant then Variance.Covariant
  else if Constr.equal trm cInvariant then Variance.Invariant
  else not_supported_verb trm "denote_variance"

let denote_ucontext evm trm (* of type UContext.t *) : _ * UContext.t =
  let i, c = unquote_pair trm in
  let evm, i = unquote_universe_instance evm i in
  let evm, c = unquote_constraints evm c in
  evm, Univ.UContext.make (i, c)

let denote_cumulativity_info evm trm (* of type CumulativityInfo *) : _ * CumulativityInfo.t =
  let uctx, variances = unquote_pair trm in
  let evm, uctx = denote_ucontext evm uctx in
  let variances = List.map denote_variance (unquote_list variances) in
  evm, CumulativityInfo.make (uctx, Array.of_list variances)


(* todo : stick to Coq implem *)
type universe_context_type =
  | Monomorphic_uctx of Univ.UContext.t
  | Polymorphic_uctx of Univ.UContext.t
  | Cumulative_uctx of Univ.CumulativityInfo.t

let to_entry_inductive_universes = function
  | Monomorphic_uctx ctx -> Monomorphic_ind_entry (ContextSet.of_context ctx)
  | Polymorphic_uctx ctx -> Polymorphic_ind_entry ctx
  | Cumulative_uctx ctx -> Cumulative_ind_entry ctx

let denote_universe_context evm trm (* of type universe_context *) : _ * universe_context_type =
  let (h, args) = app_full trm [] in
  match args with
  | ctx :: [] -> if Constr.equal h cMonomorphic_ctx then
                   let evm, ctx = denote_ucontext evm ctx in
                   evm, Monomorphic_uctx ctx
                 else if Constr.equal h cPolymorphic_ctx then
                   let evm, ctx = denote_ucontext evm ctx in
                   evm, Polymorphic_uctx ctx
                 else if Constr.equal h cCumulative_ctx then
                   let evm, ctx = denote_cumulativity_info evm ctx in
                   evm, Cumulative_uctx ctx
                 else
                   not_supported_verb trm "denote_universe_context"
  | _ -> bad_term_verb trm "denote_universe_context"



let unquote_one_inductive_entry evm trm (* of type one_inductive_entry *) : _ * Entries.one_inductive_entry =
  let (h,args) = app_full trm [] in
  if Constr.equal h tBuild_one_inductive_entry then
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

let unquote_mutual_inductive_entry evm trm (* of type mutual_inductive_entry *) : _ * Entries.mutual_inductive_entry =
  let (h,args) = app_full trm [] in
  if Constr.equal h tBuild_mutual_inductive_entry then
    match args with
    | record::finite::params::inds::univs::priv::[] ->
       let record = unquote_map_option (unquote_map_option unquote_ident) record in
       let finite = denote_mind_entry_finite finite in
       let evm, params = map_evm (fun evm p -> let (l,r) = unquote_pair p in
                                               let evm, e = denote_local_entry evm r in
                                               evm, (unquote_ident l, e))
                                 evm (unquote_list params) in
       let evm, inds = map_evm unquote_one_inductive_entry evm (unquote_list inds) in
       let evm, univs = denote_universe_context evm univs in
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
  debug (fun () -> str"declare_inductive: " ++ Printer.pr_constr_env env evm mind);
  let evm, mind = unquote_mutual_inductive_entry evm mind in
  ignore (ComInductive.declare_mutual_inductive_with_eliminations mind Names.Id.Map.empty [])


(* let not_in_tactic s =
 *   CErrors.user_err  (str ("You can not use " ^ s ^ " in a tactic.")) *)

(*
let monad_failure_full env evm s k prg =
  CErrors.user_err
    (str (s ^ " must take " ^ (string_of_int k) ^ " argument" ^ (if k > 0 then "s" else "") ^ ".") ++
       str "While trying to run: " ++ fnl () ++ Printer.pr_constr_env env evm prg ++ fnl () ++
       str "Please file a bug with Template-Coq.")
*)

(* note(gmm): polymorphism should probably be part an argument to `do_definition`
 *)
let do_definition evm k (name : Names.Id.t) (typ : Constr.t option) (body : Constr.t) =
  let univs =
    if Flags.is_universe_polymorphism ()
    then Polymorphic_const_entry (Evd.to_universe_context evm)
    else Monomorphic_const_entry (Evd.universe_context_set evm) in
  let n =
      Declare.declare_definition ~kind:k name ?types:typ
        (body, univs)
  in
  Constr.mkConst n

let do_lemma env evm k (poly : bool) (ident : Names.Id.t) (typ : Constr.t) (body : Constr.t) =
  let kind = (Decl_kinds.Global, poly, Decl_kinds.Definition) in
  let hole = CAst.make (Constrexpr.CHole (None, Misctypes.IntroAnonymous, None)) in
  let evm, (c, _) =
    Constrintern.interp_casted_constr_evars_impls env evm hole
      (EConstr.of_constr typ)
  in
  Obligations.check_evars env evm;
  let obls, _, c, cty =
    Obligations.eterm_obligations env ident evm 0 (EConstr.to_constr evm c) typ
  in
  let ctx = Evd.evar_universe_context evm in
  let hook =
    Lemmas.mk_hook (fun _ gr _ -> let env = Global.env () in
                     let evm = Evd.from_env env in
                     let evm, t = Evd.fresh_global env evm gr in
                     k (evm, t)) in
  ignore (Obligations.add_definition ident ~term:c cty ctx ~kind ~hook obls)
  (* question(gmm): why is this so different from `do_definition`? *)

let do_axiom evm (ident : Names.Id.t) (typ : Constr.t) =
    let param =
      Entries.ParameterEntry
        (None, (typ, Monomorphic_const_entry (Evd.universe_context_set evm)), None)
    in
    let n =
      Declare.declare_constant ident
        (param, Decl_kinds.IsDefinition Decl_kinds.Definition)
    in
    n


let under_option (f : Constr.t -> 'b) (t : Constr.t)
  : 'b option =
  match denote_option t with
    Some t -> Some (f t)
  | None -> None


let rec run_template_program_rec ?(intactic=false)
    (k : Environ.env * Evd.evar_map * Constr.t -> unit) env ((evm, pgm) : Evd.evar_map * Constr.t) : unit =
  let open TemplateMonad in
  let (kind, universes) = next_action env pgm in
  match kind with
    TmReturn h ->
    let (evm, _) = Typing.type_of env evm (EConstr.of_constr h) in
    k (env, evm, h)
  | TmBind (a,f) ->
    run_template_program_rec ~intactic:intactic (fun (env, evm, ar) -> run_template_program_rec ~intactic:intactic k env (evm, Constr.mkApp (f, [|ar|]))) env (evm, a)
  | TmDefinition (name,s,typ,body) ->
    let name = reduce_all env evm name in
    let evm, typ =
      match denote_option s with
        Some s -> let red = unquote_reduction_strategy env evm s in reduce env evm red typ
      | None -> evm, typ
    in
    let univs =
      if Flags.is_universe_polymorphism () then Polymorphic_const_entry (Evd.to_universe_context evm)
      else Monomorphic_const_entry (Evd.universe_context_set evm) in
    let n = Declare.declare_definition ~kind:Decl_kinds.Definition (unquote_ident name) ~types:typ (body, univs) in
    let env = Global.env () in
    k (env, evm, Constr.mkConst n)

  | TmMkDefinition (name, body) ->
    let name = unquote_ident (reduce_all env evm name) in
    let evm, trm = denote_term evm (reduce_all env evm body) in
    let (evm, _) = Typing.type_of env evm (EConstr.of_constr trm) in
    let _ = Declare.declare_definition ~kind:Decl_kinds.Definition name (trm, Monomorphic_const_entry (Evd.universe_context_set evm)) in
    let env = Global.env () in
    k (env, evm, unit_tt)
  | TmDefinitionTerm (Definition, name, typ, body) ->
    let name = unquote_ident (reduce_all env evm name) in
    let evm,body = denote_term evm body in
    let evm,typ =
      match
        under_option (fun t -> denote_term evm (reduce_all env evm t))
          typ
      with
      | None -> (evm, None)
      | Some (evm,t) -> (evm, Some t)
    in
    let res = do_definition evm Decl_kinds.Definition name typ body in
    k (env, evm, res)
  | TmDefinitionTerm (Lemma, name, typ, body) ->
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
                                let evm, t = Evd.fresh_global env evm gr in k (env, evm, t)) in
    ignore (Obligations.add_definition ident ~term:c cty ctx ~kind ~hook obls)
  (* let kind = Decl_kinds.(Global, Flags.use_polymorphic_flag (), DefinitionBody Definition) in *)
  (* Lemmas.start_proof (unquote_ident name) kind evm (EConstr.of_constr typ) *)
  (* (Lemmas.mk_hook (fun _ gr -> *)
  (* let evm, t = Evd.fresh_global env evm gr in k (env, evm, t) *)
  (* k (env, evm, unit_tt) *)
  (* )); *)

  | TmAxiom (name,s,typ) ->
    let name = unquote_ident (reduce_all env evm name) in
    let evm, typ =
      match denote_option s with
        Some s -> let red = unquote_reduction_strategy env evm s in reduce env evm red typ
      | None -> evm, typ
    in
    let res = do_axiom evm name typ in
    let env = Global.env () in
    k (env, evm, Constr.mkConst res) (* why not return kername? *)
  | TmAxiomTerm (name,typ) ->
    let name = unquote_ident (reduce_all env evm name) in
    let evm,typ = denote_term evm (reduce_all env evm typ) in
    let res = do_axiom evm name typ in
    let env = Global.env () in
    k (env, evm, Constr.mkConst res) (* why not return kername? *)
  | TmLemma (name,s,typ) ->
    let name = unquote_ident (reduce_all env evm name) in
    let evm, typ =
      match denote_option s with
        Some s -> let red = unquote_reduction_strategy env evm s in reduce env evm red typ
      | None -> evm, typ
    in
    let poly = Flags.is_universe_polymorphism () in
    let kind = (Decl_kinds.Global, poly, Decl_kinds.Definition) in
    let hole = CAst.make (Constrexpr.CHole (None, Misctypes.IntroAnonymous, None)) in
    let evm, (c, _) = Constrintern.interp_casted_constr_evars_impls env evm hole (EConstr.of_constr typ) in
    Obligations.check_evars env evm;
       let obls, _, c, cty = Obligations.eterm_obligations env name evm 0 (EConstr.to_constr evm c) typ in
       (* let evm = Evd.minimize_universes evm in *)
       let ctx = Evd.evar_universe_context evm in
       let hook = Lemmas.mk_hook (fun _ gr _ -> let env = Global.env () in
                                                let evm = Evd.from_env env in
                                                let evm, t = Evd.fresh_global env evm gr in k (env, evm, t)) in  (* todo better *)
       ignore (Obligations.add_definition name ~term:c cty ctx ~kind ~hook obls)
    (* let kind = Decl_kinds.(Global, Flags.use_polymorphic_flag (), DefinitionBody Definition) in *)
    (* Lemmas.start_proof (unquote_ident name) kind evm (EConstr.of_constr typ) *)
    (* (Lemmas.mk_hook (fun _ gr -> *)
    (* let evm, t = Evd.fresh_global env evm gr in k (env, evm, t) *)
    (* k (env, evm, unit_tt) *)
    (* )); *)
  | TmQuote (false, trm) ->
    let qt = TermReify.quote_term env trm (* user should do the reduction (using tmEval) if they want *)
    in k (env, evm, qt)
  | TmQuote (true, trm) ->
    let qt = TermReify.quote_term_rec env trm in
    k (env, evm, qt)
  | TmQuoteInd name ->
       let name = reduce_all env evm name in
       let name = unquote_string name in
       let (dp, nm) = split_name name in
       (match Nametab.locate (Libnames.make_qualid dp nm) with
        | Globnames.IndRef ni ->
           let t = TermReify.quote_mind_decl env (fst ni) in
           let _, args = Constr.destApp t in
           (match args with
            | [|kn; decl|] ->
               k (env, evm, decl)
            | _ -> bad_term_verb t "anomaly in quoting of inductive types")
        (* quote_mut_ind produce an entry rather than a decl *)
        (* let c = Environ.lookup_mind (fst ni) env in (\* FIX: For efficienctly, we should also export (snd ni)*\) *)
        (* TermReify.quote_mut_ind env c *)
        | _ -> CErrors.user_err (str name ++ str " does not seem to be an inductive."))
  | TmQuoteConst (name,bypass) ->
       let name = reduce_all env evm name in
       let name = unquote_string name in
       let bypass = reduce_all env evm bypass in
       let bypass = unquote_bool bypass in
       let entry = TermReify.quote_entry_aux bypass env evm name in
       let entry =
         match entry with
         | Some (Left cstentry) -> TemplateCoqQuoter.quote_constant_entry cstentry
         | Some (Right _) -> CErrors.user_err (str name ++ str " refers to an inductive")
         | None -> bad_term_verb pgm "anomaly in QuoteConstant"
       in
       k (env, evm, entry)
  | TmQuoteUnivs ->
    let univs = Environ.universes env in
    k (env, evm, quote_ugraph univs)
  | TmPrint trm -> Feedback.msg_info (Printer.pr_constr_env env evm trm);
    k (env, evm, unit_tt)
  | TmMsg msg ->
     let msg = reduce_all env evm msg in
     let msg = unquote_string msg in
     Feedback.msg_info (str msg);
     k (env, evm, unit_tt)
  | TmFail trm ->
    let err = unquote_string (reduce_all env evm trm) in
    CErrors.user_err (str err)
  | TmAbout id ->
    begin
      let id = unquote_string id in
      try
        let gr = Smartlocate.locate_global_with_alias (CAst.make (Libnames.qualid_of_string id)) in
        let opt = Constr.mkApp (cSome , [|tglobal_reference ; quote_global_reference gr|]) in
        k (env, evm, opt)
      with
      | Not_found -> k (env, evm, Constr.mkApp (cNone, [|tglobal_reference|]))
    end
  | TmCurrentModPath ->
    let mp = Lib.current_mp () in
    (* let dp' = Lib.cwd () in (* different on sections ? *) *)
    let s = quote_string (Names.ModPath.to_string mp) in
    k (env, evm, s)
  | TmEval (s, trm) ->
    let red = unquote_reduction_strategy env evm s in
    let (evm, trm) = reduce env evm red trm
    in k (env, evm, trm)
  | TmEvalTerm (s,trm) ->
    let red = unquote_reduction_strategy env evm s in
    let evdref = ref evm in
    let (evm, trm) =
      let evm,t = denote_term evm trm in
      reduce env evm red t
    in
    k (env,evm, trm)
  | TmMkInductive mind ->
    declare_inductive env evm mind;
    let env = Global.env () in
    k (env, evm, unit_tt)
  | TmUnquote t ->
       (try
         let t = reduce_all env evm t in
         let evm, t' = denote_term evm t in
         let typ = Retyping.get_type_of env evm (EConstr.of_constr t') in
         let evm, typ = Evarsolve.refresh_universes (Some false) env evm typ in
         let make_typed_term typ term evm =
           match texistT_typed_term with
           | ConstructRef ctor ->
              let (evm,c) = Evarutil.new_global evm texistT_typed_term in
              let term = Constr.mkApp
               (EConstr.to_constr evm c, [|typ; t'|]) in
             let evm, _ = Typing.type_of env evm (EConstr.of_constr term) in
               (env, evm, term)
           | _ -> anomaly (str "texistT_typed_term does not refer to a constructor")
         in
           k (make_typed_term (EConstr.to_constr evm typ) t' evm)
        with Reduction.NotArity -> CErrors.user_err (str "unquoting ill-typed term"))
  | TmUnquoteTyped (typ, t) ->
       let t = reduce_all env evm t in
       let evm, t' = denote_term evm t in
       let evdref = ref evm in
       (* let t' = Typing.e_solve_evars env evdref (EConstr.of_constr t') in *)
       Feedback.msg_debug (Printer.pr_constr_env env !evdref typ);
       Typing.e_check env evdref (EConstr.of_constr t') (EConstr.of_constr typ);
       let evm = !evdref in
       k (env, evm, t')
  | TmFreshName name ->
    let name' = Namegen.next_ident_away_from (unquote_ident name) (fun id -> Nametab.exists_cci (Lib.make_path id)) in
    k (env, evm, quote_ident name')
  | TmExistingInstance name ->
    Classes.existing_instance true (CAst.make (Libnames.Qualid (Libnames.qualid_of_ident (unquote_ident name)))) None
  | TmInferInstance (s, typ) ->
    begin
      let evm, typ = (match denote_option s with Some s -> let red = unquote_reduction_strategy env evm s in reduce env evm red typ | None -> evm, typ) in
      try
        let (evm,t) = Typeclasses.resolve_one_typeclass env evm (EConstr.of_constr typ) in
        k (env, evm, Constr.mkApp (cSome, [| typ; EConstr.to_constr evm t|]))
      with
        Not_found -> k (env, evm, Constr.mkApp (cNone, [|typ|]))
    end
  | TmInferInstanceTerm typ ->
    begin
      let evm,typ = denote_term evm (reduce_all env evm typ) in
      try
        let (evm,t) = Typeclasses.resolve_one_typeclass env evm (EConstr.of_constr typ) in
        let quoted = TermReify.quote_term env (EConstr.to_constr evm t) in
        k (env, evm, Constr.mkApp (cSome, [| tTerm; quoted |]))
      with
        Not_found -> k (env, evm, Constr.mkApp (cNone, [| tTerm|]))
     end
  | TmPrintTerm trm ->
    begin
      try
       let t = reduce_all env evm trm in
       let evdref = ref evm in
       let evm',t' = denote_term evm t in
       Feedback.msg_info (Printer.pr_constr_env env evm' t');
       k (env, evm, unit_tt)
      with
      Reduction.NotArity -> CErrors.user_err (str "printing ill-typed term")
    end
