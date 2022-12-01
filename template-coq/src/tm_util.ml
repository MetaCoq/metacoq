open Pp
  
let contrib_name = "template-coq"

let gen_constant_in_modules s =
  lazy (
    let tm_ref = Coqlib.lib_ref s in
    UnivGen.constr_of_monomorphic_global (Global.env ()) tm_ref
  )
  (* lazy (Universes.constr_of_global (Coqlib.gen_reference_in_modules locstr dirs s)) *)

(* This allows to load template_plugin and the extractable plugin at the same time 
  while have option settings apply to both *)
  let timing_opt =
  let open Goptions in
  let key = ["MetaCoq"; "Timing"] in
  let tables = get_tables () in
  try 
    let _ = OptionMap.find key tables in
    fun () -> 
      let tables = get_tables () in
      let opt = OptionMap.find key tables in
      match opt.opt_value with
      | BoolValue b -> b
      | _ -> assert false
  with Not_found ->
    declare_bool_option_and_ref ~depr:false ~key ~value:false

let time prefix f x =
  if timing_opt () then 
    let start = Unix.gettimeofday () in
    let res = f x in
    let stop = Unix.gettimeofday () in
    let () = Feedback.msg_info Pp.(prefix ++ str " executed in: " ++ Pp.real (stop -. start) ++ str "s") in
    res
  else f x
  
let debug_opt =
  let open Goptions in
  let key = ["MetaCoq"; "Debug"] in
  let tables = get_tables () in
  try 
    let _ = OptionMap.find key tables in
    fun () -> 
      let tables = get_tables () in
      let opt = OptionMap.find key tables in
      match opt.opt_value with
      | BoolValue b -> b
      | _ -> assert false
  with Not_found ->
  declare_bool_option_and_ref ~depr:false ~key ~value:false

let debug (m : unit ->Pp.t) =
  if debug_opt () then
    Feedback.(msg_debug (m ()))
  else
    ()
type ('a,'b) sum =
  Left of 'a | Right of 'b

let rec filter_map f l =
  match l with
  | [] -> []
  | x :: xs ->
    match f x with
    | Some x' -> x' :: filter_map f xs
    | None -> filter_map f xs
    
let rec app_full trm acc =
  match Constr.kind trm with
    Constr.App (f, xs) -> app_full f (Array.to_list xs @ acc)
  | _ -> (trm, acc)

let not_supported trm =
  let env = Global.env () in
  CErrors.user_err (str "Not Supported:" ++ spc () ++ Printer.pr_constr_env env (Evd.from_env env) trm)

let not_supported_verb trm rs =
  let env = Global.env () in
  CErrors.user_err (str "Not Supported raised at " ++ str rs ++ str ":" ++ spc () ++
    Printer.pr_constr_env env (Evd.from_env env) trm)

let bad_term trm =
  let env = Global.env () in
  CErrors.user_err (str "Bad term:" ++ spc () ++ Printer.pr_constr_env env (Evd.from_env env) trm)

let bad_term_verb trm rs =
  let env = Global.env () in
  CErrors.user_err (str "Bad term:" ++ spc () ++ Printer.pr_constr_env env (Evd.from_env env) trm
                    ++ spc () ++ str " Error: " ++ str rs)


module CaseCompat =
  struct

  open Constr
  open Context.Rel.Declaration
  open Vars
  open Util
  open Univ
  open Declarations

  (** {6 Changes of representation of Case nodes} *)

  (** Provided:
      - a universe instance [u]
      - a term substitution [subst]
      - name replacements [nas]
      [instantiate_context u subst nas ctx] applies both [u] and [subst] to [ctx]
      while replacing names using [nas] (order reversed)
  *)
  let instantiate_context u subst nas ctx =
    let rec instantiate i ctx = match ctx with
    | [] -> assert (Int.equal i (-1)); []
    | LocalAssum (_, ty) :: ctx ->
      let ctx = instantiate (pred i) ctx in
      let ty = substnl subst i (subst_instance_constr u ty) in
      LocalAssum (nas.(i), ty) :: ctx
    | LocalDef (_, ty, bdy) :: ctx ->
      let ctx = instantiate (pred i) ctx in
      let ty = substnl subst i (subst_instance_constr u ty) in
      let bdy = substnl subst i (subst_instance_constr u bdy) in
      LocalDef (nas.(i), ty, bdy) :: ctx
    in
    instantiate (Array.length nas - 1) ctx

  let case_predicate_context_gen mip ci u paramsubst nas =
    let realdecls, _ = List.chop mip.mind_nrealdecls mip.mind_arity_ctxt in
    let self =
      let args = Context.Rel.instance mkRel 0 mip.mind_arity_ctxt in
      let inst = Instance.of_array (Array.init (Instance.length u) Level.var) in
      mkApp (mkIndU (ci.ci_ind, inst), args)
    in
    let realdecls = LocalAssum (Context.anonR, self) :: realdecls in
    instantiate_context u paramsubst nas realdecls

  let case_predicate_context env ci u params nas =
    let mib = Environ.lookup_mind (fst ci.ci_ind) env in
    let mip = mib.mind_packets.(snd ci.ci_ind) in
    let paramdecl = Vars.subst_instance_context u mib.mind_params_ctxt in
    let paramsubst = Vars.subst_of_rel_context_instance paramdecl params in
    case_predicate_context_gen mip ci u paramsubst nas
      
  let case_branches_contexts_gen mib ci u params brs =
    (* Γ ⊢ c : I@{u} params args *)
    (* Γ, indices, self : I@{u} params indices ⊢ p : Type *)
    let mip = mib.mind_packets.(snd ci.ci_ind) in
    let paramdecl = Vars.subst_instance_context u mib.mind_params_ctxt in
    let paramsubst = Vars.subst_of_rel_context_instance paramdecl params in
    (* Expand the branches *)
    let subst = paramsubst in
    let ebr =
      let build_one_branch i (nas, br) (ctx, _) =
        let ctx, _ = List.chop mip.mind_consnrealdecls.(i) ctx in
        let ctx = instantiate_context u subst nas ctx in
        (nas, ctx, br)
      in
      Array.map2_i build_one_branch brs mip.mind_nf_lc
    in 
    ebr

  let case_branches_contexts env ci u pars brs =
    let mib = Environ.lookup_mind (fst ci.ci_ind) env in
    case_branches_contexts_gen mib ci u pars brs
end

module RetypeMindEntry =
  struct

  open Entries
  open Names
  open Univ

  let retype env evm c = 
    Typing.type_of env evm (EConstr.of_constr c)

  let retype_decl env evm decl =
    match decl with
    | Context.Rel.Declaration.LocalAssum (na, ty) ->
      let evm, ty = Typing.solve_evars env evm (EConstr.of_constr ty) in
      evm, Context.Rel.Declaration.LocalAssum (na, ty)
    | Context.Rel.Declaration.LocalDef (na, b, ty) ->
      let evm, b = Typing.solve_evars env evm (EConstr.of_constr b) in
      let evm, ty = Typing.solve_evars env evm (EConstr.of_constr ty) in
      let evm = Typing.check env evm b ty in
      evm, Context.Rel.Declaration.LocalDef (na, b, ty)
    
  let retype_context env evm ctx = 
    let env, evm, ctx = Context.Rel.fold_outside (fun decl (env, evm, ctx) ->
      let evm, d = retype_decl env evm decl in
      (EConstr.push_rel d env, evm, d :: ctx)) 
      ctx ~init:(env, evm, [])
    in evm, ctx

  let sup_sort s1 s2 = 
    let open Sorts in
    match s1, s2 with
  | (_, SProp) -> assert false (* template SProp not allowed *)
  | (SProp, s) | (Prop, s) | (s, Prop) -> s
  | (Set, Set) -> Sorts.set
  | (Set, Type u) | (Type u, Set) -> Sorts.sort_of_univ (Universe.sup u Universe.type0)
  | (Type u, Type v) -> Sorts.sort_of_univ (Universe.sup u v)


  let infer_mentry_univs env evm mind =
    let pars = mind.mind_entry_params in
    let evm, pars' = retype_context env evm pars in
    let envpars = Environ.push_rel_context pars env in
    let evm, arities =
      List.fold_left 
        (fun (evm, ctx) oib -> 
          let ty = oib.mind_entry_arity in
          let evm, s = retype envpars evm ty in
          let ty = Term.it_mkProd_or_LetIn ty pars in
          (evm, Context.Rel.Declaration.LocalAssum (Context.annotR (Name oib.mind_entry_typename), ty) :: ctx))
        (evm, []) mind.mind_entry_inds
    in
    let env = Environ.push_rel_context arities env in
    let env = Environ.push_rel_context pars env in
    let evm =
      List.fold_left 
        (fun evm oib ->
          let evm, cstrsort = 
            List.fold_left (fun (evm, sort) cstr ->
              let evm, cstrty = retype env evm cstr in
              let _, cstrsort = Reduction.dest_arity env (EConstr.to_constr evm cstrty) in
              (evm, sup_sort sort cstrsort))
            (evm, Sorts.prop) oib.mind_entry_lc
          in
          let _, indsort = Reduction.dest_arity env oib.mind_entry_arity in
          (* Hacky, but we don't have a good way to enfore max() <= max() constraints yet *)
          let evm = try Evd.set_leq_sort env evm cstrsort indsort with e -> evm in
          evm)
        evm mind.mind_entry_inds
    in
    evm, mind

  let nf_mentry_univs evm mind =
    let pars = List.map EConstr.Unsafe.to_rel_decl (Evarutil.nf_rel_context_evar evm (List.map EConstr.of_rel_decl mind.mind_entry_params)) in
    let nf_evar c = EConstr.Unsafe.to_constr (Evarutil.nf_evar evm (EConstr.of_constr c)) in
    let inds =
      List.map
          (fun oib -> 
            let arity = nf_evar oib.mind_entry_arity in
            let cstrs = List.map nf_evar oib.mind_entry_lc in
            { oib with mind_entry_arity = arity; mind_entry_lc = cstrs })
         mind.mind_entry_inds
      in
      { mind with mind_entry_params = pars; mind_entry_inds = inds }

  let infer_mentry_univs env evm mind = 
    let evm = 
      match mind.mind_entry_universes with
      | Entries.Monomorphic_ind_entry -> evm
      | Entries.Template_ind_entry uctx -> evm
      | Entries.Polymorphic_ind_entry uctx ->
        let uctx' = ContextSet.of_context uctx in
        Evd.merge_context_set (UState.UnivFlexible false) evm uctx'
    in
    let evm, mind = infer_mentry_univs env evm mind in
    let evm = Evd.minimize_universes evm in
    let mind = nf_mentry_univs evm mind in
    let ctx, mind = 
      match mind.mind_entry_universes with
      | Entries.Monomorphic_ind_entry ->
        Evd.universe_context_set evm, { mind with mind_entry_universes = Entries.Monomorphic_ind_entry }
      | Entries.Template_ind_entry ctx ->
        Evd.universe_context_set evm, { mind with mind_entry_universes = Entries.Template_ind_entry ctx }
      | Entries.Polymorphic_ind_entry uctx ->
        let uctx' = Evd.to_universe_context evm in
        Univ.ContextSet.empty, { mind with mind_entry_universes = Entries.Polymorphic_ind_entry uctx' }
    in ctx, mind
end 

type ('term, 'name, 'nat) adef = { adname : 'name; adtype : 'term; adbody : 'term; rarg : 'nat }

type ('term, 'name, 'nat) amfixpoint = ('term, 'name, 'nat) adef list

type ('term, 'name, 'universe_instance) apredicate = 
  { auinst : 'universe_instance; 
    apars : 'term list;
    apcontext : 'name list;
    apreturn : 'term }

type ('term, 'name) abranch =
  { abcontext : 'name list;
    abbody : 'term }

type ('nat, 'inductive, 'relevance) acase_info =
  { aci_ind : 'inductive;
    aci_npar : 'nat;
    aci_relevance : 'relevance }
    
type ('term, 'nat, 'ident, 'name, 'quoted_sort, 'cast_kind, 'kername, 'inductive, 'relevance, 'universe_instance, 'projection, 'int63, 'float64) structure_of_term =
  | ACoq_tRel of 'nat
  | ACoq_tVar of 'ident
  | ACoq_tEvar of 'nat * 'term list
  | ACoq_tSort of 'quoted_sort
  | ACoq_tCast of 'term * 'cast_kind * 'term
  | ACoq_tProd of 'name * 'term * 'term
  | ACoq_tLambda of 'name * 'term * 'term
  | ACoq_tLetIn of 'name * 'term * 'term * 'term
  | ACoq_tApp of 'term * 'term list
  | ACoq_tConst of 'kername * 'universe_instance
  | ACoq_tInd of 'inductive * 'universe_instance
  | ACoq_tConstruct of 'inductive * 'nat * 'universe_instance
  | ACoq_tCase of ('nat, 'inductive, 'relevance) acase_info * 
    ('term, 'name, 'universe_instance) apredicate *
    'term * ('term, 'name) abranch list
  | ACoq_tProj of 'projection * 'term
  | ACoq_tFix of ('term, 'name, 'nat) amfixpoint * 'nat
  | ACoq_tCoFix of ('term, 'name, 'nat) amfixpoint * 'nat
  | ACoq_tInt of 'int63
  | ACoq_tFloat of 'float64

