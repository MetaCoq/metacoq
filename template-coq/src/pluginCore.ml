(* this file is the interface that extracted plugins will use.
 *)

type ident   = Names.Id.t (* Template.Ast.ident *)
type kername = Names.KerName.t (* Template.Ast.kername *)
type reduction_strategy = Redexpr.red_expr (* Template.TemplateMonad.Common.reductionStrategy *)
type global_reference = Globnames.global_reference (* Template.Ast.global_reference *)
type term = Constr.t  (* Ast.term *)
type mutual_inductive_body = Declarations.mutual_inductive_body (* Template.Ast.mutual_inductive_body *)
type constant_entry = Declarations.constant_body (* Template.Ast.constant_entry *)
type mutual_inductive_entry = Entries.mutual_inductive_entry (* Template.Ast.mutual_inductive_entry *)

let default_flags = Redops.make_red_flag Genredexpr.[FBeta;FMatch;FFix;FCofix;FZeta;FDeltaBut []]
let rs_cbv = Genredexpr.Cbv default_flags
let rs_cbn = Genredexpr.Cbn default_flags
let rs_hnf = Genredexpr.Hnf
let rs_all = Genredexpr.Cbv Redops.all_flags
let rs_lazy = Genredexpr.Cbv Redops.all_flags

(* question(gmm): maybe this should just take a global_reference? *)
let rs_unfold (env : Environ.env) (kn : kername) =
  (* note(gmm): this shouldn't be necessary *)
  let ident = Names.Id.of_string (Names.KerName.to_string kn) in
  try
    let gr = (Nametab.global (CAst.make (Libnames.Qualid (Libnames.qualid_of_ident ident)))) in
    Genredexpr.Unfold [Locus.AllOccurrences,
                       Tacred.evaluable_of_global_reference env gr]
  with
  | _ -> CErrors.user_err Pp.(str "Constant not found or not a constant: " ++ str (Names.Id.to_string ident))

type 'a tm =
  { run_tm : Environ.env -> Evd.evar_map ->
      (Environ.env -> Evd.evar_map -> 'a -> unit) -> (unit -> unit) -> unit }
  (* note(gmm): i can't make this generic because of the way that
   * tmLemma works. in particular, it needs to create a definition
   * and then return, the result is passed through a hook.
   *)

let run (c : 'a tm) env evm (k : Environ.env -> Evd.evar_map -> 'a -> unit) : unit =
  c.run_tm env evm k (fun x -> x)

let not_implemented (s : string) : 'a tm =
  { run_tm = fun _ _ _ _ ->
    failwith ("template monad operation " ^ s ^ " not yet implemented") }

let tmReturn (x : 'a) : 'a tm =
  { run_tm = fun env evd k _ -> k env evd x }
let tmBind (x : 'a tm) (k : 'a -> 'b tm) : 'b tm =
  { run_tm = fun env evd success fail ->
        x.run_tm env evd (fun env evd v -> (k v).run_tm env evd success fail) fail }

let tmPrint (t : term) : unit tm =
  { run_tm = fun env evd success _ ->
    let _ = Feedback.msg_info (Printer.pr_constr_env env evd t) in
    success env evd () }
let tmMsg  (s : string) : unit tm =
  { run_tm = fun env evd success _ ->
    let _ = Feedback.msg_info (Pp.str s) in
    success env evd () }

let tmFail (s : string) : 'a tm =
  { run_tm = fun _ _ _ _ -> CErrors.user_err (Pp.str s) }

let tmEval (rd : reduction_strategy) (t : term) : term tm =
  { run_tm = fun env evd k _ ->
        let evd,t' = Quoter.reduce env evd rd t in
        k env evd t' }

let tmDefinition (nm : ident) ?poly:(poly=false) (typ : term option) (body : term) : kername tm =
  { run_tm = fun env evm success fail ->
    let univs =
      if poly
      then Entries.Polymorphic_const_entry (Evd.to_universe_context evm)
      else Entries.Monomorphic_const_entry (Evd.universe_context_set evm) in
    let n =
      Declare.declare_definition ~kind:Decl_kinds.Definition nm ?types:typ
        (body, univs)
    in success (Global.env ()) evm (Names.Constant.canonical n)
  }

let tmAxiom (nm : ident) ?poly:(poly=false) (typ : term) : kername tm =
  { run_tm = fun env evm success fail ->
    let param =
      let entry =
        if poly
        then Entries.Polymorphic_const_entry (Evd.to_universe_context evm)
        else Entries.Monomorphic_const_entry (Evd.universe_context_set evm)
      in Entries.ParameterEntry (None, (typ, entry), None)
    in
    let n =
      Declare.declare_constant nm
        (param, Decl_kinds.IsDefinition Decl_kinds.Definition)
    in
    success (Global.env ()) evm (Names.Constant.canonical n) }

(* this generates a lemma leaving a hole *)
let tmLemma (poly : bool) (nm : ident) (ty : term) : kername tm =
  { run_tm = fun env evm success fail ->
    let kind = (Decl_kinds.Global, poly, Decl_kinds.Definition) in
    let hole = CAst.make (Constrexpr.CHole (None, Misctypes.IntroAnonymous, None)) in
    let evm, (c, _) = Constrintern.interp_casted_constr_evars_impls env evm hole (EConstr.of_constr ty) in
    Obligations.check_evars env evm;
    let obls, _, c, cty = Obligations.eterm_obligations env nm evm 0 (EConstr.to_constr evm c) ty in
    (* let evm = Evd.minimize_universes evm in *)
    let ctx = Evd.evar_universe_context evm in
    let hook = Lemmas.mk_hook (fun _ gr _ ->
        let env = Global.env () in
        let evm = Evd.from_env env in
        let evm, t = Evd.fresh_global env evm gr in
        match Constr.kind t with
        | Constr.Const (tm, _) ->
          success env evm (Names.Constant.canonical tm)
        | _ -> failwith "Evd.fresh_global did not return a Const") in
    ignore (Obligations.add_definition nm ~term:c cty ctx ~kind ~hook obls) }

let tmFreshName (nm : ident) : ident tm =
  { run_tm = fun env evd success fail ->
    let name' =
      Namegen.next_ident_away_from nm (fun id -> Nametab.exists_cci (Lib.make_path id))
    in success env evd name' }

let tmAbout (nm : ident) : global_reference option tm =
  { run_tm = fun env evd success fail ->
    try
      let qualid = Libnames.qualid_of_ident nm in
      let gr = Smartlocate.locate_global_with_alias (CAst.make qualid) in
      success env evd (Some gr)
    with
    | Not_found -> success env evd None }

let tmCurrentModPath (_ : unit) : Names.ModPath.t tm =
  { run_tm = fun env evd success _ ->
    let mp = Lib.current_mp () in success env evd mp }

let tmQuoteInductive (kn : kername) : mutual_inductive_body option tm =
  { run_tm = fun env evm success fail ->
        try
          let mind = Environ.lookup_mind (Names.MutInd.make1 kn) env in
          success env evm (Some mind)
        with
          _ -> success env evm None }

let tmQuoteUniverses : _ tm =
  not_implemented "tmQuoteUniverses"

(* get the definition associated to a kername *)
let tmQuoteConstant (kn : kername) (bypass : bool) : constant_entry tm =
  { run_tm = fun env evd success fail ->
        let cnst = Environ.lookup_constant (Names.Constant.make1 kn) env in
        success env evd cnst }

let tmInductive (mi : mutual_inductive_entry) : unit tm =
  not_implemented "tmInductive"

let tmExistingInstance (kn : kername) : unit tm =
  { run_tm = fun env evd success fail ->
        (* note(gmm): this seems wrong. *)
        let ident = Names.Id.of_string (Names.KerName.to_string kn) in
        Classes.existing_instance true (CAst.make (Libnames.Qualid (Libnames.qualid_of_ident ident))) None;
        success env evd () }
let tmInferInstance (typ : term) : term option tm =
  { run_tm = fun env evm success fail ->
      try
        let (evm,t) = Typeclasses.resolve_one_typeclass env evm (EConstr.of_constr typ) in
        success env evm (Some (EConstr.to_constr evm t))
      with
        Not_found -> success env evm None }
