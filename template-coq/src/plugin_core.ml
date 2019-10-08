(* this file is the interface that extracted plugins will use.
 *)

type ident   = Names.Id.t (* Template.BasicAst.ident *)
type qualid  = Libnames.qualid (* Template.BasicAst.qualid *)
type kername = Names.KerName.t (* Template.BasicAst.kername *)
type reduction_strategy = Redexpr.red_expr (* Template.TemplateMonad.Common.reductionStrategy *)
type global_reference = Globnames.global_reference (* Template.Ast.global_reference *)
type term = Constr.t  (* Template.Ast.term *)
type mutual_inductive_body = Declarations.mutual_inductive_body (* Template.Ast.mutual_inductive_body *)
type constant_entry = Declarations.constant_body (* Template.Ast.constant_entry *)
type mutual_inductive_entry = Entries.mutual_inductive_entry (* Template.Ast.mutual_inductive_entry *)

let default_flags = Redops.make_red_flag Genredexpr.[FBeta;FMatch;FFix;FCofix;FZeta;FDeltaBut []]
let rs_cbv = Genredexpr.Cbv default_flags
let rs_cbn = Genredexpr.Cbn default_flags
let rs_hnf = Genredexpr.Hnf
let rs_all = Genredexpr.Cbv Redops.all_flags
let rs_lazy = Genredexpr.Cbv Redops.all_flags
let rs_unfold (env : Environ.env) (gr : global_reference) =
  try
    Genredexpr.Unfold [Locus.AllOccurrences,
                       Tacred.evaluable_of_global_reference env gr]
  with
  | _ -> CErrors.user_err
           Pp.(str "Constant not found or not a constant: " ++ Printer.pr_global gr)

type 'a tm =
  Environ.env -> Evd.evar_map ->
  (Environ.env -> Evd.evar_map -> 'a -> unit) ->
  (Pp.t -> unit) -> unit

let run (c : 'a tm) env evm (k : Environ.env -> Evd.evar_map -> 'a -> unit) : unit =
  c env evm k (fun x -> CErrors.user_err x)

let run_vernac (c : 'a tm) : unit =
  let (evm,env) = Pfedit.get_current_context () in
  run c env evm (fun _ _ _ -> ())

let with_env_evm (c : Environ.env -> Evd.evar_map -> 'a tm) : 'a tm =
  fun env evm success fail -> c env evm env evm success fail

let tmReturn (x : 'a) : 'a tm =
  fun env evd k _fail -> k env evd x
let tmBind (x : 'a tm) (k : 'a -> 'b tm) : 'b tm =
  fun env evd success fail ->
        x env evd (fun env evd v -> k v env evd success fail) fail
let tmMap (f : 'a -> 'b) (x : 'a tm) : 'b tm =
  fun env evd success fail ->
        x env evd (fun env evd v -> success env evd (f v)) fail

let tmPrint (t : term) : unit tm =
  fun env evd success _fail ->
    let _ = Feedback.msg_info (Printer.pr_constr_env env evd t) in
    success env evd ()
let tmMsg  (s : string) : unit tm =
  fun env evd success _fail ->
    let _ = Feedback.msg_info (Pp.str s) in
    success env evd ()

let tmFail (s : Pp.t) : 'a tm =
  fun _ _ _ fail -> fail s
let tmFailString (s : string) : 'a tm =
  tmFail Pp.(str s)

let tmEval (rd : reduction_strategy) (t : term) : term tm =
  fun env evd k _fail ->
    let evd,t' = Quoter.reduce env evd rd t in
    k env evd t'

let tmDefinition (nm : ident) ?poly:(poly=false) ?opaque:(opaque=false) (typ : term option) (body : term) : kername tm =
  fun env evm success _fail ->
    let univs =
      if poly
      then Entries.Polymorphic_const_entry (Evd.to_universe_context evm)
      else Entries.Monomorphic_const_entry (Evd.universe_context_set evm) in
    let n =
      Declare.declare_definition ~opaque:opaque ~kind:Decl_kinds.Definition nm ?types:typ
        (body, univs)
    in success (Global.env ()) evm (Names.Constant.canonical n)
     
let tmAxiom (nm : ident) ?poly:(poly=false) (typ : term) : kername tm =
  fun env evm success _fail ->
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
    success (Global.env ()) evm (Names.Constant.canonical n)

(* this generates a lemma leaving a hole *)
let tmLemma (nm : ident) ?poly:(poly=false)(ty : term) : kername tm =
  fun env evm success _fail ->
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
        match Constr.kind (EConstr.to_constr evm t) with
        | Constr.Const (tm, _) ->
          success env evm (Names.Constant.canonical tm)
        | _ -> failwith "Evd.fresh_global did not return a Const") in
    ignore (Obligations.add_definition nm ~term:c cty ctx ~kind ~hook obls)

let tmFreshName (nm : ident) : ident tm =
  fun env evd success _fail ->
    let name' =
      Namegen.next_ident_away_from nm (fun id -> Nametab.exists_cci (Lib.make_path id))
    in success env evd name'

let tmAbout (qualid : qualid) : global_reference option tm =
  fun env evd success _fail ->
    try
      let gr = Smartlocate.locate_global_with_alias qualid in
      success env evd (Some gr)
    with
      Not_found -> success env evd None

let tmAboutString (s : string) : global_reference option tm =
  fun env evd success fail ->
    let (dp, nm) = Quoted.split_name s in
    let q = Libnames.make_qualid dp nm in
    tmAbout q env evd success fail

let tmCurrentModPath : Names.ModPath.t tm =
  fun env evd success _fail ->
    let mp = Lib.current_mp () in success env evd mp

let tmQuoteInductive (kn : kername) : (Names.MutInd.t * mutual_inductive_body) option tm =
  fun env evm success _fail ->
    try
      let mi = Names.MutInd.make1 kn in
      let mind = Environ.lookup_mind mi env in
      success env evm (Some (mi, mind))
    with
      Not_found -> success env evm None

let tmQuoteUniverses : UGraph.t tm =
  fun env evm success _fail ->
    success env evm (Environ.universes env)

(* get the definition associated to a kername *)
let tmQuoteConstant (kn : kername) (bypass : bool) : constant_entry tm =
  fun env evd success fail ->
    (* todo(gmm): there is a bug here *)
    try
      let cnst = Environ.lookup_constant (Names.Constant.make1 kn) env in
      success env evd cnst
    with
      Not_found -> fail Pp.(str "constant not found " ++ Names.KerName.print kn)

let tmInductive (mi : mutual_inductive_entry) : unit tm =
  fun env evd success _fail ->
    ignore (ComInductive.declare_mutual_inductive_with_eliminations mi Names.Id.Map.empty []) ;
    success (Global.env ()) evd ()

let tmExistingInstance (kn : kername) : unit tm =
  fun env evd success _fail ->
    (* note(gmm): this seems wrong. *)
    let ident = Names.Id.of_string (Names.KerName.to_string kn) in
    Classes.existing_instance true (Libnames.qualid_of_ident ident) None;
    success env evd ()

let tmInferInstance (typ : term) : term option tm =
  fun env evm success fail ->
    try
      let (evm,t) = Typeclasses.resolve_one_typeclass env evm (EConstr.of_constr typ) in
      success env evm (Some (EConstr.to_constr evm t))
    with
      Not_found -> success env evm None
