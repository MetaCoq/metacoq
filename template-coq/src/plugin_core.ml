(* this file is the interface that extracted plugins will use.
 *)

type ident   = Names.Id.t (* Template.BasicAst.ident *)
type qualid  = Libnames.qualid (* Template.BasicAst.qualid *)
type kername = Names.KerName.t (* Template.BasicAst.kername *)
type reduction_strategy = Redexpr.red_expr (* Template.TemplateMonad.Common.reductionStrategy *)
type global_reference = Names.GlobRef.t (* Template.Ast.global_reference *)
type term = Constr.t  (* Template.Ast.term *)
type mutual_inductive_body = Declarations.mutual_inductive_body (* Template.Ast.mutual_inductive_body *)
type constant_body = Opaqueproof.opaque Declarations.constant_body
type constant_entry = Entries.constant_entry (* Template.Ast.constant_entry *)
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
  let env = Global.env () in 
  let evm = Evd.from_env env in
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
    let evm, def = DeclareDef.prepare_definition ~allow_evars:true ~opaque 
        ~poly ~types:(Option.map EConstr.of_constr typ) evm 
        UState.default_univ_decl ~body:(EConstr.of_constr body) in
    let n =
      DeclareDef.declare_definition ~kind:(Decls.(IsDefinition Definition)) 
        ~name:nm ~scope:(DeclareDef.Global Declare.ImportDefaultBehavior)
        Names.Id.Map.empty def []
    in success (Global.env ()) evm (Names.Constant.canonical (Globnames.destConstRef n))

let tmAxiom (nm : ident) ?poly:(poly=false) (typ : term) : kername tm =
  fun env evm success _fail ->
    let param =
      let entry = Evd.univ_entry ~poly evm
       in Declare.ParameterEntry (None, (typ, entry), None)
    in
    let n =
      Declare.declare_constant ~name:nm
        ~kind:(Decls.IsDefinition Decls.Definition)
        param
    in
    success (Global.env ()) evm (Names.Constant.canonical n)

(* this generates a lemma leaving a hole *)
let tmLemma (nm : ident) ?poly:(poly=false)(ty : term) : kername tm =
  fun env evm success _fail ->
    let kind = Decls.Definition in
    let hole = CAst.make (Constrexpr.CHole (Some Evar_kinds.(QuestionMark default_question_mark), Namegen.IntroAnonymous, None)) in
    Feedback.msg_debug (Pp.str "interp_casted called");
    let evm, (c, _) =
      try Constrintern.interp_casted_constr_evars_impls ~program_mode:true env evm hole (EConstr.of_constr ty)
      with e -> Feedback.msg_debug (Pp.str "interp_casted raised"); raise e in
    Obligations.check_evars env evm;
    let obls, _, c, cty = Obligations.eterm_obligations env nm evm 0 c (EConstr.of_constr ty) in
    (* let evm = Evd.minimize_universes evm in *)
    let ctx = Evd.evar_universe_context evm in
    let hook = DeclareDef.Hook.make (fun { DeclareDef.Hook.S.dref = gr } ->
        let env = Global.env () in
        let evm = Evd.from_env env in
        let evm, t = Evd.fresh_global env evm gr in
        match Constr.kind (EConstr.to_constr evm t) with
        | Constr.Const (tm, _) ->
          success env evm (Names.Constant.canonical tm)
        | _ -> failwith "Evd.fresh_global did not return a Const") in
    ignore (Obligations.add_definition ~name:nm ~term:c cty ctx ~poly ~kind ~hook obls)

let tmFreshName (nm : ident) : ident tm =
  fun env evd success _fail ->
    let name' =
      Namegen.next_ident_away_from nm (fun id -> Nametab.exists_cci (Lib.make_path id))
    in success env evd name'

let tmAbout (qualid : qualid) : global_reference option tm =
  fun env evd success _fail ->
    let opt =
      try
        Some (Smartlocate.locate_global_with_alias qualid)
      with
        Not_found -> None
    in success env evd opt


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

(*let universes_entry_of_decl ?withctx d =
  let open Declarations in
  let open Entries in
  match d with
  | Monomorphic ctx -> 
    (match withctx with
    | Some ctx' -> Monomorphic_entry (Univ.ContextSet.union ctx ctx')
    | None -> Monomorphic_entry ctx)
  | Polymorphic ctx -> 
    assert(Option.is_empty withctx);
    Polymorphic_entry (Univ.AUContext.names ctx, Univ.AUContext.repr ctx)*)
(*
let _constant_entry_of_cb (cb : Declarations.constant_body) =
  let open Declarations in
  let open Entries in
  let secctx = match cb.const_hyps with [] -> None | l -> Some l in
  let with_body_opaque b ?withctx opaque =
    Entries.{ const_entry_secctx = secctx;
    const_entry_feedback = None;
    const_entry_type = Some cb.const_type;
    const_entry_body = Future.from_val ((b, Univ.ContextSet.empty), Safe_typing.empty_private_constants);
    const_entry_universes = universes_entry_of_decl ?withctx cb.const_universes;
    const_entry_opaque = opaque;
    const_entry_inline_code = cb.const_inline_code }
  in
  let parameter inline =
    (secctx, (cb.const_type, universes_entry_of_decl cb.const_universes), inline)
  in
  match cb.const_body with
  | Def b -> DefinitionEntry (with_body_opaque (Mod_subst.force_constr b) false)
  | Undef inline -> ParameterEntry (parameter inline)
  | OpaqueDef pr -> 
    let opaquetab = Global.opaque_tables () in
    let proof = Opaqueproof.force_proof opaquetab pr in
    let ctx = Opaqueproof.force_constraints opaquetab pr in
    DefinitionEntry (with_body_opaque proof ~withctx:ctx true)
  | Primitive _ -> failwith "Primitives not supported by TemplateCoq"

*)

(* get the definition associated to a kername *)
let tmQuoteConstant (kn : kername) (bypass : bool) : Opaqueproof.opaque Declarations.constant_body tm =
  fun env evd success fail ->
    (* todo(gmm): there is a bug here *)
    try
      let cnst = Environ.lookup_constant (Names.Constant.make1 kn) env in
      success env evd cnst
    with
      Not_found -> fail Pp.(str "constant not found " ++ Names.KerName.print kn)

let tmInductive (mi : mutual_inductive_entry) : unit tm =
  fun env evd success _fail ->
    ignore (DeclareInd.declare_mutual_inductive_with_eliminations mi Names.Id.Map.empty []) ;
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
