(* this file is the interface that extracted plugins will use.
 *)

type ident   = Names.Id.t (* Template.Ast.ident *)
type kername = Names.KerName.t (* Template.Ast.kername *)
type reductionStrategy =  (* Template.TemplateMonad.Common.reductionStrategy *)
    Cbv
  | Cbn
  | Hnf
  | All
  | Lazy
  | Unfold of ident
type global_reference (* Template.Ast.global_reference *)
type term = Constr.t  (* Ast.term *)
type mutual_inductive_body (* Template.Ast.mutual_inductive_body *)
type constant_entry (* Template.Ast.constant_entry *)

type 'a tm =
  { run_tm : Environ.env -> Evd.evar_map ->
      (Environ.env -> Evd.evar_map -> 'a -> unit) -> unit -> unit }
  (* note(gmm): i can't make this generic because of the way that
   * tmLemma works. in particular, it needs to create a definition
   * and then return, the result is passed through a hook.
   *)

let run (c : 'a tm) env evm (k : Environ.env -> Evd.evar_map -> 'a -> unit) : unit =
  c.run_tm env evm k ()

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
let tmEval (rd : reductionStrategy) (t : term) : term tm =
  { run_tm = fun env evd k _ ->
        let evd,t' = Quoter.reduce env evd rd t in
        k env evd t' }

let tmDefinition (nm : ident) (typ : term option) (trm : term) : kername tm =
  not_implemented "tmDefinition"
let tmAxiom (nm : ident) (typ : term) : kername tm =
  { run_tm = fun env evm success fail ->
    let param =
      Entries.ParameterEntry
        (None, (typ, Monomorphic_const_entry (Evd.universe_context_set evm)), None)
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
        | _ -> failwith "Evt.fresh_global did not return a Const") in
    ignore (Obligations.add_definition nm ~term:c cty ctx ~kind ~hook obls) }

let tmFreshName (nm : ident) : ident tm =
  { run_tm = fun env evd success fail ->
    let name' =
      Namegen.next_ident_away_from nm (fun id -> Nametab.exists_cci (Lib.make_path id))
    in success env evd name' }

let tmAbout (nm : ident) : global_reference option tm =
  not_implemented "tmAbout"
let tmCurrentModPath (_ : unit) : Names.ModPath.t tm =
  { run_tm = fun env evd success _ ->
    let mp = Lib.current_mp () in success env evd mp }

let tmQuoteInductive (kn : kername) : mutual_inductive_body tm =
  not_implemented "tmQuoteInductive"
let tmQuoteUniverses : _ tm =
  not_implemented "tmQuoteUniverses"
let tmQuoteConstant (kn : kername) (bypass : bool) : constant_entry tm =
  not_implemented "tmQuoteConstant"

let tmMkInductive : _ -> _ tm =
  fun _ -> not_implemented "tmMkInductive"

let tmExistingInstance (kn : kername) : unit tm =
  not_implemented "tmExistingInstance"
let tmInferInstance (tm : term) : term option tm =
  not_implemented "tmInferInstance"
