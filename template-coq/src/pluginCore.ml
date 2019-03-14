(* this file is the interface that extracted plugins will use.
 *)

type ident   = Names.Id.t (* Template.Ast.ident *)
type kername = Names.Constant.t (* Template.Ast.kername *)
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
  Environ.env -> Evd.evar_map -> (Environ.env * Evd.evar_map * 'a) option

let not_implemented (s : string) : 'a tm =
  fun _ _ ->
    failwith ("template monad operation " ^ s ^ " not yet implemented")

let tmReturn (x : 'a) : 'a tm =
  fun env evd -> Some (env, evd, x)
let tmBind (x : 'a tm) (k : 'a -> 'b tm) : 'b tm =
  fun env evd ->
  match x env evd with
  | None -> None
  | Some (env,evd,v) -> k v env evd

let tmPrint (t : term) : unit tm =
  fun env evd ->
    let _ = Feedback.msg_info (Printer.pr_constr_env env evd t) in
    Some (env, evd, ())
let tmMsg  (s : string) : unit tm =
  fun env evd ->
    let _ = Feedback.msg_info (Pp.str s) in
    Some (env, evd, ())

let tmFail (s : string) : 'a tm =
  fun _ _ -> CErrors.user_err (Pp.str s)
let tmEval (rd : reductionStrategy) (t : term) : term tm =
  not_implemented "tmEval"

let tmDefinition (nm : ident) (typ : term option) (trm : term) : kername tm =
  not_implemented "tmDefinition"
let tmAxiom (nm : ident) (typ : term) : kername tm =
  fun env evm ->
    let param =
      Entries.ParameterEntry
        (None, (typ, Monomorphic_const_entry (Evd.universe_context_set evm)), None)
    in
    let n =
      Declare.declare_constant nm
        (param, Decl_kinds.IsDefinition Decl_kinds.Definition)
    in
    Some (Global.env (), evm, n)
let tmLemma (nm : ident) (ty : term option) (trm : term) : kername tm =
  not_implemented "tmLemma"

let tmFreshName (nm : ident) : ident tm =
  fun env evd ->
    let name' =
      Namegen.next_ident_away_from nm (fun id -> Nametab.exists_cci (Lib.make_path id))
    in Some (env, evd, name')

let tmAbout (nm : ident) : global_reference option tm =
  not_implemented "tmAbout"
let tmCurrentModPath (_ : unit) : Names.ModPath.t tm =
  fun env evd ->
  let mp = Lib.current_mp () in Some (env, evd, mp)

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
