(* this file is the interface that extracted plugins will use.
 *)

type ident   = Names.Id.t (* Template.BasicAst.ident *)
type qualid  = Libnames.qualid (* Template.BasicAst.ident *)
type kername = Names.KerName.t (* Template.BasicAst.kername *)
type reduction_strategy = Redexpr.red_expr (* Template.TemplateMonad.Common.reductionStrategy *)
type global_reference = Globnames.global_reference (* Template.Ast.global_reference *)
type term = Constr.t  (* Template.Ast.term *)
type mutual_inductive_body = Declarations.mutual_inductive_body (* Template.Ast.mutual_inductive_body *)
type constant_entry = Declarations.constant_body (* Template.Ast.constant_entry *)
type mutual_inductive_entry = Entries.mutual_inductive_entry (* Template.Ast.mutual_inductive_entry *)

val rs_cbv : reduction_strategy
val rs_cbn : reduction_strategy
val rs_hnf : reduction_strategy
val rs_all : reduction_strategy
val rs_lazy : reduction_strategy
val rs_unfold : Environ.env -> global_reference -> reduction_strategy

type 'a tm

val run : 'a tm -> Environ.env -> Evd.evar_map -> (Environ.env -> Evd.evar_map -> 'a -> unit) -> unit

val with_env_evm : (Environ.env -> Evd.evar_map -> 'a tm) -> 'a tm

val run_vernac : 'a tm -> unit

val tmReturn : 'a -> 'a tm
val tmBind : 'a tm -> ('a -> 'b tm) -> 'b tm
val tmMap  : ('a -> 'b) -> 'a tm -> 'b tm

val tmPrint : term -> unit tm
val tmMsg  : string -> unit tm

val tmFail : Pp.t -> 'a tm
val tmFailString : string -> 'a tm
val tmEval : reduction_strategy -> term -> term tm

val tmDefinition : ident -> ?poly:bool -> ?opaque:bool -> term option -> term -> kername tm
val tmAxiom : ident -> ?poly:bool -> term -> kername tm
val tmLemma : ident -> ?poly:bool -> term -> kername tm

val tmFreshName : ident -> ident tm

val tmAbout : qualid -> global_reference option tm
val tmAboutString : string -> global_reference option tm
val tmCurrentModPath : Names.ModPath.t tm

val tmQuoteInductive : kername -> (Names.MutInd.t * mutual_inductive_body) option tm
val tmQuoteUniverses : UGraph.t tm
val tmQuoteConstant : kername -> bool -> constant_entry tm

val tmInductive : mutual_inductive_entry -> unit tm

val tmExistingInstance : kername -> unit tm
val tmInferInstance : term -> term option tm
