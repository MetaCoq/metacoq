(* this file is the interface that extracted plugins will use.
 *)

type ident   = Names.Id.t (* Template.Ast.ident *)
type kername = Names.KerName.t (* Template.Ast.kername *)
type reduction_strategy = Redexpr.red_expr (* Template.TemplateMonad.Common.reductionStrategy *)
type global_reference = Globnames.global_reference (* Template.Ast.global_reference *)
type term = Constr.t  (* Ast.term *)
type mutual_inductive_body = Declarations.mutual_inductive_body (* Template.Ast.mutual_inductive_body *)
type constant_entry = Declarations.constant_body (* Template.Ast.constant_entry *)

val rs_cbv : reduction_strategy
val rs_cbn : reduction_strategy
val rs_hnf : reduction_strategy
val rs_all : reduction_strategy
val rs_lazy : reduction_strategy
(* val rs_unfold : ? *)


type 'a tm

val run : 'a tm -> Environ.env -> Evd.evar_map -> (Environ.env -> Evd.evar_map -> 'a -> unit) -> unit

val tmReturn : 'a -> 'a tm
val tmBind : 'a tm -> ('a -> 'b tm) -> 'b tm

val tmPrint : term -> unit tm
val tmMsg  : string -> unit tm

val tmFail : string -> 'a tm
val tmEval : reduction_strategy -> term -> term tm

val tmDefinition : ident -> ?poly:bool -> term option -> term -> kername tm
val tmAxiom : ident -> ?poly:bool -> term -> kername tm
val tmLemma : bool -> ident -> term -> kername tm

val tmFreshName : ident -> ident tm

val tmAbout : ident -> global_reference option tm
val tmCurrentModPath : unit -> Names.ModPath.t tm

val tmQuoteInductive : kername -> mutual_inductive_body option tm
val tmQuoteUniverses : _ tm
val tmQuoteConstant : kername -> bool -> constant_entry tm

val tmMkInductive : _ -> _ tm

val tmExistingInstance : kername -> unit tm
val tmInferInstance : term -> term option tm
