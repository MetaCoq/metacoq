(* this file is the interface that extracted plugins will use.
 *)

type ident   (* Template.Ast.ident *)
type kername (* Template.Ast.kername *)
type reductionStrategy (* Template.TemplateMonad.Common.reductionStrategy *)
type global_reference (* Template.Ast.global_reference *)
type term = Constr.t  (* Ast.term *)

type 'a tm

val tmReturn : 'a -> 'a tm
val tmBind : 'a tm -> ('a -> 'b tm) -> 'b tm

val tmPrint : term -> unit tm
val tmMsg  : string -> unit tm

val tmFail : string -> 'a tm
val tmEval : reductionStrategy -> term -> term tm

val tmDefinition : ident -> term option -> term -> kername tm
val tmAxiom : ident -> term -> kername tm
val tmLemma : ident -> term option -> term -> kername tm

val tmFreshName : ident -> ident tm

val tmAbout : ident -> global_reference option tm
val tmCurrentModPath : unit -> string tm

val tmQuoteInductive : kername -> _ tm
val tmQuoteUniverses : _ tm
val tmQuoteConstant : kername -> bool -> _ tm

val tmMkInductive : _ -> _ tm

val tmExistingInstance : kername -> unit tm
val tmInferInstance : term -> term option tm
