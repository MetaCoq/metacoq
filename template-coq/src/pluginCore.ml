(* this file is the interface that extracted plugins will use.
 *)

type ident   (* Template.Ast.ident *)
type kername (* Template.Ast.kername *)
type reductionStrategy (* Template.TemplateMonad.Common.reductionStrategy *)
type global_reference (* Template.Ast.global_reference *)
type term = Constr.t  (* Ast.term *)

type 'a tm = 'a

let not_implemented (s : string) : 'a tm =
  assert false

let tmReturn (x : 'a) : 'a tm = x
let tmBind (x : 'a) (k : 'a -> 'b tm) : 'b tm =
  k x

let tmPrint (t : term) : unit tm =
  not_implemented "tmPrint"
let tmMsg  (s : string) : unit tm =
  not_implemented "tmMsg"

let tmFail (s : string) : 'a tm =
  not_implemented "tmFail"
let tmEval (rd : reductionStrategy) (t : term) : term tm =
  not_implemented "tmEval"

let tmDefinition (nm : ident) (typ : term option) (trm : term) : kername tm =
  not_implemented "tmDefinition"
let tmAxiom (nm : ident) (trm : term) : kername tm =
  not_implemented "tmAxiom"
let tmLemma (nm : ident) (ty : term option) (trm : term) : kername tm =
  not_implemented "tmLemma"

let tmFreshName (nm : ident) : ident tm =
  not_implemented "tmFreshName"

let tmAbout (nm : ident) : global_reference option tm =
  not_implemented "tmAbout"
let tmCurrentModPath (_ : unit) : string tm =
  not_implemented "tmCurrentModPath"

let tmQuoteInductive (kn : kername) : _ tm =
  not_implemented "tmQuoteInductive"
let tmQuoteUniverses : _ tm =
  not_implemented "tmQuoteUniverses"
let tmQuoteConstant (kn : kername) (bypass : bool) : _ tm =
  not_implemented "tmQuoteConstant"

let tmMkInductive : _ -> _ tm =
  not_implemented "tmMkInductive"

let tmExistingInstance (kn : kername) : unit tm =
  not_implemented "tmExistingInstance"
let tmInferInstance (tm : term) : term option tm =
  not_implemented "tmInferInstance"
