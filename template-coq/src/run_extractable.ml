open Extractable
open Plugin_core

let rec interp_tm (t : 'a coq_TM) : 'a tm =
  match t with
  | Coq_tmReturn x -> tmReturn x
  | Coq_tmBind (c, k) -> tmBind (interp_tm c) (fun x -> interp_tm (k x))
  | Coq_tmPrint t -> tmPrint t
  | Coq_tmMsg msg -> tmMsg msg
  | Coq_tmFail err -> tmFail err
  | Coq_tmEval (r,t) -> tmEval r t
  | Coq_tmDefinition (nm, typ, trm) -> tmDefinition nm typ trm
  | Coq_tmAxiom (nm, typ) -> tmAxiom nm typ
  | Coq_tmLemma (nm, typ) -> tmLemma nm typ
  | Coq_tmFreshName nm -> tmFreshName tm
  | Coq_tmAbout id -> tmAbout id
  | Coq_tmCurrentModPath -> tmCurrentModPath
  | Coq_tmQuoteIndutive kn -> tmQuoteInductive kn
  | Coq_tmQuoteUniverses -> tmQuoteUniverses
  | Coq_tmQuoteConstant (kn, b) -> tmQuoteConstant kn b
  | Coq_tmInductive i -> tmInductive i
  | Coq_tmExistingInstance k -> tmExistingInstance k
  | Coq_tmInferInstance t -> tmInferInstance t
