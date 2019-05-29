open CErrors
open Univ
open Names
open GlobRef
open Constr_quoter
open Pp

open Quoter

module TemplateMonad :
sig
  type template_monad =
      TmReturn of Constr.t
    | TmBind  of Constr.t * Constr.t
    | TmPrint of Constr.t
    | TmFail of Constr.t
    | TmEval of Constr.t * Constr.t
    | TmDefinition of Constr.t * Constr.t * Constr.t * Constr.t
    | TmAxiom of Constr.t * Constr.t * Constr.t
    | TmLemma of Constr.t * Constr.t * Constr.t
    | TmFreshName of Constr.t
    | TmAbout of Constr.t
    | TmCurrentModPath
    | TmQuote of Constr.t
    | TmQuoteRec of Constr.t
    | TmQuoteInd of Constr.t
    | TmQuoteUnivs
    | TmQuoteConst of Constr.t * Constr.t
    | TmMkDefinition of Constr.t * Constr.t
    | TmMkInductive of Constr.t
    | TmUnquote of Constr.t
    | TmUnquoteTyped of Constr.t * Constr.t
    | TmExistingInstance of Constr.t
    | TmInferInstance of Constr.t * Constr.t

  val next_action
    : Environ.env -> Constr.t -> (template_monad * Univ.Instance.t)

end =
struct

  let resolve_symbol (path : string list) (tm : string) : Constr.t Lazy.t =
    lazy (gen_constant_in_modules contrib_name [path] tm)

  let resolve_symbol_p (path : string list) (tm : string) : global_reference Lazy.t =
    lazy (Coqlib.gen_reference_in_modules contrib_name [path] tm)

  let pkg_reify = ["Template";"Ast"]
  let pkg_template_monad = ["Template";"TemplateMonad"]
  let pkg_template_monad_prop = ["Template";"TemplateMonad";"Core";"InProp"]
  let pkg_template_monad_type = ["Template";"TemplateMonad";"Core";"InType"]

  let r_reify = resolve_symbol pkg_reify
  let r_template_monad = resolve_symbol pkg_template_monad
  let r_template_monad_prop_p = resolve_symbol_p pkg_template_monad_prop
  let r_template_monad_type_p = resolve_symbol_p pkg_template_monad_type


  (* for "InProp" *)
  let (ptmReturn,
       ptmBind,
       ptmQuote,
       ptmQuoteRec,
       ptmEval,
       ptmDefinitionRed,
       ptmAxiomRed,
       ptmLemmaRed,
       ptmFreshName,
       ptmAbout,
       ptmCurrentModPath,
       ptmMkDefinition,
       ptmMkInductive,
       ptmPrint,
       ptmFail,
       ptmQuoteInductive,
       ptmQuoteConstant,
       ptmQuoteUniverses,
       ptmUnquote,
       ptmUnquoteTyped,
       ptmInferInstance,
       ptmExistingInstance) =
    (r_template_monad_prop_p "tmReturn",
     r_template_monad_prop_p "tmBind",
     r_template_monad_prop_p "tmQuote",
     r_template_monad_prop_p "tmQuoteRec",
     r_template_monad_prop_p "tmEval",
     r_template_monad_prop_p "tmDefinitionRed",
     r_template_monad_prop_p "tmAxiomRed",
     r_template_monad_prop_p "tmLemmaRed",
     r_template_monad_prop_p "tmFreshName",
     r_template_monad_prop_p "tmAbout",
     r_template_monad_prop_p "tmCurrentModPath",
     r_template_monad_prop_p "tmMkDefinition",
     r_template_monad_prop_p "tmMkInductive",
     r_template_monad_prop_p "tmPrint",
     r_template_monad_prop_p "tmFail",
     r_template_monad_prop_p "tmQuoteInductive",
     r_template_monad_prop_p "tmQuoteConstant",
     r_template_monad_prop_p "tmQuoteUniverses",
     r_template_monad_prop_p "tmUnquote",
     r_template_monad_prop_p "tmUnquoteTyped",
     r_template_monad_prop_p "tmInferInstance",
     r_template_monad_prop_p "tmExistingInstance")

  (* for "InType" *)
  let (ttmReturn,
       ttmBind,
       ttmEval,
       ttmDefinitionRed,
       ttmAxiomRed,
       ttmLemmaRed,
       ttmFreshName,
       ttmAbout,
       ttmCurrentModPath,
       ttmMkDefinition,
       ttmMkInductive,
       ttmFail,
       ttmQuoteInductive,
       ttmQuoteConstant,
       ttmQuoteUniverses,
       ttmUnquote,
       ttmUnquoteTyped,
       ttmInferInstance,
       ttmExistingInstance) =
    (r_template_monad_type_p "tmReturn",
     r_template_monad_type_p "tmBind",
     r_template_monad_type_p "tmEval",
     r_template_monad_type_p "tmDefinitionRed",
     r_template_monad_type_p "tmAxiomRed",
     r_template_monad_type_p "tmLemmaRed",
     r_template_monad_type_p "tmFreshName",
     r_template_monad_type_p "tmAbout",
     r_template_monad_type_p "tmCurrentModPath",
     r_template_monad_type_p "tmMkDefinition",
     r_template_monad_type_p "tmMkInductive",
     r_template_monad_type_p "tmFail",
     r_template_monad_type_p "tmQuoteInductive",
     r_template_monad_type_p "tmQuoteConstant",
     r_template_monad_type_p "tmQuoteUniverses",
     r_template_monad_type_p "tmUnquote",
     r_template_monad_type_p "tmUnquoteTyped",
     r_template_monad_type_p "tmInferInstance",
     r_template_monad_type_p "tmExistingInstance")

  type constr = Constr.t

  type template_monad =
      TmReturn of Constr.t
    | TmBind  of Constr.t * Constr.t
    | TmPrint of Constr.t
    | TmFail of Constr.t
    | TmEval of Constr.t * Constr.t
    | TmDefinition of Constr.t * Constr.t * Constr.t * Constr.t
    | TmAxiom of Constr.t * Constr.t * Constr.t
    | TmLemma of Constr.t * Constr.t * Constr.t
    | TmFreshName of Constr.t
    | TmAbout of Constr.t
    | TmCurrentModPath
    | TmQuote of Constr.t
    | TmQuoteRec of Constr.t
    | TmQuoteInd of Constr.t
    | TmQuoteUnivs
    | TmQuoteConst of Constr.t * Constr.t
    | TmMkDefinition of Constr.t * Constr.t
    | TmMkInductive of Constr.t
    | TmUnquote of Constr.t
    | TmUnquoteTyped of Constr.t * Constr.t
    | TmExistingInstance of Constr.t
    | TmInferInstance of Constr.t * Constr.t

  (* todo: the recursive call is uneeded provided we call it on well formed terms *)
  let rec app_full trm acc =
    match Constr.kind trm with
      Constr.App (f, xs) -> app_full f (Array.to_list xs @ acc)
    | _ -> (trm, acc)

  let monad_failure s k =
    CErrors.user_err  (str (s ^ " must take " ^ (string_of_int k) ^ " argument" ^ (if k > 0 then "s" else "") ^ ".")
                       ++ str "Please file a bug with Template-Coq.")

  let print_term (u: Constr.t) : Pp.t = pr_constr u

  let monad_failure_full s k prg =
    CErrors.user_err
      (str (s ^ " must take " ^ (string_of_int k) ^ " argument" ^ (if k > 0 then "s" else "") ^ ".") ++
       str "While trying to run: " ++ fnl () ++ print_term prg ++ fnl () ++
       str "Please file a bug with Template-Coq.")

  let next_action env (pgm : constr) : template_monad * _ =
    let pgm = Reduction.whd_all env pgm in
    let (coConstr, args) = app_full pgm [] in
    let (glob_ref, universes) =
      try
        let open Constr in
        match kind coConstr with
        | Const (c, u) -> ConstRef c, u
        | Ind (i, u) -> IndRef i, u
        | Construct (c, u) -> ConstructRef c, u
        | Var id -> VarRef id, Instance.empty
        | _ -> raise Not_found
      with _ ->
        CErrors.user_err (str "Invalid argument or not yet implemented. The argument must be a TemplateProgram: " ++ pr_constr coConstr)
    in
    if Globnames.eq_gr glob_ref (Lazy.force ptmReturn) || Globnames.eq_gr glob_ref (Lazy.force ttmReturn) then
      match args with
      | _::h::[] ->
        (TmReturn h, universes)
      | _ -> monad_failure "tmReturn" 2
    else if Globnames.eq_gr glob_ref (Lazy.force ptmBind) || Globnames.eq_gr glob_ref (Lazy.force ttmBind) then
      match args with
      | _::_::a::f::[] ->
        (TmBind (a, f), universes)
      | _ -> monad_failure_full "tmBind" 4 pgm
    else if Globnames.eq_gr glob_ref (Lazy.force ptmDefinitionRed) || Globnames.eq_gr glob_ref (Lazy.force ttmDefinitionRed) then
      match args with
      | name::s::typ::body::[] ->
        (TmDefinition (name,s,typ,body), universes)
      | _ -> monad_failure "tmDefinitionRed" 4
    else if Globnames.eq_gr glob_ref (Lazy.force ptmAxiomRed) || Globnames.eq_gr glob_ref (Lazy.force ttmAxiomRed) then
      match args with
      | name::s::typ::[] ->
        (TmAxiom (name,s,typ), universes)
      | _ -> monad_failure "tmAxiomRed" 3
    else if Globnames.eq_gr glob_ref (Lazy.force ptmLemmaRed) || Globnames.eq_gr glob_ref (Lazy.force ttmLemmaRed) then
      match args with
      | name::s::typ::[] ->
        (TmLemma (name,s,typ), universes)
      | _ -> monad_failure "tmLemmaRed" 3
    else if Globnames.eq_gr glob_ref (Lazy.force ptmMkDefinition) || Globnames.eq_gr glob_ref (Lazy.force ttmMkDefinition) then
      match args with
      | name::body::[] ->
        (TmMkDefinition (name, body), universes)
      | _ -> monad_failure "tmMkDefinition" 2
    else if Globnames.eq_gr glob_ref (Lazy.force ptmQuote) then
      match args with
      | _::trm::[] ->
        (TmQuote trm, universes)
      | _ -> monad_failure "tmQuote" 2
    else if Globnames.eq_gr glob_ref (Lazy.force ptmQuoteRec) then
      match args with
      | _::trm::[] ->
        (TmQuoteRec trm, universes)
      | _ -> monad_failure "tmQuoteRec" 2
    else if Globnames.eq_gr glob_ref (Lazy.force ptmQuoteInductive) || Globnames.eq_gr glob_ref (Lazy.force ttmQuoteInductive) then
      match args with
      | name::[] ->
        (TmQuoteInd name, universes)
      | _ -> monad_failure "tmQuoteInductive" 1
    else if Globnames.eq_gr glob_ref (Lazy.force ptmQuoteConstant) || Globnames.eq_gr glob_ref (Lazy.force ttmQuoteConstant) then
      match args with
      | name::bypass::[] ->
        (TmQuoteConst (name, bypass), universes)
      | _ -> monad_failure "tmQuoteConstant" 2
    else if Globnames.eq_gr glob_ref (Lazy.force ptmQuoteUniverses) || Globnames.eq_gr glob_ref (Lazy.force ttmQuoteUniverses) then
      match args with
      | _::[] ->
        (TmQuoteUnivs, universes)
      | _ -> monad_failure "tmQuoteUniverses" 1
    else if Globnames.eq_gr glob_ref (Lazy.force ptmPrint) then
      match args with
      | _::trm::[] ->
        (TmPrint trm, universes)
      | _ -> monad_failure "tmPrint" 2
    else if Globnames.eq_gr glob_ref (Lazy.force ptmFail) || Globnames.eq_gr glob_ref (Lazy.force ttmFail) then
      match args with
      | _::trm::[] ->
        (TmFail trm, universes)
      | _ -> monad_failure "tmFail" 2
    else if Globnames.eq_gr glob_ref (Lazy.force ptmAbout) || Globnames.eq_gr glob_ref (Lazy.force ttmAbout) then
      match args with
      | id::[] ->
        (TmAbout id, universes)
      | _ -> monad_failure "tmAbout" 1
    else if Globnames.eq_gr glob_ref (Lazy.force ptmCurrentModPath) || Globnames.eq_gr glob_ref (Lazy.force ttmCurrentModPath) then
      match args with
      | _::[] ->
        (TmCurrentModPath, universes)
      | _ -> monad_failure "tmCurrentModPath" 1
    else if Globnames.eq_gr glob_ref (Lazy.force ptmEval) || Globnames.eq_gr glob_ref (Lazy.force ttmEval) then
      match args with
      | s(*reduction strategy*)::_(*type*)::trm::[] ->
        (TmEval (s, trm), universes)
      | _ -> monad_failure "tmEval" 3
    else if Globnames.eq_gr glob_ref (Lazy.force ptmMkInductive) || Globnames.eq_gr glob_ref (Lazy.force ttmMkInductive) then
      match args with
      | mind::[] -> (TmMkInductive mind, universes)
      | _ -> monad_failure "tmMkInductive" 1
    else if Globnames.eq_gr glob_ref (Lazy.force ptmUnquote) || Globnames.eq_gr glob_ref (Lazy.force ttmUnquote) then
      match args with
      | t::[] ->
        (TmUnquote t, universes)
      | _ -> monad_failure "tmUnquote" 1
    else if Globnames.eq_gr glob_ref (Lazy.force ptmUnquoteTyped) || Globnames.eq_gr glob_ref (Lazy.force ttmUnquoteTyped) then
      match args with
      | typ::t::[] ->
        (TmUnquoteTyped (typ, t), universes)
      | _ -> monad_failure "tmUnquoteTyped" 2
    else if Globnames.eq_gr glob_ref (Lazy.force ptmFreshName) || Globnames.eq_gr glob_ref (Lazy.force ttmFreshName) then
      match args with
      | name::[] ->
        (TmFreshName name, universes)
      | _ -> monad_failure "tmFreshName" 1
    else if Globnames.eq_gr glob_ref (Lazy.force ptmExistingInstance) || Globnames.eq_gr glob_ref (Lazy.force ttmExistingInstance) then
      match args with
      | name :: [] ->
        (TmExistingInstance name, universes)
      | _ -> monad_failure "tmExistingInstance" 1
    else if Globnames.eq_gr glob_ref (Lazy.force ptmInferInstance) || Globnames.eq_gr glob_ref (Lazy.force ttmInferInstance) then
      match args with
      | s :: typ :: [] ->
        (TmInferInstance (s, typ), universes)
      | _ -> monad_failure "tmInferInstance" 2
    else CErrors.user_err (str "Invalid argument or not yet implemented. The argument must be a TemplateProgram: " ++ pr_constr coConstr)

end
