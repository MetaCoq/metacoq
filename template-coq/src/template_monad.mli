val ptmTestQuote : Names.global_reference Lazy.t
val ptmQuoteDefinition : Names.global_reference Lazy.t
val ptmQuoteDefinitionRed : Names.global_reference Lazy.t
val ptmQuoteRecDefinition : Names.global_reference Lazy.t
val ptmMkDefinition : Names.global_reference Lazy.t
val ptmMkInductive : Names.global_reference Lazy.t


type template_monad =
    TmReturn of Constr.t
  | TmBind  of Constr.t * Constr.t

    (* printing *)
  | TmPrint of Constr.t      (* only Prop *)
  | TmPrintTerm of Constr.t  (* only Extractable *)
  | TmMsg of Constr.t
  | TmFail of Constr.t

    (* evaluation *)
  | TmEval of Constr.t * Constr.t      (* only Prop *)
  | TmEvalTerm of Constr.t * Constr.t  (* only Extractable *)

    (* creating definitions *)
  | TmDefinition of Constr.t * Constr.t * Constr.t * Constr.t * Constr.t
  | TmDefinitionTerm of Constr.t * Constr.t * Constr.t * Constr.t
  | TmLemma of Constr.t * Constr.t
  | TmLemmaTerm of Constr.t * Constr.t
  | TmAxiom of Constr.t * Constr.t * Constr.t
  | TmAxiomTerm of Constr.t * Constr.t
  | TmMkInductive of Constr.t
  | TmVariable of Constr.t * Constr.t

  | TmFreshName of Constr.t

  | TmAbout of Constr.t
  | TmCurrentModPath

    (* quoting *)
  | TmQuote of bool * Constr.t  (* only Prop *)
  | TmQuoteInd of Constr.t * bool (* strict *)
  | TmQuoteConst of Constr.t * Constr.t * bool (* strict *)
  | TmQuoteUnivs

  | TmUnquote of Constr.t                   (* only Prop *)
  | TmUnquoteTyped of Constr.t * Constr.t (* only Prop *)

    (* typeclass resolution *)
  | TmExistingInstance of Constr.t
  | TmInferInstance of Constr.t * Constr.t (* only Prop *)
  | TmInferInstanceTerm of Constr.t        (* only Extractable *)


val app_full
  : Constr.constr -> Constr.constr list -> Constr.constr * Constr.constr list


val next_action
  : Environ.env -> Evd.evar_map -> Constr.t -> (template_monad * Univ.Instance.t)
