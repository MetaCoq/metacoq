
(** The reifier to Coq values *)
module ConstrReification =
struct
  type t = Constr.t

  type quoted_ident = Constr.t (* of type Ast.ident *)
  type quoted_int = Constr.t (* of type nat *)
  type quoted_bool = Constr.t (* of type bool *)
  type quoted_name = Constr.t (* of type BasicAst.name *)
  type quoted_aname = Constr.t (* of type BasicAst.aname (names with relevance) *)
  type quoted_relevance = Constr.t (* of type BasicAst.relevance *)
  type quoted_sort = Constr.t (* of type Ast.universe *)
  type quoted_cast_kind = Constr.t  (* of type Ast.cast_kind *)
  type quoted_kernel_name = Constr.t (* of type Ast.kername *)
  type quoted_inductive = Constr.t (* of type Ast.inductive *)
  type quoted_proj = Constr.t (* of type Ast.projection *)
  type quoted_global_reference = Constr.t (* of type Ast.global_reference *)

  type quoted_sort_family = Constr.t (* of type Ast.sort_family *)
  type quoted_constraint_type = Constr.t (* of type Universes.constraint_type *)
  type quoted_univ_constraint = Constr.t (* of type Universes.univ_constraint *)
  type quoted_univ_constraints = Constr.t (* of type Universes.constraints *)
  type quoted_univ_instance = Constr.t (* of type Universes.universe_instance *)
  type quoted_univ_context = Constr.t (* of type Universes.UContext.t *)
  type quoted_univ_contextset = Constr.t (* of type Universes.ContextSet.t *)
  type quoted_abstract_univ_context = Constr.t (* of type Universes.AUContext.t *)
  type quoted_variance = Constr.t (* of type Universes.Variance.t *)
  type quoted_universes_decl = Constr.t (* of type Universes.universes_decl *)

  type quoted_universes_entry = Constr.t (* of type Ast.universes_entry *)
  type quoted_ind_entry = quoted_ident * t * quoted_bool * quoted_ident list * t list
  type quoted_definition_entry = Constr.t (* of type Ast.definition_entry *)
  type quoted_parameter_entry = Constr.t (* of type Ast.parameter_entry *)
  type quoted_constant_entry = Constr.t (* of type Ast.constant_entry *)
  type quoted_mind_entry = Constr.t (* of type Ast.mutual_inductive_entry *)
  type quoted_mind_finiteness = Constr.t (* of type Ast.mutual_inductive_entry ?? *)
  type quoted_entry = Constr.t (* of type option (constant_entry + mutual_inductive_entry) *)

  type quoted_context_decl = Constr.t (* in Ast *)
  type quoted_context = Constr.t (* in Ast *)

  type quoted_one_inductive_body = Constr.t (* of type Ast.one_inductive_body *)
  type quoted_mutual_inductive_body = Constr.t (* of type Ast.mutual_inductive_body *)
  type quoted_constant_body = Constr.t (* of type Ast.constant_body *)
  type quoted_global_decl = Constr.t (* of type Ast.global_decl *)
  type quoted_global_env = Constr.t (* of type Ast.global_env *)
  type quoted_program = Constr.t (* of type Ast.program *)

  let resolve (tm : string) : Constr.t Lazy.t =
    lazy (
      let tm_ref = Coqlib.lib_ref tm in
      UnivGen.constr_of_monomorphic_global tm_ref
    )
    (* gen_constant_in_modules contrib_name [path] tm *)

  let resolve_ref (tm : string) : Names.GlobRef.t Lazy.t =
    lazy (Coqlib.lib_ref tm)

  let ast s = resolve ("metacoq.ast." ^ s)
  let template s = resolve ("metacoq.template." ^ s)
  let template_ref s = resolve_ref ("metacoq.template." ^ s)

  let tString = resolve "metacoq.string.cons"
  let tEmptyString = resolve "metacoq.string.nil"
  let tO = resolve "metacoq.nat.zero"
  let tS = resolve "metacoq.nat.succ"
  let tnat = resolve "metacoq.nat.type"
  let bool_type = resolve "metacoq.bool.type"
  let ttrue = resolve "metacoq.bool.true"
  let tfalse = resolve "metacoq.bool.false"
  let option_type = resolve "metacoq.option.type"
  let cSome = resolve "metacoq.option.some"
  let cNone = resolve "metacoq.option.none"

  let tZ = resolve "metacoq.Z.type"
  let cZ0 = resolve "metacoq.Z.zero"
  let cZpos = resolve "metacoq.Z.pos"
  let cZneg = resolve "metacoq.Z.neg"
  
  let tpos = resolve "metacoq.pos.type"
  let cposzero = resolve "metacoq.pos.xH"
  let cposI = resolve "metacoq.pos.xI"
  let cposO = resolve "metacoq.pos.xO"
  
  let cSome_instance = resolve "metacoq.option_instance.some"
  let cNone_instance = resolve "metacoq.option_instance.none"

  let unit_tt = resolve "metacoq.unit.intro"
  
  let tAscii = resolve "metacoq.ascii.intro"
  let tlist = resolve "metacoq.list.type"
  let c_nil = resolve "metacoq.list.nil"
  let c_cons = resolve "metacoq.list.cons"

  let prod_type = resolve "metacoq.prod.type"
  let c_pair = resolve "metacoq.prod.intro"

  let sum_type = resolve "metacoq.sum.type"
  let cInl = resolve "metacoq.sum.inl"
  let cInr = resolve "metacoq.sum.inr"

  let texistT = resolve "metacoq.sigma.intro"
  let texistT_typed_term = resolve_ref "metacoq.sigma.typed_term"

  let constr_mkApp (h, a) = Constr.mkApp (Lazy.force h, a)
  let constr_mkAppl (h, a) = Constr.mkApp (Lazy.force h, Array.map Lazy.force a)
  let prod a b = constr_mkApp (prod_type, [| a ; b |])
  let prodl a b = prod (Lazy.force a) (Lazy.force b)
  let pair a b f s = constr_mkApp (c_pair, [| a ; b ; f ; s |])
  let pairl a b f s = pair (Lazy.force a) (Lazy.force b) f s

  (* reify the constructors in Template.Ast.v, which are the building blocks of reified terms *)
  let tRelevance = ast "relevance"
  let (tRelevant,tIrrelevant) = (ast "Relevant", ast "Irrelevant")
  let taname = ast "aname"
  let tmkBindAnn = ast "mkBindAnn"
  let nAnon = ast "nAnon"
  let nNamed = ast "nNamed"
  let kVmCast = ast "VmCast"
  let kNative = ast "NativeCast"
  let kCast = ast "Cast"
  let kRevertCast = ast "RevertCast"
  let lSProp = ast "universe.lsprop"
  let lProp = ast "universe.lprop"
  let lnpe = ast "universe.lnpe"
  let lSet = ast "level.lSet"
  let tsort_family = ast "sort_family"
  let lfresh_universe = ast "fresh_universe"
  let lfresh_level = ast "fresh_level"
  let sfProp = ast "InProp"
  let sfSProp = ast "InSProp"
  let sfSet = ast "InSet"
  let sfType = ast "InType"
  let tident = ast "ident"
  let tname = ast "name"
  let tIndTy = ast "inductive"
  let tmkInd = ast "mkInd"
  let tmkdecl = ast "mkdecl"
  let (tTerm,tRel,tVar,tEvar,tSort,tCast,tProd,
       tLambda,tLetIn,tApp,tCase,tFix,tConstructor,tConst,tInd,tCoFix,tProj) =
    (ast "term", ast "tRel", ast "tVar", ast "tEvar",
     ast "tSort", ast "tCast", ast "tProd", ast "tLambda",
     ast "tLetIn", ast "tApp", ast "tCase", ast "tFix",
     ast "tConstruct", ast "tConst", ast "tInd", ast "tCoFix", ast "tProj")
  let tkername = ast "kername"
  let tmodpath = ast "modpath"
  let tMPfile = ast "MPfile"
  let tMPbound = ast "MPbound"
  let tMPdot = ast "MPdot"

  let tproplevel = ast "level.prop_level_type"
  let tlevelSProp = ast "level.lsprop"
  let tlevelProp = ast "level.lprop"
  let tlevel = ast "level.t"
  let tLevel = ast "level.Level"
  let tLevelVar = ast "level.Var"
  let tunivLe = ast "constraints.Le"
  let tunivLe0 = ast "constraints.Le0"
  let tunivLt = ast "constraints.Lt"
  let tunivEq = ast "constraints.Eq"
  let tMktUnivExprSet = ast "univexprset.mkt"
  let tBuild_Universe = ast "universe.build0"
  let tfrom_kernel_repr = ast "universe.from_kernel_repr"
  (* let tto_kernel_repr = ast "universe.to_kernel_repr" *)
  let tof_levels = ast "universe.of_levels"
  let tLevelSet_of_list = ast "universe.of_list"

  let noprop_tSet = ast "noproplevel.lSet"
  let noprop_tLevel = ast "noproplevel.Level"
  let noprop_tLevelVar = ast "noproplevel.Var"
  let univexpr_lProp = ast "univexpr.prop"
  let univexpr_npe = ast "univexpr.npe"

  (* let tunivcontext = resolve_symbol pkg_univ "universe_context" *)
  let tVariance = ast "variance.t"
  let cIrrelevant = ast "variance.Irrelevant"
  let cCovariant = ast "variance.Covariant"
  let cInvariant = ast "variance.Invariant"
  let cMonomorphic_ctx = ast "Monomorphic_ctx"
  let cPolymorphic_ctx = ast "Polymorphic_ctx"
  let tUContext = ast "UContext.t"
  let tAUContext = ast "AUContext.t"
  let tUContextmake = ast "UContext.make"
  let tAUContextmake = ast "AUContext.make"
  let tConstraintSet = ast "ConstraintSet.t_"
  let tConstraintSetempty = ast "ConstraintSet.empty"
  let tConstraintSetadd = ast "ConstraintSet.add"
  let tLevelSet = ast "LevelSet.t"
  let tmake_univ_constraint = ast "make_univ_constraint"
  let tinit_graph = ast "graph.init"
  (* FIXME this doesn't exist! *)
  let tadd_global_constraints = ast "graph.add_global_constraints"

  let (tdef,tmkdef) = (ast "def", ast "mkdef")

  let (cFinite,cCoFinite,cBiFinite) = (ast "Finite", ast "CoFinite", ast "BiFinite")
  let tone_inductive_body = ast "one_inductive_body"
  let tBuild_one_inductive_body = ast "Build_one_inductive_body"
  let tBuild_mutual_inductive_body = ast "Build_mutual_inductive_body"
  let tBuild_constant_body = ast "Build_constant_body"
  let tglobal_decl = ast "global_decl"
  let tConstantDecl = ast "ConstantDecl"
  let tInductiveDecl = ast "InductiveDecl"
  let tglobal_env = ast "global_env"

  let (tglobal_reference, tVarRef, tConstRef, tIndRef, tConstructRef) =
    (ast "global_reference", ast "VarRef", ast "ConstRef", ast "IndRef", ast "ConstructRef")

  let tcontext_decl = ast "context_decl"
  let tcontext = ast "context"

  let tMutual_inductive_entry = ast "mutual_inductive_entry"
  let tOne_inductive_entry = ast "one_inductive_entry"
  let tBuild_mutual_inductive_entry = ast "Build_mutual_inductive_entry"
  let tBuild_one_inductive_entry = ast "Build_one_inductive_entry"
  let tConstant_entry = ast "constant_entry"
  let cParameterEntry = ast "ParameterEntry"
  let cDefinitionEntry = ast "DefinitionEntry"
  let cBuild_parameter_entry = ast "Build_parameter_entry"
  let cBuild_definition_entry = ast "Build_definition_entry"
  let cMonomorphic_entry = ast "Monomorphic_entry"
  let cPolymorphic_entry = ast "Polymorphic_entry"

  let (tcbv, tcbn, thnf, tall, tlazy, tunfold) = 
    (template "cbv", template "cbn", template "hnf", template "all", template "lazy", template "unfold")


  let constr_equall h t = Constr.equal h (Lazy.force t)

end
