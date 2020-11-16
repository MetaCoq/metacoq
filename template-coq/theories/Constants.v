(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import BasicAst uGraph TemplateMonad
     TemplateMonad.Extractable.

(* Base types *)

Register Coq.Strings.String.string as metacoq.string.type.
Register Coq.Strings.String.EmptyString as metacoq.string.nil.
Register Coq.Strings.String.String as metacoq.string.cons.

Register Coq.Strings.Ascii.ascii as metacoq.ascii.type.
Register Coq.Strings.Ascii.Ascii as metacoq.ascii.intro.

Register Coq.Init.Datatypes.nat as metacoq.nat.type.
Register Coq.Init.Datatypes.O as metacoq.nat.zero.
Register Coq.Init.Datatypes.S as metacoq.nat.succ.

Register Coq.Init.Datatypes.bool as metacoq.bool.type.
Register Coq.Init.Datatypes.true as metacoq.bool.true.
Register Coq.Init.Datatypes.false as metacoq.bool.false.

Register Coq.Init.Datatypes.option as metacoq.option.type.
Register Coq.Init.Datatypes.None as metacoq.option.none.
Register Coq.Init.Datatypes.Some as metacoq.option.some.
Register MetaCoq.Template.TemplateMonad.Common.my_None as metacoq.option_instance.none.
Register MetaCoq.Template.TemplateMonad.Common.my_Some as metacoq.option_instance.some.

Register Coq.Init.Datatypes.list as metacoq.list.type.
Register Coq.Init.Datatypes.nil as metacoq.list.nil.
Register Coq.Init.Datatypes.cons as metacoq.list.cons.

Register Coq.Init.Datatypes.prod as metacoq.prod.type.
Register Coq.Init.Datatypes.pair as metacoq.prod.intro.

Register Coq.Init.Datatypes.sum as metacoq.sum.type.
Register Coq.Init.Datatypes.inl as metacoq.sum.inl.
Register Coq.Init.Datatypes.inr as metacoq.sum.inr.

Register Coq.Init.Datatypes.unit as metacoq.unit.type.
Register Coq.Init.Datatypes.tt as metacoq.unit.intro.

Register Coq.Init.Specif.sigT as metacoq.sigma.type.
Register Coq.Init.Specif.existT as metacoq.sigma.intro.
Register MetaCoq.Template.TemplateMonad.Common.existT_typed_term as metacoq.sigma.typed_term.

Register Coq.Numbers.BinNums.positive as metacoq.pos.type.
Register Coq.Numbers.BinNums.xI as metacoq.pos.xI.
Register Coq.Numbers.BinNums.xO as metacoq.pos.xO.
Register Coq.Numbers.BinNums.xH as metacoq.pos.xH.

Register Coq.Numbers.BinNums.Z as metacoq.Z.type.
Register Coq.Numbers.BinNums.Zpos as metacoq.Z.pos.
Register Coq.Numbers.BinNums.Zneg as metacoq.Z.neg.
Register Coq.Numbers.BinNums.Z0 as metacoq.Z.zero.

(* Ast *)
Register MetaCoq.Template.BasicAst.relevance as metacoq.ast.relevance.
Register MetaCoq.Template.BasicAst.Relevant as metacoq.ast.Relevant.
Register MetaCoq.Template.BasicAst.Irrelevant as metacoq.ast.Irrelevant.
Register MetaCoq.Template.BasicAst.mkBindAnn as metacoq.ast.mkBindAnn.
Register MetaCoq.Template.BasicAst.aname as metacoq.ast.aname.

Register MetaCoq.Template.BasicAst.nAnon as metacoq.ast.nAnon.
Register MetaCoq.Template.BasicAst.nNamed as metacoq.ast.nNamed.
Register MetaCoq.Template.BasicAst.ident as metacoq.ast.ident.
Register MetaCoq.Template.BasicAst.kername as metacoq.ast.kername.
Register MetaCoq.Template.BasicAst.modpath as metacoq.ast.modpath.
Register MetaCoq.Template.BasicAst.MPfile as metacoq.ast.MPfile.
Register MetaCoq.Template.BasicAst.MPbound as metacoq.ast.MPbound.
Register MetaCoq.Template.BasicAst.MPdot as metacoq.ast.MPdot.
Register MetaCoq.Template.BasicAst.name as metacoq.ast.name.
Register MetaCoq.Template.BasicAst.inductive as metacoq.ast.inductive.
Register MetaCoq.Template.BasicAst.mkInd as metacoq.ast.mkInd.
Register MetaCoq.Template.BasicAst.def as metacoq.ast.def.
Register MetaCoq.Template.BasicAst.mkdef as metacoq.ast.mkdef.
Register MetaCoq.Template.BasicAst.cast_kind as metacoq.ast.cast_kind.
Register MetaCoq.Template.BasicAst.VmCast as metacoq.ast.VmCast.
Register MetaCoq.Template.BasicAst.NativeCast as metacoq.ast.NativeCast.
Register MetaCoq.Template.BasicAst.Cast as metacoq.ast.Cast.
Register MetaCoq.Template.BasicAst.RevertCast as metacoq.ast.RevertCast.
Register MetaCoq.Template.BasicAst.recursivity_kind as metacoq.ast.recursivity_kind.
Register MetaCoq.Template.BasicAst.Finite as metacoq.ast.Finite.
Register MetaCoq.Template.BasicAst.CoFinite as metacoq.ast.CoFinite.
Register MetaCoq.Template.BasicAst.BiFinite as metacoq.ast.BiFinite.
Register MetaCoq.Template.BasicAst.global_reference as metacoq.ast.global_reference.
Register MetaCoq.Template.BasicAst.VarRef as metacoq.ast.VarRef.
Register MetaCoq.Template.BasicAst.ConstRef as metacoq.ast.ConstRef.
Register MetaCoq.Template.BasicAst.IndRef as metacoq.ast.IndRef.
Register MetaCoq.Template.BasicAst.ConstructRef as metacoq.ast.ConstructRef.

(* Universes *)

Register MetaCoq.Template.Universes.sort_family as metacoq.ast.sort_family.
Register MetaCoq.Template.Universes.fresh_level as metacoq.ast.fresh_level.
Register MetaCoq.Template.Universes.fresh_universe as metacoq.ast.fresh_universe.
Register MetaCoq.Template.Universes.InProp as metacoq.ast.InProp.
Register MetaCoq.Template.Universes.InSet as metacoq.ast.InSet.
Register MetaCoq.Template.Universes.InType as metacoq.ast.InType.
(* We convert from simple constraints to ones in Z *)
Register MetaCoq.Template.Universes.ConstraintType.Lt as metacoq.ast.constraints.Lt.
Register MetaCoq.Template.Universes.ConstraintType.Le0 as metacoq.ast.constraints.Le0.
Register MetaCoq.Template.Universes.ConstraintType.Le as metacoq.ast.constraints.Le.
Register MetaCoq.Template.Universes.ConstraintType.Eq as metacoq.ast.constraints.Eq.
Register MetaCoq.Template.Universes.Universe.from_kernel_repr as metacoq.ast.universe.from_kernel_repr.
Register MetaCoq.Template.Universes.Universe.of_levels as metacoq.ast.universe.of_levels.
Register MetaCoq.Template.Universes.LevelSetProp.of_list as metacoq.ast.universe.of_list.
Register MetaCoq.Template.Universes.Level.t as metacoq.ast.level.t.
Register MetaCoq.Template.Universes.Level.Level as metacoq.ast.level.Level.
Register MetaCoq.Template.Universes.PropLevel.t as metacoq.ast.level.prop_level_type.
Register MetaCoq.Template.Universes.PropLevel.lProp as metacoq.ast.level.lprop.
Register MetaCoq.Template.Universes.PropLevel.lSProp as metacoq.ast.level.lsprop.
Register MetaCoq.Template.Universes.Level.lSet as metacoq.ast.level.lSet.
Register MetaCoq.Template.Universes.Level.Var as metacoq.ast.level.Var.
(* FIXME*)
Register MetaCoq.Template.Universes.Universe.lType as metacoq.ast.univexpr.npe.

Register MetaCoq.Template.Universes.UnivExprSet.Mkt as metacoq.ast.univexprset.mkt.
Register MetaCoq.Template.Universes.Universe.Build_t0 as metacoq.ast.universe.build0.
Register MetaCoq.Template.Universes.Universe.lSProp as metacoq.ast.universe.lsprop.
Register MetaCoq.Template.Universes.Universe.lProp as metacoq.ast.universe.lprop.
Register MetaCoq.Template.Universes.Universe.lType as metacoq.ast.universe.lnpe.


Register MetaCoq.Template.Universes.Variance.t as metacoq.ast.variance.t.
Register MetaCoq.Template.Universes.Variance.Irrelevant as metacoq.ast.variance.Irrelevant.
Register MetaCoq.Template.Universes.Variance.Covariant as metacoq.ast.variance.Covariant.
Register MetaCoq.Template.Universes.Variance.Invariant as metacoq.ast.variance.Invariant.

Register MetaCoq.Template.Universes.universes_decl as metacoq.ast.universes_decl.
Register MetaCoq.Template.Universes.Monomorphic_ctx as metacoq.ast.Monomorphic_ctx.
Register MetaCoq.Template.Universes.Polymorphic_ctx as metacoq.ast.Polymorphic_ctx.

Register MetaCoq.Template.Universes.ConstraintSet.t_ as metacoq.ast.ConstraintSet.t_.
Register MetaCoq.Template.Universes.ConstraintSet.empty as metacoq.ast.ConstraintSet.empty.
Register MetaCoq.Template.Universes.ConstraintSet.add as metacoq.ast.ConstraintSet.add.

Register MetaCoq.Template.Universes.UContext.t as metacoq.ast.UContext.t.
Register MetaCoq.Template.Universes.UContext.make as metacoq.ast.UContext.make.
Register MetaCoq.Template.Universes.AUContext.t as metacoq.ast.AUContext.t.
Register MetaCoq.Template.Universes.AUContext.make as metacoq.ast.AUContext.make.

Register MetaCoq.Template.Universes.LevelSet.t_ as metacoq.ast.LevelSet.t.
Register MetaCoq.Template.Universes.UnivConstraint.make as metacoq.ast.make_univ_constraint.

Register MetaCoq.Template.common.uGraph.init_graph as metacoq.ast.graph.init.
(* FIXME wrong! *)
Register MetaCoq.Template.common.uGraph.gc_of_constraints as metacoq.ast.graph.add_global_constraints.

(* Terms *)

Register MetaCoq.Template.Ast.term as metacoq.ast.term.
Register MetaCoq.Template.Ast.tRel as metacoq.ast.tRel.
Register MetaCoq.Template.Ast.tVar as metacoq.ast.tVar.
Register MetaCoq.Template.Ast.tEvar as metacoq.ast.tEvar.
Register MetaCoq.Template.Ast.tSort as metacoq.ast.tSort.
Register MetaCoq.Template.Ast.tCast as metacoq.ast.tCast.
Register MetaCoq.Template.Ast.tProd as metacoq.ast.tProd.
Register MetaCoq.Template.Ast.tLambda as metacoq.ast.tLambda.
Register MetaCoq.Template.Ast.tLetIn as metacoq.ast.tLetIn.
Register MetaCoq.Template.Ast.tApp as metacoq.ast.tApp.
Register MetaCoq.Template.Ast.tConst as metacoq.ast.tConst.
Register MetaCoq.Template.Ast.tInd as metacoq.ast.tInd.
Register MetaCoq.Template.Ast.tConstruct as metacoq.ast.tConstruct.
Register MetaCoq.Template.Ast.tCase as metacoq.ast.tCase.
Register MetaCoq.Template.Ast.tProj as metacoq.ast.tProj.
Register MetaCoq.Template.Ast.tFix as metacoq.ast.tFix.
Register MetaCoq.Template.Ast.tCoFix as metacoq.ast.tCoFix.

(* Local and global declarations *)
Register MetaCoq.Template.Ast.parameter_entry as metacoq.ast.parameter_entry.
Register MetaCoq.Template.Ast.Build_parameter_entry as metacoq.ast.Build_parameter_entry.
Register MetaCoq.Template.Ast.definition_entry as metacoq.ast.definition_entry.
Register MetaCoq.Template.Ast.Build_definition_entry as metacoq.ast.Build_definition_entry.

Register MetaCoq.Template.Universes.Monomorphic_entry as metacoq.ast.Monomorphic_entry.
Register MetaCoq.Template.Universes.Polymorphic_entry as metacoq.ast.Polymorphic_entry.

Register MetaCoq.Template.Ast.constant_entry as metacoq.ast.constant_entry.
Register MetaCoq.Template.Ast.ParameterEntry as metacoq.ast.ParameterEntry.
Register MetaCoq.Template.Ast.DefinitionEntry as metacoq.ast.DefinitionEntry.

Register MetaCoq.Template.Ast.one_inductive_entry as metacoq.ast.one_inductive_entry.
Register MetaCoq.Template.Ast.Build_one_inductive_entry as metacoq.ast.Build_one_inductive_entry.
Register MetaCoq.Template.Ast.mutual_inductive_entry as metacoq.ast.mutual_inductive_entry.
Register MetaCoq.Template.Ast.Build_mutual_inductive_entry as metacoq.ast.Build_mutual_inductive_entry.

Register MetaCoq.Template.Ast.context_decl as metacoq.ast.context_decl.
Register MetaCoq.Template.Ast.mkdecl as metacoq.ast.mkdecl.
Register MetaCoq.Template.Ast.context as metacoq.ast.context.

Register MetaCoq.Template.Ast.one_inductive_body as metacoq.ast.one_inductive_body.
Register MetaCoq.Template.Ast.Build_one_inductive_body as metacoq.ast.Build_one_inductive_body.
Register MetaCoq.Template.Ast.mutual_inductive_body as metacoq.ast.mutual_inductive_body.
Register MetaCoq.Template.Ast.Build_mutual_inductive_body as metacoq.ast.Build_mutual_inductive_body.
Register MetaCoq.Template.Ast.constant_body as metacoq.ast.constant_body.
Register MetaCoq.Template.Ast.Build_constant_body as metacoq.ast.Build_constant_body.

Register MetaCoq.Template.Ast.global_decl as metacoq.ast.global_decl.
Register MetaCoq.Template.Ast.ConstantDecl as metacoq.ast.ConstantDecl.
Register MetaCoq.Template.Ast.InductiveDecl as metacoq.ast.InductiveDecl.
Register MetaCoq.Template.Ast.global_env as metacoq.ast.global_env.
Register MetaCoq.Template.Ast.global_env_ext as metacoq.ast.global_env_ext.
Register MetaCoq.Template.Ast.program as metacoq.ast.program.

(* Template monad *)

Register MetaCoq.Template.TemplateMonad.Common.cbv as metacoq.template.cbv.
Register MetaCoq.Template.TemplateMonad.Common.cbn as metacoq.template.cbn.
Register MetaCoq.Template.TemplateMonad.Common.hnf as metacoq.template.hnf.
Register MetaCoq.Template.TemplateMonad.Common.all as metacoq.template.all.
Register MetaCoq.Template.TemplateMonad.Common.lazy as metacoq.template.lazy.
Register MetaCoq.Template.TemplateMonad.Common.unfold as metacoq.template.unfold.

(* Prop *)
Register MetaCoq.Template.TemplateMonad.Core.tmReturn as metacoq.templatemonad.prop.tmReturn.
Register MetaCoq.Template.TemplateMonad.Core.tmBind as metacoq.templatemonad.prop.tmBind.
Register MetaCoq.Template.TemplateMonad.Core.tmPrint as metacoq.templatemonad.prop.tmPrint.
Register MetaCoq.Template.TemplateMonad.Core.tmMsg as metacoq.templatemonad.prop.tmMsg.
Register MetaCoq.Template.TemplateMonad.Core.tmFail as metacoq.templatemonad.prop.tmFail.
Register MetaCoq.Template.TemplateMonad.Core.tmEval as metacoq.templatemonad.prop.tmEval.
Register MetaCoq.Template.TemplateMonad.Core.tmVariable as metacoq.templatemonad.prop.tmVariable.
Register MetaCoq.Template.TemplateMonad.Core.tmLemma as metacoq.templatemonad.prop.tmLemma.
Register MetaCoq.Template.TemplateMonad.Core.tmDefinitionRed_ as metacoq.templatemonad.prop.tmDefinitionRed_.
Register MetaCoq.Template.TemplateMonad.Core.tmAxiomRed as metacoq.templatemonad.prop.tmAxiomRed.
Register MetaCoq.Template.TemplateMonad.Core.tmMkDefinition as metacoq.templatemonad.prop.tmMkDefinition.
Register MetaCoq.Template.TemplateMonad.Core.tmMkInductive as metacoq.templatemonad.prop.tmMkInductive.
Register MetaCoq.Template.TemplateMonad.Core.tmFreshName as metacoq.templatemonad.prop.tmFreshName.
Register MetaCoq.Template.TemplateMonad.Core.tmLocate as metacoq.templatemonad.prop.tmLocate.
Register MetaCoq.Template.TemplateMonad.Core.tmCurrentModPath as metacoq.templatemonad.prop.tmCurrentModPath.

Register MetaCoq.Template.TemplateMonad.Core.tmQuote as metacoq.templatemonad.prop.tmQuote.
Register MetaCoq.Template.TemplateMonad.Core.tmQuoteRec as metacoq.templatemonad.prop.tmQuoteRec.
Register MetaCoq.Template.TemplateMonad.Core.tmQuoteRecTransp as metacoq.templatemonad.prop.tmQuoteRecTransp.
Register MetaCoq.Template.TemplateMonad.Core.tmQuoteInductive as metacoq.templatemonad.prop.tmQuoteInductive.
Register MetaCoq.Template.TemplateMonad.Core.tmQuoteConstant as metacoq.templatemonad.prop.tmQuoteConstant.
Register MetaCoq.Template.TemplateMonad.Core.tmQuoteUniverses as metacoq.templatemonad.prop.tmQuoteUniverses.

Register MetaCoq.Template.TemplateMonad.Core.tmUnquote as metacoq.templatemonad.prop.tmUnquote.
Register MetaCoq.Template.TemplateMonad.Core.tmUnquoteTyped as metacoq.templatemonad.prop.tmUnquoteTyped.

Register MetaCoq.Template.TemplateMonad.Core.tmInferInstance as metacoq.templatemonad.prop.tmInferInstance.
Register MetaCoq.Template.TemplateMonad.Core.tmExistingInstance as metacoq.templatemonad.prop.tmExistingInstance.

Register MetaCoq.Template.TemplateMonad.Core.tmTestQuote as metacoq.templatemonad.prop.tmTestQuote.
Register MetaCoq.Template.TemplateMonad.Core.tmTestUnquote as metacoq.templatemonad.prop.tmTestUnquote.
Register MetaCoq.Template.TemplateMonad.Core.tmQuoteDefinition as metacoq.templatemonad.prop.tmQuoteDefinition.
Register MetaCoq.Template.TemplateMonad.Core.tmQuoteDefinitionRed as metacoq.templatemonad.prop.tmQuoteDefinitionRed.
Register MetaCoq.Template.TemplateMonad.Core.tmQuoteRecDefinition as metacoq.templatemonad.prop.tmQuoteRecDefinition.


(* Type *)
Register MetaCoq.Template.TemplateMonad.Extractable.tmReturn as metacoq.templatemonad.type.tmReturn.
Register MetaCoq.Template.TemplateMonad.Extractable.tmBind as metacoq.templatemonad.type.tmBind.
Register MetaCoq.Template.TemplateMonad.Extractable.tmPrint as metacoq.templatemonad.type.tmPrint.
Register MetaCoq.Template.TemplateMonad.Extractable.tmMsg as metacoq.templatemonad.type.tmMsg.
Register MetaCoq.Template.TemplateMonad.Extractable.tmFail as metacoq.templatemonad.type.tmFail.
Register MetaCoq.Template.TemplateMonad.Extractable.tmEval as metacoq.templatemonad.type.tmEval.
Register MetaCoq.Template.TemplateMonad.Extractable.tmDefinition_ as metacoq.templatemonad.type.tmDefinition_.
Register MetaCoq.Template.TemplateMonad.Extractable.tmAxiom as metacoq.templatemonad.type.tmAxiom.
Register MetaCoq.Template.TemplateMonad.Extractable.tmLemma as metacoq.templatemonad.type.tmLemma.
Register MetaCoq.Template.TemplateMonad.Extractable.tmFreshName as metacoq.templatemonad.type.tmFreshName.
Register MetaCoq.Template.TemplateMonad.Extractable.tmLocate as metacoq.templatemonad.type.tmLocate.
Register MetaCoq.Template.TemplateMonad.Extractable.tmCurrentModPath as metacoq.templatemonad.type.tmCurrentModPath.
Register MetaCoq.Template.TemplateMonad.Extractable.tmQuoteInductive as metacoq.templatemonad.type.tmQuoteInductive.
Register MetaCoq.Template.TemplateMonad.Extractable.tmQuoteUniverses as metacoq.templatemonad.type.tmQuoteUniverses.
Register MetaCoq.Template.TemplateMonad.Extractable.tmQuoteConstant as metacoq.templatemonad.type.tmQuoteConstant.
Register MetaCoq.Template.TemplateMonad.Extractable.tmInductive as metacoq.templatemonad.type.tmInductive.
Register MetaCoq.Template.TemplateMonad.Extractable.tmInferInstance as metacoq.templatemonad.type.tmInferInstance.
Register MetaCoq.Template.TemplateMonad.Extractable.tmExistingInstance as metacoq.templatemonad.type.tmExistingInstance.
