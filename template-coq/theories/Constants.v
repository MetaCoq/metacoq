(* Distributed under the terms of the MIT license. *)
From MetaCoq.Utils Require Import bytestring.
From MetaCoq.Common Require Import BasicAst uGraph.
From MetaCoq.Template Require Import TemplateMonad TemplateMonad.Extractable.

(* Base types *)

Register bytestring.String.t as metacoq.string.type.
Register bytestring.String.EmptyString as metacoq.string.nil.
Register bytestring.String.String as metacoq.string.cons.

Register Stdlib.Init.Byte.byte as metacoq.byte.type.

Register Stdlib.Init.Datatypes.nat as metacoq.nat.type.
Register Stdlib.Init.Datatypes.O as metacoq.nat.zero.
Register Stdlib.Init.Datatypes.S as metacoq.nat.succ.

Register Stdlib.Init.Datatypes.bool as metacoq.bool.type.
Register Stdlib.Init.Datatypes.true as metacoq.bool.true.
Register Stdlib.Init.Datatypes.false as metacoq.bool.false.

Register Stdlib.Init.Datatypes.option as metacoq.option.type.
Register Stdlib.Init.Datatypes.None as metacoq.option.none.
Register Stdlib.Init.Datatypes.Some as metacoq.option.some.
Register MetaCoq.Template.TemplateMonad.Common.my_None as metacoq.option_instance.none.
Register MetaCoq.Template.TemplateMonad.Common.my_Some as metacoq.option_instance.some.

Register Stdlib.Init.Datatypes.list as metacoq.list.type.
Register Stdlib.Init.Datatypes.nil as metacoq.list.nil.
Register Stdlib.Init.Datatypes.cons as metacoq.list.cons.

Register Stdlib.Init.Datatypes.prod as metacoq.prod.type.
Register Stdlib.Init.Datatypes.pair as metacoq.prod.intro.

Register Stdlib.Init.Datatypes.sum as metacoq.sum.type.
Register Stdlib.Init.Datatypes.inl as metacoq.sum.inl.
Register Stdlib.Init.Datatypes.inr as metacoq.sum.inr.

Register Stdlib.Init.Datatypes.unit as metacoq.unit.type.
Register Stdlib.Init.Datatypes.tt as metacoq.unit.intro.

Register Stdlib.Init.Specif.sigT as metacoq.sigma.type.
Register Stdlib.Init.Specif.existT as metacoq.sigma.intro.
Register MetaCoq.Template.TemplateMonad.Common.existT_typed_term as metacoq.sigma.typed_term.

Register Stdlib.Numbers.BinNums.positive as metacoq.pos.type.
Register Stdlib.Numbers.BinNums.xI as metacoq.pos.xI.
Register Stdlib.Numbers.BinNums.xO as metacoq.pos.xO.
Register Stdlib.Numbers.BinNums.xH as metacoq.pos.xH.

Register Stdlib.Numbers.BinNums.Z as metacoq.Z.type.
Register Stdlib.Numbers.BinNums.Zpos as metacoq.Z.pos.
Register Stdlib.Numbers.BinNums.Zneg as metacoq.Z.neg.
Register Stdlib.Numbers.BinNums.Z0 as metacoq.Z.zero.

(* Ast *)
Register MetaCoq.Common.BasicAst.relevance as metacoq.ast.relevance.
Register MetaCoq.Common.BasicAst.Relevant as metacoq.ast.Relevant.
Register MetaCoq.Common.BasicAst.Irrelevant as metacoq.ast.Irrelevant.
Register MetaCoq.Common.BasicAst.mkBindAnn as metacoq.ast.mkBindAnn.
Register MetaCoq.Common.BasicAst.aname as metacoq.ast.aname.

Register MetaCoq.Common.BasicAst.nAnon as metacoq.ast.nAnon.
Register MetaCoq.Common.BasicAst.nNamed as metacoq.ast.nNamed.
Register MetaCoq.Common.Kernames.ident as metacoq.ast.ident.
Register MetaCoq.Common.Kernames.kername as metacoq.ast.kername.
Register MetaCoq.Common.Kernames.modpath as metacoq.ast.modpath.
Register MetaCoq.Common.Kernames.MPfile as metacoq.ast.MPfile.
Register MetaCoq.Common.Kernames.MPbound as metacoq.ast.MPbound.
Register MetaCoq.Common.Kernames.MPdot as metacoq.ast.MPdot.
Register MetaCoq.Common.Kernames.inductive as metacoq.ast.inductive.
Register MetaCoq.Common.Kernames.mkInd as metacoq.ast.mkInd.
Register MetaCoq.Common.Kernames.mkProjection as metacoq.ast.mkProjection.
Register MetaCoq.Common.Kernames.global_reference as metacoq.ast.global_reference.
Register MetaCoq.Common.Kernames.VarRef as metacoq.ast.VarRef.
Register MetaCoq.Common.Kernames.ConstRef as metacoq.ast.ConstRef.
Register MetaCoq.Common.Kernames.IndRef as metacoq.ast.IndRef.
Register MetaCoq.Common.Kernames.ConstructRef as metacoq.ast.ConstructRef.

Register MetaCoq.Common.BasicAst.name as metacoq.ast.name.
Register MetaCoq.Common.BasicAst.def as metacoq.ast.def.
Register MetaCoq.Common.BasicAst.mkdef as metacoq.ast.mkdef.
Register MetaCoq.Common.BasicAst.cast_kind as metacoq.ast.cast_kind.
Register MetaCoq.Common.BasicAst.case_info as metacoq.ast.case_info.
Register MetaCoq.Common.BasicAst.mk_case_info as metacoq.ast.mk_case_info.
Register MetaCoq.Common.BasicAst.VmCast as metacoq.ast.VmCast.
Register MetaCoq.Common.BasicAst.NativeCast as metacoq.ast.NativeCast.
Register MetaCoq.Common.BasicAst.Cast as metacoq.ast.Cast.
Register MetaCoq.Common.BasicAst.recursivity_kind as metacoq.ast.recursivity_kind.
Register MetaCoq.Common.BasicAst.Finite as metacoq.ast.Finite.
Register MetaCoq.Common.BasicAst.CoFinite as metacoq.ast.CoFinite.
Register MetaCoq.Common.BasicAst.BiFinite as metacoq.ast.BiFinite.
Register MetaCoq.Common.BasicAst.fresh_evar_id as metacoq.ast.fresh_evar_id.

(* Universes *)

Register MetaCoq.Common.Universes.allowed_eliminations as metacoq.ast.allowed_eliminations.
Register MetaCoq.Common.Universes.fresh_level as metacoq.ast.fresh_level.
Register MetaCoq.Common.Universes.fresh_universe as metacoq.ast.fresh_universe.
Register MetaCoq.Common.Universes.IntoSProp as metacoq.ast.IntoSProp.
Register MetaCoq.Common.Universes.IntoPropSProp as metacoq.ast.IntoPropSProp.
Register MetaCoq.Common.Universes.IntoSetPropSProp as metacoq.ast.IntoSetPropSProp.
Register MetaCoq.Common.Universes.IntoAny as metacoq.ast.IntoAny.
(* We convert from simple constraints to ones in Z *)
Register MetaCoq.Common.Universes.ConstraintType.Lt as metacoq.ast.constraints.Lt.
Register MetaCoq.Common.Universes.ConstraintType.Le0 as metacoq.ast.constraints.Le0.
Register MetaCoq.Common.Universes.ConstraintType.Le as metacoq.ast.constraints.Le.
Register MetaCoq.Common.Universes.ConstraintType.Eq as metacoq.ast.constraints.Eq.
Register MetaCoq.Common.Universes.Universe.t as metacoq.ast.universe.t.
Register MetaCoq.Common.Universes.Universe.make' as metacoq.ast.universe.make_of_level.
Register MetaCoq.Common.Universes.Universe.from_kernel_repr as metacoq.ast.universe.from_kernel_repr.
Register MetaCoq.Common.Universes.LevelSetProp.of_list as metacoq.ast.universe.of_list.
Register MetaCoq.Common.Universes.Level.t as metacoq.ast.level.t.
Register MetaCoq.Common.Universes.Level.level as metacoq.ast.level.Level.
Register MetaCoq.Common.Universes.PropLevel.t as metacoq.ast.level.prop_level_type.
Register MetaCoq.Common.Universes.PropLevel.lProp as metacoq.ast.level.lprop.
Register MetaCoq.Common.Universes.PropLevel.lSProp as metacoq.ast.level.lsprop.
Register MetaCoq.Common.Universes.Level.lzero as metacoq.ast.level.lzero.
Register MetaCoq.Common.Universes.Level.lvar as metacoq.ast.level.Var.

Register MetaCoq.Common.Universes.LevelExprSet.Mkt as metacoq.ast.levelexprset.mkt.
Register MetaCoq.Common.Universes.Build_nonEmptyLevelExprSet as metacoq.ast.universe.build0.
Register MetaCoq.Common.Universes.Sort.sSProp as metacoq.ast.sort.sprop.
Register MetaCoq.Common.Universes.Sort.sProp as metacoq.ast.sort.prop.
Register MetaCoq.Common.Universes.Sort.sType as metacoq.ast.sort.type.


Register MetaCoq.Common.Universes.Variance.t as metacoq.ast.variance.t.
Register MetaCoq.Common.Universes.Variance.Irrelevant as metacoq.ast.variance.Irrelevant.
Register MetaCoq.Common.Universes.Variance.Covariant as metacoq.ast.variance.Covariant.
Register MetaCoq.Common.Universes.Variance.Invariant as metacoq.ast.variance.Invariant.

Register MetaCoq.Common.Universes.universes_decl as metacoq.ast.universes_decl.
Register MetaCoq.Common.Universes.Monomorphic_ctx as metacoq.ast.Monomorphic_ctx.
Register MetaCoq.Common.Universes.Polymorphic_ctx as metacoq.ast.Polymorphic_ctx.

Register MetaCoq.Common.Universes.ConstraintSet.t_ as metacoq.ast.ConstraintSet.t_.
Register MetaCoq.Common.Universes.ConstraintSet.empty as metacoq.ast.ConstraintSet.empty.
Register MetaCoq.Common.Universes.ConstraintSet.add as metacoq.ast.ConstraintSet.add.
Register MetaCoq.Common.Universes.ConstraintSet.elements as metacoq.ast.ConstraintSet.elements.

Register MetaCoq.Common.Universes.UContext.t as metacoq.ast.UContext.t.
Register MetaCoq.Common.Universes.UContext.make as metacoq.ast.UContext.make.
Register MetaCoq.Common.Universes.AUContext.t as metacoq.ast.AUContext.t.
Register MetaCoq.Common.Universes.AUContext.make as metacoq.ast.AUContext.make.

Register MetaCoq.Common.Universes.LevelSet.t_ as metacoq.ast.LevelSet.t.
Register MetaCoq.Common.Universes.LevelSet.elements as metacoq.ast.LevelSet.elements.
Register MetaCoq.Common.Universes.UnivConstraint.make as metacoq.ast.make_univ_constraint.

Register MetaCoq.Common.uGraph.init_graph as metacoq.ast.graph.init.
(* FIXME wrong! *)
Register MetaCoq.Common.uGraph.gc_of_constraints as metacoq.ast.graph.add_global_constraints.

(* Terms *)

Register MetaCoq.Template.Ast.predicate as metacoq.ast.predicate.
Register MetaCoq.Template.Ast.mk_predicate as metacoq.ast.mk_predicate.
Register MetaCoq.Template.Ast.branch as metacoq.ast.branch.
Register MetaCoq.Template.Ast.mk_branch as metacoq.ast.mk_branch.

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
Register MetaCoq.Template.Ast.tInt as metacoq.ast.tInt.
Register MetaCoq.Template.Ast.tFloat as metacoq.ast.tFloat.
Register MetaCoq.Template.Ast.tString as metacoq.ast.tString.
Register MetaCoq.Template.Ast.tArray as metacoq.ast.tArray.

(* Local and global declarations *)
Register MetaCoq.Template.Ast.parameter_entry as metacoq.ast.parameter_entry.
Register MetaCoq.Template.Ast.Build_parameter_entry as metacoq.ast.Build_parameter_entry.
Register MetaCoq.Template.Ast.definition_entry as metacoq.ast.definition_entry.
Register MetaCoq.Template.Ast.Build_definition_entry as metacoq.ast.Build_definition_entry.

Register MetaCoq.Common.Universes.Monomorphic_entry as metacoq.ast.Monomorphic_entry.
Register MetaCoq.Common.Universes.Polymorphic_entry as metacoq.ast.Polymorphic_entry.

Register MetaCoq.Template.Ast.constant_entry as metacoq.ast.constant_entry.
Register MetaCoq.Template.Ast.ParameterEntry as metacoq.ast.ParameterEntry.
Register MetaCoq.Template.Ast.DefinitionEntry as metacoq.ast.DefinitionEntry.

Register MetaCoq.Template.Ast.one_inductive_entry as metacoq.ast.one_inductive_entry.
Register MetaCoq.Template.Ast.Build_one_inductive_entry as metacoq.ast.Build_one_inductive_entry.
Register MetaCoq.Template.Ast.mutual_inductive_entry as metacoq.ast.mutual_inductive_entry.
Register MetaCoq.Template.Ast.Build_mutual_inductive_entry as metacoq.ast.Build_mutual_inductive_entry.

Register MetaCoq.Common.BasicAst.context_decl as metacoq.ast.context_decl.
Register MetaCoq.Common.BasicAst.mkdecl as metacoq.ast.mkdecl.
Register MetaCoq.Template.Ast.Env.context as metacoq.ast.context.

Register MetaCoq.Template.Ast.Env.constructor_body as metacoq.ast.constructor_body.
Register MetaCoq.Template.Ast.Env.Build_constructor_body as metacoq.ast.Build_constructor_body.
Register MetaCoq.Template.Ast.Env.Build_projection_body as metacoq.ast.Build_projection_body.
Register MetaCoq.Template.Ast.Env.projection_body as metacoq.ast.projection_body.
Register MetaCoq.Template.Ast.Env.one_inductive_body as metacoq.ast.one_inductive_body.
Register MetaCoq.Template.Ast.Env.Build_one_inductive_body as metacoq.ast.Build_one_inductive_body.
Register MetaCoq.Template.Ast.Env.mutual_inductive_body as metacoq.ast.mutual_inductive_body.
Register MetaCoq.Template.Ast.Env.Build_mutual_inductive_body as metacoq.ast.Build_mutual_inductive_body.
Register MetaCoq.Template.Ast.Env.constant_body as metacoq.ast.constant_body.
Register MetaCoq.Template.Ast.Env.Build_constant_body as metacoq.ast.Build_constant_body.

Register MetaCoq.Template.Ast.Env.global_decl as metacoq.ast.global_decl.
Register MetaCoq.Template.Ast.Env.ConstantDecl as metacoq.ast.ConstantDecl.
Register MetaCoq.Template.Ast.Env.InductiveDecl as metacoq.ast.InductiveDecl.
Register MetaCoq.Common.Environment.Retroknowledge.mk_retroknowledge as metacoq.ast.mk_retroknowledge.
Register MetaCoq.Template.Ast.Env.mk_global_env as metacoq.ast.Build_global_env.
Register MetaCoq.Template.Ast.Env.global_env as metacoq.ast.global_env.
Register MetaCoq.Template.Ast.Env.global_env_ext as metacoq.ast.global_env_ext.
Register MetaCoq.Template.Ast.Env.program as metacoq.ast.program.

(* Template monad *)

Register MetaCoq.Template.TemplateMonad.Common.cbv as metacoq.template.cbv.
Register MetaCoq.Template.TemplateMonad.Common.cbn as metacoq.template.cbn.
Register MetaCoq.Template.TemplateMonad.Common.hnf as metacoq.template.hnf.
Register MetaCoq.Template.TemplateMonad.Common.all as metacoq.template.all.
Register MetaCoq.Template.TemplateMonad.Common.lazy as metacoq.template.lazy.
Register MetaCoq.Template.TemplateMonad.Common.unfold as metacoq.template.unfold.

Register MetaCoq.Template.TemplateMonad.Common.local as metacoq.template.hints.local.
Register MetaCoq.Template.TemplateMonad.Common.export as metacoq.template.hints.export.
Register MetaCoq.Template.TemplateMonad.Common.global as metacoq.template.hints.global.


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
Register MetaCoq.Template.TemplateMonad.Core.tmLocateModule as metacoq.templatemonad.prop.tmLocateModule.
Register MetaCoq.Template.TemplateMonad.Core.tmLocateModType as metacoq.templatemonad.prop.tmLocateModType.
Register MetaCoq.Template.TemplateMonad.Core.tmCurrentModPath as metacoq.templatemonad.prop.tmCurrentModPath.

Register MetaCoq.Template.TemplateMonad.Core.tmQuote as metacoq.templatemonad.prop.tmQuote.
Register MetaCoq.Template.TemplateMonad.Core.tmQuoteRec as metacoq.templatemonad.prop.tmQuoteRec.
Register MetaCoq.Template.TemplateMonad.Core.tmQuoteRecTransp as metacoq.templatemonad.prop.tmQuoteRecTransp.
Register MetaCoq.Template.TemplateMonad.Core.tmQuoteInductive as metacoq.templatemonad.prop.tmQuoteInductive.
Register MetaCoq.Template.TemplateMonad.Core.tmQuoteConstant as metacoq.templatemonad.prop.tmQuoteConstant.
Register MetaCoq.Template.TemplateMonad.Core.tmQuoteUniverses as metacoq.templatemonad.prop.tmQuoteUniverses.
Register MetaCoq.Template.TemplateMonad.Core.tmQuoteModule as metacoq.templatemonad.prop.tmQuoteModule.
Register MetaCoq.Template.TemplateMonad.Core.tmQuoteModFunctor as metacoq.templatemonad.prop.tmQuoteModFunctor.
Register MetaCoq.Template.TemplateMonad.Core.tmQuoteModType as metacoq.templatemonad.prop.tmQuoteModType.

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
Register MetaCoq.Template.TemplateMonad.Extractable.tmLocateModule as metacoq.templatemonad.type.tmLocateModule.
Register MetaCoq.Template.TemplateMonad.Extractable.tmLocateModType as metacoq.templatemonad.type.tmLocateModType.
Register MetaCoq.Template.TemplateMonad.Extractable.tmCurrentModPath as metacoq.templatemonad.type.tmCurrentModPath.
Register MetaCoq.Template.TemplateMonad.Extractable.tmQuoteInductive as metacoq.templatemonad.type.tmQuoteInductive.
Register MetaCoq.Template.TemplateMonad.Extractable.tmQuoteUniverses as metacoq.templatemonad.type.tmQuoteUniverses.
Register MetaCoq.Template.TemplateMonad.Extractable.tmQuoteConstant as metacoq.templatemonad.type.tmQuoteConstant.
Register MetaCoq.Template.TemplateMonad.Extractable.tmQuoteModule as metacoq.templatemonad.type.tmQuoteModule.
Register MetaCoq.Template.TemplateMonad.Extractable.tmQuoteModFunctor as metacoq.templatemonad.type.tmQuoteModFunctor.
Register MetaCoq.Template.TemplateMonad.Extractable.tmQuoteModType as metacoq.templatemonad.type.tmQuoteModType.
Register MetaCoq.Template.TemplateMonad.Extractable.tmInductive as metacoq.templatemonad.type.tmInductive.
Register MetaCoq.Template.TemplateMonad.Extractable.tmInferInstance as metacoq.templatemonad.type.tmInferInstance.
Register MetaCoq.Template.TemplateMonad.Extractable.tmExistingInstance as metacoq.templatemonad.type.tmExistingInstance.
