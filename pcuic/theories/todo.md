Done
----------------------------------------------------------------

File | Issues
-----| -----------------------------
Syntax/PCUICTactics.v | should this be in Syntax or in utils?
utils/PCUICUtils.v | nothing to do here, move to template utils
utils/PCUICOnOne.v | same, move to template utils (merge with All_Forall?)
utils/PCUICPrimitive.v |
PCUICAst.v |
utils/PCUICSize.v | merge with AstUtils?
Syntax/PCUICInduction.v | merge with AstUtils?
Syntax/PCUICDepth.v | merge with AstUtils?
utils/PCUICAstUtils.v |
utils/PCUICPretty.v | merge with AstUtils? Why do we have print_term and string_of_term?
Syntax/PCUICCases.v |
Syntax/PCUICPosition.v | Equality should depend on position, not the other way around?
Syntax/PCUICReflect.v |
Syntax/PCUICNamelessDef.v | subsumed by PCUICAlpha, to be removed
Syntax/PCUICClosed.v | what is the point of this given that we have OnFreeVars? Should we try and merge them?
Syntax/PCUICOnFreeVars.v |
Syntax/PCUICRenameDef.v | this is only 60 lines, and has a weird dependency on typing for something in "syntax", we should probably do something (at least change the name). Also, there is a concurrent notion in PCUICParallelReduction.
Syntax/PCUICInstDef.v | similar to PCUICRenameDef.v
Syntax/PCUICLiftSubst.v | how much of this should go into files 
Syntax/PCUICContextRelation.v | made this a part of BasicAst, where context_decl is first defined
Syntax/PCUICUnivSubst.v | 
PCUICContextSubst.v | Is this worth keeping?
PCUICCasesContexts.v | similar to PCUICContextSubst.v
PCUICEquality.v |
Conversion/PCUICNamelessConv.v | subsumed by PCUICAlpha, to be removed
Typing/PCUICNamelessTyp.v | subsumed by PCUICAlpha, to be removed
Conversion/PCUICRenameConv.v |
Conversion/PCUICInstConv.v |
Conversion/PCUICWeakeningEnvConv.v | should contain the right lemmas which are for now in PCUICWeakeningEnvTyp.v
Conversion/PCUICUnivSubstitutionConv.v | same as for PCUICWeakeningEnvConv.v
Conversion/PCUICWeakeningConv.v | 
Conversion/PCUICOnFreeVarsConv.v | should be renamed/moved into other files
Conversion/PCUICClosedConv.v | should be renamed/moves into other files
Typing/PCUICRenameTyp.v |
Typing/PCUICInstTyp.v |
Typing/PCUICWeakeningEnvTyp.v |
Typing/PCUICWeakeningTyp.v |
Typing/PCUICUnivSubstitutionTyp.v |
Typing/PCUICClosedTyp.v | this is not about stability of typing, does putting it with the others still make sense?
Typing/PCUICContextConversionTyp.v | there is no PCUICContextConversionConv counterpart, this is weird

PCUICReduction.v
PCUICTyping.v
PCUICGuardCondition.v
PCUICGlobalEnv.v
PCUICInversion.v
PCUICNormal.v
PCUICEqualityDec.v
PCUICSubstitution.v
PCUICContextReduction.v
PCUICCumulativity.v
PCUICCumulativitySpec.v
PCUICParallelReduction.v
PCUICParallelReductionConfluence.v
PCUICConfluence.v
PCUICWellScopedCumulativity.v
PCUICContextConversion.v
PCUICConversion.v
PCUICConvCumInversion.v
PCUICRedTypeIrrelevance.v
PCUICGeneration.v
PCUICAlpha.v
PCUICContexts.v
PCUICArities.v
PCUICWfUniverses.v
PCUICSpine.v
PCUICInductives.v

PCUICValidity.v
PCUICInductiveInversion.v
PCUICSR.v
PCUICCanonicity.v

PCUICCSubst.v
PCUICWcbvEval.v
PCUICCumulProp.v
PCUICElimination.v
PCUICSN.v
PCUICPrincipality.v
PCUICSigmaCalculus.v

PCUICSafeLemmata.v

TemplateToPCUIC.v
TemplateToPCUICCorrectness.v
TemplateToPCUICWcbvEval.v
PCUICToTemplate.v
PCUICToTemplateCorrectness.v
PCUICExpandLets.v
PCUICExpandLetsCorrectness.v

Bidirectional/BDEnvironmentTyping.v
Bidirectional/BDTyping.v
Bidirectional/BDToPCUIC.v
Bidirectional/BDFromPCUIC.v
Bidirectional/BDUnique.v
Bidirectional/BDStrengthening.v

# All.v

# To do separate extraction of the files, not working currently
# due to ssreflect's definition of [over].
# Extraction.v
