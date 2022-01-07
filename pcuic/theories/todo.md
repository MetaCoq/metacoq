Done
----------------------------------------------------------------

File | Issues
-----| -----------------------------
theories/utils/PCUICUtils.v | nothing to do here, move to template utils
theories/utils/PCUICOnOne.v | same, move to template utils (merge with All_Forall?)
theories/utils/PCUICPrimitive.v |
theories/PCUICAst.v |
theories/utils/PCUICSize.v | merge with AstUtils?
theories/Syntax/PCUICInduction.v | merge with AstUtils?
theories/Syntax/PCUICDepth.v | merge with AstUtils?
theories/utils/PCUICAstUtils.v |
theories/utils/PCUICPretty.v | merge with AstUtils? Why do we have print_term and string_of_term?
theories/Syntax/PCUICCases.v |
theories/Syntax/PCUICPosition.v | Equality should depend on position, not the other way around?
theories/Syntax/PCUICReflect.v |
theories/Syntax/PCUICNamelessDef.v | create a Nameless folder?
theories/Syntax/PCUICClosed.v | what is the point of this given that we have OnFreeVars? Should we try and merge them?
theories/Syntax/PCUICOnFreeVars.v |
theories/Syntax/PCUICRenameDef.v | this is only 60 lines, and has a weird dependency on typing for something in "syntax", we should probably do something (at least change the name). Also, there is a concurrent notion in PCUICParallelReduction.
theories/Syntax/PCUICInstDef.v | similar to PCUICRenameDef.v
theories/Syntax/PCUICLiftSubst.v | how much of this should go into files 
theories/Syntax/PCUICContextRelation.v | made this a part of BasicAst, where context_decl is first defined
theories/Syntax/PCUICUnivSubst.v | 
theories/PCUICContextSubst.v | Is this worth keeping?
theories/PCUICCasesContexts.v | similar to PCUICContextSubst.v


theories/Conversion/PCUICNamelessConv.v
theories/Conversion/PCUICRenameConv.v
theories/Conversion/PCUICInstConv.v
theories/Conversion/PCUICWeakeningEnvConv.v
theories/Conversion/PCUICUnivSubstitutionConv.v
theories/Conversion/PCUICWeakeningConv.v
theories/Conversion/PCUICClosedConv.v
theories/Conversion/PCUICOnFreeVarsConv.v

theories/Typing/PCUICNamelessTyp.v
theories/Typing/PCUICRenameTyp.v
theories/Typing/PCUICInstTyp.v
theories/Typing/PCUICWeakeningEnvTyp.v
theories/Typing/PCUICWeakeningTyp.v
theories/Typing/PCUICUnivSubstitutionTyp.v
theories/Typing/PCUICClosedTyp.v
theories/Typing/PCUICContextConversionTyp.v

theories/PCUICReduction.v
theories/PCUICTyping.v
theories/PCUICGuardCondition.v
theories/PCUICGlobalEnv.v
theories/PCUICInversion.v
theories/PCUICNormal.v
theories/PCUICEquality.v
theories/PCUICEqualityDec.v
theories/PCUICSubstitution.v
theories/PCUICContextReduction.v
theories/PCUICCumulativity.v
theories/PCUICCumulativitySpec.v
theories/PCUICParallelReduction.v
theories/PCUICParallelReductionConfluence.v
theories/PCUICConfluence.v
theories/PCUICWellScopedCumulativity.v
theories/PCUICContextConversion.v
theories/PCUICConversion.v
theories/PCUICConvCumInversion.v
theories/PCUICRedTypeIrrelevance.v
theories/PCUICGeneration.v
theories/PCUICAlpha.v
theories/PCUICContexts.v
theories/PCUICArities.v
theories/PCUICWfUniverses.v
theories/PCUICSpine.v
theories/PCUICInductives.v

theories/PCUICValidity.v
theories/PCUICInductiveInversion.v
theories/PCUICSR.v
theories/PCUICCanonicity.v

theories/PCUICCSubst.v
theories/PCUICWcbvEval.v
theories/PCUICCumulProp.v
theories/PCUICElimination.v
theories/PCUICSN.v
theories/PCUICPrincipality.v
theories/PCUICSigmaCalculus.v

theories/PCUICSafeLemmata.v

theories/TemplateToPCUIC.v
theories/TemplateToPCUICCorrectness.v
theories/TemplateToPCUICWcbvEval.v
theories/PCUICToTemplate.v
theories/PCUICToTemplateCorrectness.v
theories/PCUICExpandLets.v
theories/PCUICExpandLetsCorrectness.v

theories/Bidirectional/BDEnvironmentTyping.v
theories/Bidirectional/BDTyping.v
theories/Bidirectional/BDToPCUIC.v
theories/Bidirectional/BDFromPCUIC.v
theories/Bidirectional/BDUnique.v
theories/Bidirectional/BDStrengthening.v

# theories/All.v

# To do separate extraction of the files, not working currently
# due to ssreflect's definition of [over].
# theories/Extraction.v
