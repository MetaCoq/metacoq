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
PCUICSigmaCalculus.v |
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
PCUICReduction.v | needs a bit of cleaning up to present the congruence lemmas properly
PCUICTyping.v |
PCUICGuardCondition.v |
PCUICGlobalEnv.v | should this be integrated to EnvironmentTyping.v? Nothing specific to typing here
PCUICGeneration.v | very short, should it be merged into Typing.v?
PCUICInversion.v | how much is this redundant with the equivalence bidirectional <-> undirected? should we mention this is a consequence of confluence?
PCUICEqualityDec.v | does this belong here or in the safe-checker?
PCUICNormal.v |
PCUICSN.v | try and minimize dependencies?
PCUICSafeLemmata.v | should these lemmas be moved to other files where they belong?
PCUICSubstitution.v | there seems to be a lot of mess in this file, does all of it belong here?
PCUICContextReduction.v |
PCUICCumulativitySpec.v |
PCUICCumulativity.v | maybe change the name to be clearer?
PCUICWfUniverses.v |
PCUICParallelReduction.v
PCUICParallelReductionConfluence.v | should we change rho’s name? it is very uninformative as is
PCUICConfluence.v | also contains properties relating eq_term and reduction (eq_term is a simulation for confluence), should we split that apart?
PCUICRedTypeIrrelevance.v |
PCUICWellScopedCumulativity.v | the name `equality` is very confusing here imho
PCUICContextConversion.v |
PCUICConversion.v | There’s a lot here, putting forward the interesting bits or splitting the file might make sense
PCUICContexts.v | Not sure what the coherence is here
PCUICArities.v | There’s not much about arities here, maybe could be integrated into PCUICSpine (and maybe other places)?
PCUICSpine.v | Not sure what’s happening here
PCUICInductives.v |
PCUICValidity.v |
PCUICInductiveInversion.v |
PCUICAlpha.v |
PCUICSR.v |
PCUICCSubst.v |
PCUICWcbvEval.v |
PCUICCanonicity.v | Does not prove canonicity at all… Should we still prove a form of progress here? Use other forms that are proven elsewhere more or less implicitely?
PCUICCumulProp.v |
PCUICElimination.v |
PCUICConvCumInversion.v | This looks like something we should do otherwise using the relations we already have
PCUICPrincipality.v | Should we keep this now that we have the proof using bidirectional typing?
TemplateToPCUIC.v |
TemplateToPCUICCorrectness.v |
TemplateToPCUICWcbvEval.v |
PCUICToTemplate.v |
PCUICToTemplateCorrectness.v |
PCUICExpandLets.v |
PCUICExpandLetsCorrectness.v |
Bidirectional/BDEnvironmentTyping.v | should ideally be integrated into EnvironmentTyping
Bidirectional/BDTyping.v
Bidirectional/BDToPCUIC.v
Bidirectional/BDFromPCUIC.v
Bidirectional/BDUnique.v
Bidirectional/BDStrengthening.v

# All.v

# To do separate extraction of the files, not working currently
# due to ssreflect's definition of [over].
# Extraction.v
