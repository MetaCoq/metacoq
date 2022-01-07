# PCUIC

The order of files here should roughly be a linearization of the dependency DAG of the library.

## General

| File                | Description
|---------------------|----------------------------------------------
| [PCUICUtils]        | Generally useful definitions and properties
| [PCUICOnOne]        | Lemmas for the OnOne relation
| [PCUICPrimitive]    | Definitions and lemmas for primitives datatypes

[PCUICUtils]: ./utils/PCUICUtils.v
[PCUICOnOne]: ./utils/PCUICOnOne.v
[PCUICPrimitive]: ./utils/PCUICPrimitive.v

## AST

| File             | Description                                  
|------------------|----------------------------------------------
| [PCUICAst]       | Definition of the Abstract Syntax Tree of PCUIC
| [PCUICAstUtils]  | General utilities on the AST
| [PCUICCases]     | Utilities for the case representation
| [PCUICInduction] | Induction principle on syntax
| [PCUICSize]      | Size of terms
| [PCUICDepth]     | Depth of terms
| [PCUICReflect]   | Decidability of equality between terms
| [PCUICContextRelations] | Helper lemmas for relations between contexts
| [PCUICPosition]  | Notions of position and stack, well-order on positions

[PCUICAst]: PCUICAst.v
[PCUICAstUtils]: ./utils/PCUICAstUtils.v
[PCUICCases]: ./Syntax/PCUICCases.v
[PCUICInduction]: ./Syntax/PCUICInduction.v
[PCUICSize]: ./utils/PCUICSize.v
[PCUICDepth]: ./Syntax/PCUICDepth.v
[PCUICReflect]: ./Syntax/PCUICReflect.v
[PCUICContextRelations]: ./Syntax/PCUICContextRelations.v
[PCUICPosition]: ./Syntax/PUICPosition.v

## Closedness, Renamings and Instantiations

| File                  | Description                                               |
|-----------------------|-----------------------------------------------------------|
| [PCUICUnivSubst]      | Substitution of universe variables (for universe polymorphism)
| [PCUICLiftSubst]      | First commutation properties for lifting and substitution
| [PCUICSigmaCalculus]  | General theory of renamings
| [PCUICClosed]         | Properties of the closedness predicate on terms
| [PCUICOnFreeVars]     | General theory of predicates on (free) variables (generalizing closedness)
| [PCUICRenameDef]      | Definition of "good" renamings
| [PCUICInstDef]        | Definition of "good" instantiations
| [PCUICContextSubst]   | Linking a context (with let-ins), an instance (reversed substitution) for its assumptions and a well-formed substitution for it

[PCUICUnivSubst]: ./Syntax/PCUICUnivSubst.v
[PCUICLiftSubst]: ./Syntax/PCUICLiftSubst.v
[PCUICSigmaCalculus]: ./PCUICSigmaCalculus.v
[PCUICClosed]: ./Syntax/PCUICClosed.v
[PCUICOnFreeVars]: ./Syntax/PCUICOnFreeVars.v
[PCUICRenameDef]: ./Syntax/PCUICRenameDef.v
[PCUICInstDef]: ./Syntax/PCUICRenameDef.v
[PCUICContextSubst]: ./PCUICContextSubst.v

## Nameless terms

| File                | Description                                               |
|---------------------|-----------------------------------------------------------|
| [PCUICNamelessDef]  | Name-removing translation
| 

[PCUICNamelessDef]: ./Syntax/NamelessDef.v

## α-equality

| File                  | Description
| ----------------------| --------------------
| [PCUICCasesContexts]  | Helper lemmas for the handling of case branche and predicate contexts


[PCUICCasesContexts]: ./PCUICCasesContexts.v

## Typing and Meta Theory

| File             | Description                                               |
|------------------|-----------------------------------------------------------|
| [PCUICTyping]    | Definition of reduction, conversion and typing            |
| [PCUICReduction] | Results on reduction (including parallel reduction)       |
| [PCUICWeakeningEnv] | Weakening on environments                              |
| [PCUICClosed]    | Definition of closed terms                                |
| [PCUICWeakening] | Weakening lemma                                           |
| [PCUICCumulativity] | Some properties on cumulativity                        |
| [PCUICEquality]  | Equality up to universes between terms                    |
| [PCUICSubstitution] | Substitution lemma                                     |
| [PCUICInversion] | Inversion lemmata on typing                               |
| [PCUICGeneration] | Admissibility lemmata  (for instance `mkApps`)           |
| [PCUICParallelReduction] | Definition of parallel reduction                  |
| [PCUICParallelReductionConfluence] | Proof of confluence of the parallel reduction |
| [PCUICConfluence] | Proof of confluence                                      |
| [PCUICContextConversion] | Proof of context conversion for typing and cumulativity  |
| [PCUICPrincipality] | Principality of typing and invariance by syntactic (in)equality |
| [PCUICUnivSubstitution] | Universe substitution lemmata                      |
| [PCUICValidity] | Every type `A` such that `Γ ⊢ t : A` is *valid*, meaning it is sorted or a well-formed arity |
| [PCUICSR] | Subject reduction |
| [PCUICCSubst]    | Definition of closed (capturing) substitution             |
| [PCUICWcbvEval] | Weak-head call-by-value evaluation strategy |

[PCUICPretty]: PCUICPretty.v
[PCUICTyping]: PCUICTyping.v
[PCUICReduction]: PCUICReduction.v
[PCUICPosition]: PCUICPosition.v
[PCUICNameless]: PCUICNameless.v
[PCUICWeakeningEnv]: PCUICWeakeningEnv.v
[PCUICClosed]: PCUICClosed.v
[PCUICSigmaCalculus]: PCUICSigmaCalculus.v
[PCUICWeakening]: PCUICWeakening.v
[PCUICCumulativity]: PCUICCumulativity.v
[PCUICEquality]: PCUICEquality.v
[PCUICSubstitution]: PCUICSubstitution.v
[PCUICInversion]: PCUICInversion.v
[PCUICGeneration]: PCUICGeneration.v
[PCUICParallelReduction]: PCUICParallelReduction.v
[PCUICParallelReductionConfluence]: PCUICParallelReductionConfluence.v
[PCUICConfluence]: PCUICConfluence.v
[PCUICContextConversion]: PCUICContextConversion.v
[PCUICPrincipality]: PCUICPrincipality.v
[PCUICUnivSubstitution]: PCUICUnivSubstitution.v
[PCUICValidity]: PCUICValidity.v
[PCUICSR]: PCUICSR.v
[PCUICCSubst]: PCUICCSubst.v
[PCUICWcbvEval]: PCUICWcbvEval.v

## Relation with Template-Coq

| File              | Description                                              |
|-------------------|----------------------------------------------------------|
| [TemplateToPCUIC] | Translation from Template-Coq syntax to PUIC syntax      |
| [TemplateToPCUICCorrectness] | Type preservation of the aformentioned translation |
| [PCUICToTemplate] | Translation from PCUIC syntax to Template-Coq syntax |
| [PCUICToTemplateCorrectness] | Type preservation of the aformentioned translation |

[TemplateToPCUIC]: TemplateToPCUIC.v
[TemplateToPCUICCorrectness]: TemplateToPCUICCorrectness.v
[PCUICToTemplate]: PCUICToTemplate.v
[PCUICToTemplateCorrectness]: PCUICToTemplateCorrectness.v

## Erasure

| File               | Description                                             |
|--------------------|---------------------------------------------------------|
| [PCUICErasedTerm]  | AST for erased terms (proofs are identified)            |
| [PCUICElimination] | Information about elimination of proofs                 |

[PCUICErasedTerm]: PCUICErasedTerm.v
[PCUICElimination]: PCUICElimination.v

## Preliminaries for Safe Checker

| File               | Description                                             |
|--------------------|---------------------------------------------------------|
| [PCUICNormal]      | (Weak-head) neutral and normal forms                    |
| [PCUICSafeLemmata] | Lemma-base for the safe checker                         |
| [PCUICSN]          | Axiom of normalisation                                  |


[PCUICNormal]: PCUICNormal.v
[PCUICSafeLemmata]: PCUICSafeLemmata.v
[PCUICSN]: PCUICSN.v

## Other

Some of the following files need to be sorted and/or explained.

| File               | Description                                             |
|--------------------|---------------------------------------------------------|
| [Extraction]       |                                                         |
| [PCUICAlpha]       | α-conversion (for printing annotations)                 |
| [PCUICLoader]      |                                                         |

[Extraction]: Extraction.v
[PCUICAlpha]: PCUICAlpha.v
[PCUICLoader]: PCUICLoader.v
