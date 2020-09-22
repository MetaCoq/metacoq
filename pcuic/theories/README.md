# PCUIC

## General

| File         | Description                                  |
|--------------|----------------------------------------------|
| [PCUICUtils] | General utility, not specific to type-theory |

[PCUICUtils]: PCUICUtils.v

## Syntax

| File             | Description                                               |
|------------------|-----------------------------------------------------------|
| [PCUICAst]       | Definition of the syntax of PCUIC                         |
| [PCUICAstUtils]  | Utility on syntax                                         |
| [PCUICInduction] | Induction principle on syntax                             |
| [PCUICLiftSubst] | Definition of renaming, lifting and substitution          |
| [PCUICUnivSubst] | Universe substitution (for universe polymorphism)         |
| [PCUICReflect]   | Instances of equality reflection                          |

[PCUICAst]: PCUICAst.v
[PCUICAstUtils]: PCUICAstUtils.v
[PCUICInduction]: PCUICInduction.v
[PCUICLiftSubst]: PCUICLiftSubst.v
[PCUICUnivSubst]: PCUICUnivSubst.v
[PCUICReflect]: PCUICReflect.v

## Typing and Meta Theory

| File             | Description                                               |
|------------------|-----------------------------------------------------------|
| [PCUICPretty]    |  Pretty-printing of PCUIC terms                           |
| [PCUICSize]      |  Size function on PCUIC terms                             |
| [PCUICTyping]    | Definition of reduction, conversion and typing            |
| [PCUICReduction] | Results on reduction (including parallel reduction)       |
| [PCUICPosition]  | Notions of position and stack, well-order on positions    |
| [PCUICNameless]  | Notion of terms without printing annotation               |
| [PCUICWeakeningEnv] | Weakening on environments                              |
| [PCUICClosed]    | Definition of closed terms                                |
| [PCUICSigmaCalculus] | Type preservation for σ-calculus instantiation        |
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
[PCUICSize]: PCUICSize.v
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

## Fueled type checker

| File             | Description                                               |
|------------------|-----------------------------------------------------------|
| [PCUICChecker]   | Fueled type checker for PCUIC                             |
| [PCUICRetyping]  | `type_of` function to get the type without re-checking it is well-typed |

[PCUICChecker]: PCUICChecker.v
[PCUICRetyping]: PCUICRetyping.v

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
