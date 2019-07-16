# PCUIC

## Syntax

[PCUICAst](PCUICAst.v) defines the syntax of terms of PCUIC: `term`.
Utility functions on this syntax can be found in
[PCUICAstUtils](PCUICAstUtils.v), while [PCUICInduction](PCUICInduction)
provides induction principles on the syntax, while taking care of special
constructors like `tCase` (pattern-maching), `tFix` (fixed points) and
`tCoFix` (co-fixed points) which take lists of terms as arguments.
[PCUICLiftSubst](PCUICLiftSubst.v) defines renaming, lifting and susbtitution.
[PCUICUnivSubst](PCUICUnivSubst.v) defines universe substitution (for universe
polymorphism).
[PCUICReflect](PCUICReflect.v) contains the definition of the `ReflectEq` type
class, coming with boolean equality `eqb` which reflects equality, and give
many instances of that class.

## Typing and Meta Theory

Typing in PCUIC is defined in [PCUICTyping](PCUICTyping.v), it also comes
with the definition of reduction, conversion and cumulativity.
Some results about reduction (including the definition of parallel reduction)
can be found in [PCUICReduction](PCUICReduction.v).
In [PCUICPosition](PCUICPosition.v), we define the notion of `position` in a
`term`, as well as the notion of `stack`, how they are related and a
well-founded order on positions (in a given term).
In [PCUICNameless](PCUICNameless.v) we define a notion of `nameless` terms
(without any pretty-printing annotations) and the `nl` function to remove
such names in a term.
Weakening on environments is done in [PCUICWeakeningEnv](PCUICWeakeningEnv.v).
The notion of closed terms is defined in [PCUICClosed](PCUICClosed.v).
In [PCUICSigmaCalculus](PCUICSigmaCalculus.v) we show type
preservation for σ-calculus instantiation.
Then [PCUICWeakening](PCUICWeakening.v) contains the weakening lemma.
Some properties on cumulativity are proven in
[PCUICCumulativity](PCUICCumulativity.v), it also includes some other
properties about `eq_term` but they can mainly be found in
[PCUICEquality](PCUICEquality.v).
[PCUICSubstitution](PCUICSubstitution.v) contains the substitution lemma.
All inversion lemmata on typing are in [PCUICInversion](PCUICInversion.v).
[PCUICGeneration](PCUICGeneration.v) on the other hand is about admissibility
lemmata on typing, for instance typing of n-ary application `mkApps`.
[PCUICParallelReduction](PCUICParallelReduction.v) and
[PCUICParallelReductionConfluence](PCUICParallelReductionConfluence.v) have
self-explanatory names, they define parallel reduction and show it is confluent
as a stepping stone to prove confluence of the "usual" reduction in
[PCUICConfluence](PCUICConfluence.v).
We prove principality (if a term has two types, it can be typed with a subtype
of both) in [PCUICPrincipality](PCUICPrincipality.v).
[PCUICUnivSubstitution](PCUICUnivSubstitution.v) contains more universe
substitution lemmata.
[PCUICValidity](PCUICValidity.v) allows us to show that every type `A`
such that `Γ ⊢ t : A` is *valid*, meaning it is sorted or a well-formed
arity.
Subject reduction is addressed in [PCUICSR](PCUICSR.v).
[PCUICWcbvEval](PCUICWcbvEval.v) defines the weak head call by value
evaluation strategy.

[PCUICMetaTheory](PCUICMetaTheory.v) sums up the meta-theory?
(probably outdated)

## Fueled type checker

[PCUICChecker](PCUICChecker.v) contains a fueled type checker for PCUIC
whose completeness can be found in
[PCUICCheckerCompleteness](PCUICCheckerCompleteness.v).
[PCUICRetyping](PCUICRetyping.v) provides a `type_of` function to get the
type of well-typed expression, it doesn't check again that the term is
well-typed, so it can go faster.

## Relation with TemplateCoq

[TemplateToPCUIC](TemplateToPCUIC.v), as the name implies, contains a
translation from TemplateCoq syntax to PCUIC syntax.
[TemplateToPCUICCorrectness](TemplateToPCUICCorrectness.v) shows that this
translation is type-preserving.

## Erasure

[PCUICErasedTerm](PCUICErasedTerm.v) contains the AST for the erased terms
(proofs are identified).
[PCUICElimination](PCUICElimination.v) defines information about elimination
of proofs.

## Preliminaries for Safe Checker

In [PCUICNormal](PCUICNormal.v) we define the notion of (weak head) neutral and
normal terms.
[PCUICSafeLemmata](PCUICSafeLemmata.v) mostly contains lemmata that should be
moved, but also the definition of `welltyped` and `wellformed` which are
`Prop` variants of typing, stating that a term is well typed (or is an arity
in the case of `wellformed`). The file includes lemmata about it.
[PCUICSN](PCUICSN.v) defines the `normalisation` axiom as well-foundedness
of the co-reduction, as well as related lemmata.
