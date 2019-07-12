# PCUIC

*This README is WIP.*

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

## Typing

Typing in PCUIC is defined in [PCUICTyping](PCUICTyping.v), it also comes
with the definition of reduction, conversion and cumulativity.
Some results about reduction (including the definition of parallel reduction)
can be found in [PCUICReduction](PCUICReduction.v).

**(...)**

## Relation with TemplateCoq

[TemplateToPCUIC](TemplateToPCUIC.v), as the name implies, contains a
translation from TemplateCoq syntax to PCUIC syntax.
[TemplateToPCUICCorrectness](TemplateToPCUICCorrectness.v) shows that this
translation is type-preserving.

## Preliminaries for Safe Checker

In [PCUICPosition](PCUICPosition.v), we define the notion of `position` in a
`term`, as well as the notion of `stack`, how they are related and a
well-founded order on positions (in a given term).
[PCUICSafeLemmata](PCUICSafeLemmata.v) mostly contains lemmata that should be
moved, but also the definition of `welltyped` and `wellformed` which are
`Prop` variants of typing, stating that a term is well typed (or is an arity
in the case of `wellformed`). The file includes lemmata about it.
[PCUICSN](PCUICSN.v) defines the `normalisation` axiom as well-foundedness
of the co-reduction, as well as related lemmata.
