# Translation from ETT to ITT and then to TemplateCoq

### Prerequisites

**TemplateCoq**
In order to build this project you need to build TemplateCoq. In order to do so, just `make` in the parent repository.

**Equations**
You also need the Equations plugin to build it. See [here](http://mattam82.github.io/Coq-Equations/) for how to install it.


To build the project, you only need to `make`.

### Detail of the files

- `SAst.v` describes common syntax (in a similar fashion to `Ast.v` of
   `theories`) to both ETT and ITT.
- `SLiftSubst.v` describes meta-operations on the syntax (namely lifting and substitution).
- `SCommon.v` states common definitions like context.

- `ITyping.v` contains the typing rules of ITT.
- `XTyping.v` contains the typing rules of ETT.

- `ITypingLemmata.v` contains lemmata regarding typing in ITT.
- `ITypingLemmata.v` contains inversion and admissibility lemmata in ITT.
- `PackLifts.v` contains the necessary lifts to deal with packing.

- `Translation.v` contains the translation itself and the necessary
  lemmata.
- `Reduction.v` is about a notion of reduction to simplify the output
  of the translation (thus reducing the use of axioms when they aren't
  needed).
- `Quotes.v` contains quotations of terms for the final translation.
- `FinalTranslation.v` containes the transaltion from ITT to
  TemplateCoq (meaning we can reify terms of ITT).
- `Example.v` contains an example of the two translations chained to
  build a Coq term from an ETT derivation.
