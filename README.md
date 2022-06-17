# MetaCoq

<p align="center">
<img src="https://raw.githubusercontent.com/MetaCoq/metacoq.github.io/master/assets/LOGO.png" alt="MetaCoq" width="50px"/>
</p>

[![Build status](https://github.com/MetaCoq/metacoq/actions/workflows/build.yml/badge.svg?branch=coq-8.16)](https://github.com/MetaCoq/metacoq/actions) [![MetaCoq Chat](https://img.shields.io/badge/zulip-join_chat-brightgreen.svg)](https://coq.zulipchat.com)

MetaCoq is a project formalizing Coq in Coq and providing tools for
manipulating Coq terms and developing certified plugins
(i.e. translations, compilers or tactics) in Coq.


**Quick jump**
- [Getting started](#getting-started)
- [Installation instructions](#installation-instructions)
- [Documentation](#documentation)
- [Overview of the project](#overview-of-the-project)
- [Papers](#papers)
- [Team & Credits](#team--credits)
- [Bugs](#bugs)



## Getting started

- You may want to start with a [demo](https://github.com/MetaCoq/metacoq/tree/coq-8.16/examples/demo.v).

- The current branch [documentation (as light coqdoc files)](https://metacoq.github.io/html/toc.html).

- The [overview](#overview-of-the-project) of the different parts of the project.



## Installation instructions

See [INSTALL.md](https://github.com/MetaCoq/metacoq/tree/coq-8.16/INSTALL.md)



## Documentation

See [DOC.md](https://github.com/MetaCoq/metacoq/tree/coq-8.16/DOC.md)



## Overview of the project

At the center of this project is the Template-Coq quoting library for
Coq. The project currently has a single repository extending
Template-Coq with additional features. Each extension is in dedicated folder.

### [Template-Coq](https://github.com/MetaCoq/metacoq/tree/coq-8.16/template-coq)

Template-Coq is a quoting library for [Coq](http://coq.inria.fr). It
takes `Coq` terms and constructs a representation of their syntax tree as
an inductive data type. The representation is based on the kernel's
term representation.

After importing `MetaCoq.Template.Loader` there are commands `MetaCoq Test Quote t.`, 
`MetaCoq Quote Definition name := (t).` and `MetaCoq Quote Recursively Definition name := (t).` as 
well as a tactic `quote_term t k`,
where in all cases `t` is a term and `k` a continuation tactic.

In addition to this representation of terms, Template Coq includes:

- Reification of the environment structures, for constant and inductive
  declarations.

- Denotation of terms and global declarations

- A monad for manipulating global declarations, calling the type
  checker, and inserting them in the global environment, in
  the style of MTac. Monadic programs `p : TemplateMonad A` can be run using `MetaCoq Run p`.

- A formalisation of the typing rules reflecting the ones of Coq, not covering eta-expansion and template polymorphism.

### [PCUIC](https://github.com/MetaCoq/metacoq/tree/coq-8.11/pcuic)

PCUIC, the Polymorphic Cumulative Calculus of Inductive Constructions is
a cleaned up version of the term language of Coq and its associated
type system, shown equivalent to the one of Coq. This version of the
calculus has proofs of standard metatheoretical results:

- Weakening for global declarations, weakening and substitution for
  local contexts.

- Confluence of reduction using a notion of parallel reduction

- Context conversion and validity of typing.

- Subject Reduction (case/cofix reduction excluded)

- Principality: every typeable term has a smallest type.

- Elimination restrictions: the elimination restrictions ensure
  that singleton elimination (from Prop to Type) is only allowed
  on singleton inductives in Prop.

- Canonicity: The weak head normal form of erms of inductive type is a constructor application.

- Consistency under the assumption of strong normalization
  
- Weak call-by-value standardization: Normal forms of terms of first-order inductive type
can be found via weak call-by-value evaluation.

### [Safe Checker](https://github.com/MetaCoq/metacoq/tree/coq-8.16/safechecker)

Implementation of a fuel-free and verified reduction machine, conversion
checker and type checker for PCUIC. This relies on a postulate of
strong normalization of the reduction relation of PCUIC on well-typed terms.
The extracted safe checker is available in Coq through a new vernacular command:

    MetaCoq SafeCheck <term>

After importing `MetaCoq.SafeChecker.Loader`.

To roughly compare the time used to check a definition with Coq's vanilla
type-checker, one can use:

    MetaCoq CoqCheck <term>

### [Erasure](https://github.com/MetaCoq/metacoq/tree/coq-8.16/erasure)

An erasure procedure to untyped lambda-calculus accomplishing the
same as the type and proof erasure phase of the Extraction plugin of Coq.
The extracted safe erasure is available in Coq through a new vernacular command:

    MetaCoq Erase <term>

After importing `MetaCoq.Erasure.Loader`.


### [Translations](https://github.com/MetaCoq/metacoq/tree/coq-8.16/translations)

Examples of translations built on top of this:

- a parametricity plugin in [translations/param_original.v](https://github.com/MetaCoq/metacoq/tree/coq-8.16/translations/param_original.v)

- a plugin to negate funext in [translations/times_bool_fun.v](https://github.com/MetaCoq/metacoq/tree/coq-8.16/translations/times_bool_fun.v)


### Examples

- An example Coq plugin built on the Template Monad, which can be used to
  add a constructor to any inductive type is in [examples/add_constructor.v](https://github.com/MetaCoq/metacoq/tree/coq-8.16/examples/add_constructor.v)

- The test-suite files [test-suite/erasure_test.v](https://github.com/MetaCoq/metacoq/tree/coq-8.16/test-suite/erasure_test.v)
  and [test-suite/safechecker_test.v](https://github.com/MetaCoq/metacoq/tree/coq-8.16/test-suite/safechecker_test.v) show example
  uses (and current limitations of) the verified checker and erasure.

## Papers

- ["Coq Coq Correct! Verification of Type Checking and Erasure for Coq, in Coq"](https://metacoq.github.io/coqcoqcorrect)
  Matthieu Sozeau, Simon Boulier, Yannick Forster, Nicolas Tabareau
  and Théo Winterhalter. POPL 2020, New Orleans.

- ["Coq Coq Codet! Towards a Verified Toolchain for Coq in
  MetaCoq"](http://www.irif.fr/~sozeau/research/publications/Coq_Coq_Codet-CoqWS19.pdf)
  Matthieu Sozeau, Simon Boulier, Yannick Forster, Nicolas Tabareau and
  Théo Winterhalter. Abstract and
  [presentation](http://www.ps.uni-saarland.de/~forster/downloads/slides-coqws19.pdf)
  given at the [Coq Workshop
  2019](https://staff.aist.go.jp/reynald.affeldt/coq2019/), September
  2019.

- ["The MetaCoq Project"](https://www.irif.fr/~sozeau/research/publications/drafts/The_MetaCoq_Project.pdf)
  Matthieu Sozeau, Abhishek Anand, Simon Boulier, Cyril Cohen, Yannick Forster, Fabian Kunze,
  Gregory Malecha, Nicolas Tabareau and Théo Winterhalter. JAR, February 2020.
  Extended version of the ITP 2018 paper.

  This includes a full documentation of the Template Monad and the typing rules of PCUIC.

- [A certifying extraction with time bounds from Coq to call-by-value λ-calculus](https://www.ps.uni-saarland.de/Publications/documents/ForsterKunze_2019_Certifying-extraction.pdf).
  Yannick Forster and Fabian Kunze.
  ITP 2019.
  [Example](https://github.com/uds-psl/certifying-extraction-with-time-bounds/blob/master/Tactics/Extract.v)

- ["Towards Certified Meta-Programming with Typed Template-Coq"](https://hal.archives-ouvertes.fr/hal-01809681/document)
  Abhishek Anand, Simon Boulier, Cyril Cohen, Matthieu Sozeau and Nicolas Tabareau.
  ITP 2018.

- The system was presented at [Coq'PL 2018](https://popl18.sigplan.org/event/coqpl-2018-typed-template-coq)



## Team & Credits

<p align="center">
<img
src="https://github.com/MetaCoq/metacoq.github.io/raw/master/assets/abhishek-anand.jpg"
alt="Abhishek Anand" width="150px"/>
<img
src="https://github.com/MetaCoq/metacoq.github.io/raw/master/assets/danil-annenkov.jpeg"
alt="Danil Annenkov" width="150px"/>
<img
src="https://github.com/MetaCoq/metacoq.github.io/raw/master/assets/simon-boulier.jpg"
alt="Simon Boulier" width="150px"/><br/>
<img
src="https://github.com/MetaCoq/metacoq.github.io/raw/master/assets/cyril-cohen.png"
alt="Cyril Cohen" width="150px"/>
<img
src="https://github.com/MetaCoq/metacoq.github.io/raw/master/assets/yannick-forster.jpg"
alt="Yannick Forster" width="150px"/>
<img
src="https://github.com/MetaCoq/metacoq.github.io/raw/master/assets/gregory-malecha.jpg"
alt="Gregory Malecha" width="150px"/><br/>
<img
src="https://github.com/MetaCoq/metacoq.github.io/raw/master/assets/matthieu-sozeau.png"
alt="Matthieu Sozeau" width="150px"/>
<img
src="https://github.com/MetaCoq/metacoq.github.io/raw/master/assets/nicolas-tabareau.jpg"
alt="Nicolas Tabareau" width="150px"/>
<img
src="https://github.com/MetaCoq/metacoq.github.io/raw/master/assets/theo-winterhalter.jpg"
alt="Théo Winterhalter" width="150px"/>

MetaCoq is developed by (left to right)
<a href="https://github.com/aa755">Abhishek Anand</a>,
<a href="https://github.com/annenkov">Danil Annenkov</a>,
<a href="https://github.com/SimonBoulier">Simon Boulier</a>,
<a href="https://github.com/CohenCyril">Cyril Cohen</a>,
<a href="https://github.com/yforster">Yannick Forster</a>,
<a href="https://github.com/gmalecha">Gregory Malecha</a>,
<a href="https://github.com/mattam82">Matthieu Sozeau</a>,
<a href="https://github.com/Tabareau">Nicolas Tabareau</a> and
<a href="https://github.com/TheoWinterhalter">Théo Winterhalter</a>.
</p>


```
Copyright (c) 2014-2022 Gregory Malecha
Copyright (c) 2015-2022 Abhishek Anand, Matthieu Sozeau
Copyright (c) 2017-2022 Simon Boulier, Nicolas Tabareau, Cyril Cohen
Copyright (c) 2018-2022 Danil Annenkov, Yannick Forster, Théo Winterhalter
```

This software is distributed under the terms of the MIT license.
See [LICENSE](https://github.com/MetaCoq/metacoq/tree/coq-8.16/LICENSE) for details.



## Bugs

Please report any bugs or feature requests on the github [issue tracker](https://github.com/MetaCoq/metacoq/issues).
