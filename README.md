MetaCoq
=======

<img src="https://github.com/MetaCoq/metacoq/raw/master/docs/assets/LOGO.png" alt="MetaCoq" width="50px"/>

[![Build Status](https://travis-ci.org/MetaCoq/metacoq.svg?branch=coq-8.9)](https://travis-ci.org/MetaCoq/metacoq)
[![Gitter](https://badges.gitter.im/coq/metacoq.svg)](https://gitter.im/coq/metacoq?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge)

MetaCoq is a project formalizing Coq in Coq and providing tools for
manipulating Coq terms and developing certified plugins
(i.e. translations, compilers or tactics) in Coq.

**Quick jump**
- [Installing](#installation-instructions)
- [Documentation](#documentation)
- [Papers](#papers)
- [Team](#team--credits)

At the center of this project is the Template-Coq quoting library for
Coq. The project currently has a single repository extending
Template-Coq with additional features:

[Template-Coq](template-coq/theories)
------------

Template-Coq is a quoting library for [Coq](http://coq.inria.fr). It
takes `Coq` terms and constructs a representation of their syntax tree as
a `Coq` inductive data type. The representation is based on the kernel's
term representation.

In addition to this representation of terms, Template Coq includes:

- Reification of the environment structures, for constant and inductive
  declarations.

- Denotation of terms and global declarations

- A monad for manipulating global declarations, calling the type
  checker, and inserting them in the global environment, in
  the style of MTac.

[Checker](checker/theories)
-------

A partial type-checker for the Calculus of Inductive Constructions,
whose extraction to ML is runable as a plugin (using command `MetaCoq
Check foo`). This checker uses _fuel_, so it must be passed a number
of maximal reduction steps to perfom when calling conversion, and is
NOT verified.

[PCUIC](pcuic/theories)
-----

PCUIC, the Polymorphic Cumulative Calculus of Inductive Constructions is
a cleaned up version of the term language of Coq and its associated
type system, equivalent to the one of Coq. This version of the
calculus has (partial) proofs of standard metatheoretical results:

- Weakening for global declarations, weakening and substitution for
  local contexts.

- Confluence of reduction using a notion of parallel reduction

- Validity, Subject Reduction and Principality.

[Safe Checker](safechecker/theories)
-----

Implementation of a fuel-free and verified reduction machine, conversion
checker and type checker for PCUIC. This relies on a postulate of 
strong normalisation of the reduction relation of PCUIC on well-typed terms.
The extracted safe checker is available in Coq through a new vernacular command:

    MetaCoq SafeCheck <term>

After importing `MetaCoq.SafeChecker.Loader`.

To roughly compare the time used to check a definition with Coq's vanila
type-checker, one can use:

    MetaCoq CoqCheck <term>

[Erasure](erasure/theories)
----------

An erasure procedure to untyped lambda-calculus accomplishing the
same as the Extraction plugin of Coq. The extracted safe erasure is
available in Coq through a new vernacular command:

    MetaCoq Erase <term>

After importing `MetaCoq.Erasure.Loader`.

[Translations](translations)
------------

Examples of translations built on top of this:

- a parametricity plugin in [translations/param_original.v](https://github.com/MetaCoq/metacoq/tree/coq-8.9/translations/param_original.v)
- a plugin to negate funext in [translations/times_bool_fun.v](https://github.com/MetaCoq/metacoq/tree/coq-8.9/translations/times_bool_fun.v)

Documentation
=============

- You may want to start with a [demo](https://github.com/MetaCoq/metacoq/tree/coq-8.9/test-suite/demo.v)
- The 8.9 branch [documentation (as light coqdoc files)](html/toc.html).
- An example Coq plugin built on the Template Monad, which can be used to
  add a constructor to any inductive type is in [test-suite/add_constructor.v](https://github.com/MetaCoq/metacoq/tree/coq-8.9/test-suite/add_constructor.v)
- The test-suite files [test-suite/erasure_test.v](https://github.com/MetaCoq/metacoq/tree/coq-8.9/test-suite/erasure_test.v)
  and [test-suite/safechecker_test.v](https://github.com/MetaCoq/metacoq/tree/coq-8.9/test-suite/safechecker_test.v) show example
  uses (and current limitations of) the verified checker and erasure.

ident vs. qualid. vs kername
---------------------------

MetaCoq uses three types convertible to `string` which have a different intended meaning:

- `ident` is the type of identifiers, they should not contains any dot.
  E.g. `nat`

- `qualid` is the type of partially qualified names.
  E.g. `Datatypes.nat`

- `kername` is the type of fully qualified names.
  E.g. `Coq.Init.Datatypes.nat`

Quoting always produce fully qualified names. On the converse, unquoting allow to
have only partially qualified names and rely on Coq to resolve them. The commands
of the TemplateMonad also allow partially qualified names.

Options
-------

`Set / Unset Strict Unquote Universe Mode`. When this mode is on,
the unquoting of a universe level fails if this level does not exists.
Otherwise the level is added to the current context. It is on by default.

There is also an "opaque" universe `fresh_universe` which is unquoted to
a fresh level when `Strict Unquote Universe Mode` is off.

Papers
======

- ["Coq Coq Codet! Towards a Verified Toolchain for Coq in
  MetaCoq"](http://www.irif.fr/~sozeau/research/publications/Coq_Coq_Codet-CoqWS19.pdf)
  Matthieu Sozeau, Simon Boulier, Yannick Forster, Nicolas Tabareau and
  Théo Winterhalter. Abstract and
  [presentation](http://www.ps.uni-saarland.de/~forster/downloads/slides-coqws19.pdf)
  given at the [Coq Workshop
  2019](https://staff.aist.go.jp/reynald.affeldt/coq2019/), September
  2019.

- ["Coq Coq Correct! Verification of Type Checking and Erasure for Coq, in Coq"](https://www.irif.fr/~sozeau/research/publications/drafts/Coq_Coq_Correct.pdf).
  Matthieu Sozeau, Simon Boulier, Yannick Forster, Nicolas Tabareau
  and Théo Winterhalter. Submitted, July 2019.
    
- [A certifying extraction with time bounds from Coq to call-by-value λ-calculus](https://www.ps.uni-saarland.de/Publications/documents/ForsterKunze_2019_Certifying-extraction.pdf).
  Yannick Forster and Fabian Kunze.
  ITP 2019.
  [Example](https://github.com/uds-psl/certifying-extraction-with-time-bounds/blob/master/Tactics/Extract.v)

- ["The MetaCoq Project"](https://www.irif.fr/~sozeau/research/publications/drafts/The_MetaCoq_Project.pdf)
  Matthieu Sozeau, Abhishek Anand, Simon Boulier, Cyril Cohen, Yannick Forster, Fabian Kunze,
  Gregory Malecha, Nicolas Tabareau and Théo Winterhalter.
  Extended version of the ITP 2018 paper. Submitted, March 2019.

  This includes a full documentation of the Template Monad.

- ["Towards Certified Meta-Programming with Typed Template-Coq"](https://hal.archives-ouvertes.fr/hal-01809681/document)
  Abhishek Anand, Simon Boulier, Cyril Cohen, Matthieu Sozeau and Nicolas Tabareau.
  ITP 2018.

- The system was presented at [Coq'PL 2018](https://popl18.sigplan.org/event/coqpl-2018-typed-template-coq)

Team & Credits
=======

<center>
<figure><img
src="https://github.com/MetaCoq/metacoq/raw/master/docs/assets/abhishek-anand.jpg"
alt="Abhishek Anand" width="150px" display="inline"/>
<img
src="https://github.com/MetaCoq/metacoq/raw/master/docs/assets/danil-annenkov.jpeg"
alt="Danil Annenkov" width="150px" display="inline"/>
<img
src="https://github.com/MetaCoq/metacoq/raw/master/docs/assets/simon-boulier.jpg"
alt="Simon Boulier" width="150px"/>
<img
src="https://github.com/MetaCoq/metacoq/raw/master/docs/assets/cyril-cohen.png"
alt="Cyril Cohen" width="150px"/>
<img
src="https://github.com/MetaCoq/metacoq/raw/master/docs/assets/yannick-forster.jpg"
alt="Yannick Forster" width="150px"/>
<img
src="https://github.com/MetaCoq/metacoq/raw/master/docs/assets/gregory-malecha.jpg"
alt="Gregory Malecha" width="150px"/>
<img
src="https://github.com/MetaCoq/metacoq/raw/master/docs/assets/matthieu-sozeau.png"
alt="Matthieu Sozeau" width="150px"/>
<img
src="https://github.com/MetaCoq/metacoq/raw/master/docs/assets/nicolas-tabareau.jpg"
alt="Nicolas Tabareau" width="150px"/>
<img
src="https://github.com/MetaCoq/metacoq/raw/master/docs/assets/theo-winterhalter.jpg"
alt="Théo Winterhalter" width="150px"/>

<figcaption>MetaCoq is developed by (left to right) 
<a href="https://github.com/aa755">Abhishek Anand</a>,
<a href="https://github.com/annenkov">Danil Annenkov</a>,
<a href="https://github.com/simonboulier">Simon Boulier</a>,
<a href="https://github.com/CohenCyril">Cyril Cohen</a>,
<a href="https://github.com/yforster">Yannick Forster</a>,
<a href="https://github.com/gmalecha">Gregory Malecha</a>,
<a href="https://github.com/mattam82">Matthieu Sozeau</a>,
<a href="https://github.com/Tabareau">Nicolas Tabareau</a> and
<a href="https://github.com/TheoWinterhalter">Théo Winterhalter</a>.
</figcaption>
</figure>
</center>

```
Copyright (c) 2014-2019 Gregory Malecha
Copyright (c) 2015-2019 Abhishek Anand, Matthieu Sozeau
Copyright (c) 2017-2019 Simon Boulier, Nicolas Tabareau, Cyril Cohen
Copyright (c) 2018-2019 Danil Annenkov, Yannick Forster, Théo Winterhalter
```

This software is distributed under the terms of the MIT license.
See [LICENSE](LICENSE) for details.

Bugs
====

Please report any bugs (or feature requests) on the github [issue tracker](https://github.com/MetaCoq/metacoq/issues).

Branches
========

The [coq-8.9](https://github.com/MetaCoq/metacoq/tree/coq-8.9) branch is
the active development branch. If possible, it's strongly recommended to use this branch.

The branches [coq-8.6](https://github.com/MetaCoq/metacoq/tree/coq-8.6),
[coq-8.7](https://github.com/MetaCoq/metacoq/tree/coq-8.7) are frozen.
[coq-8.8](https://github.com/MetaCoq/metacoq/tree/coq-8.8) is also available.

The branch [master](https://github.com/MetaCoq/metacoq/tree/master) tracks the current Coq `master` branch.
(Currently not working)

Installation instructions
=========================

Installing with OPAM
-----------------

The easiest way to get all packages is through [`opam`](http://opam.ocaml.org).

To add the Coq repository to available `opam` packages, use:

    # opam repo add coq-released https://coq.inria.fr/opam/released

Then, simply issue:

    # opam install coq-metacoq

MetaCoq is split into multiple packages that get all installed using the
`coq-metacoq` meta-package:

 - `coq-metacoq-template` for the Template Monad and quoting plugin
 - `coq-metacoq-checker` for the UNverified checker of template-coq terms
 - `coq-metacoq-pcuic` for the PCUIC development and proof of the
   Template-Coq -> PCUIC translation
 - `coq-metacoq-safechecker` for the verified checker on PCUIC terms
 - `coq-metacoq-erasure` for the verifed erasure from PCUIC to
   untyped lambda-calculus.
 - `coq-metacoq-translations` for example translations from type theory
   to type theory: e.g. variants of parametricity.

The `1.0alpha` versions of the package are for `Coq 8.8` and `Coq 8.9`.
There are also `.dev` packages available in the `extra-dev` repository
of Coq, to get those you will need to activate the following repositories:

    opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev
    opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev

Old, deprecated standalone packages `template-coq-2.1~beta` and
`template-coq-2.1~beta3` including previous versions of template-coq
and parts of the MetaCoq development are for Coq 8.8.
Package `template-coq-2.0~beta` is for Coq 8.7.
    
Setting up an `opam` switch
---------------

To setup a fresh `opam` installation, you might want to create a
"switch" (an environment of `opam` packages) for `Coq` if you don't have
one yet. You need to use **opam 2** to obtain the right version of
`Equations`.

    # opam switch create coq.8.9.1 4.07.1
    # eval $(opam env)

This creates the `coq.8.9.1` switch which initially contains only the
basic `OCaml` `4.07.1` compiler, and puts you in the right environment
(check with `ocamlc -v`).

Once in the right switch, you can install `Coq` and the `Equations` package using:

    # opam pin add coq 8.9.1
    # opam pin add coq-equations 1.2+8.9

Pinning the packages prevents opam from trying to upgrade it afterwards, in
this switch. If the commands are successful you should have `coq`
available (check with `coqc -v`). Then simply use:

    # opam install coq-metacoq

Installing from GitHub repository (for developers)
------------------------------

To get the source code:

    # git clone https://github.com/MetaCoq/metacoq.git
    # git checkout -b coq-8.9 origin/coq-8.9
    # git status

This checks that you are indeed on the `coq-8.9` branch.

You can create a [local
switch](https://opam.ocaml.org/blog/opam-20-tips/#Local-switches) for
developing using (in the root directory of the sources):

    # opam switch create . 4.07.1

Or use `opam switch link foo` to link an existing `opam` switch `foo` with
the sources directory.

Requirements
------------

To compile the library, you need:

- `Coq 8.9.1` (for the `coq-8.9` branch) or `Coq 8.8.2` (for the
  `coq-8.8` branch). Older versions of `8.9` or `8.8` might also work.
- `OCaml` (tested with `4.06.1` and `4.07.1`, beware that `OCaml 4.06.0`
  can produce linking errors on some platforms)
- [`Equations 1.2`](http://mattam82.github.io/Coq-Equations/)

When using `opam` you can get those using `opam install --deps-only .`.

You can test the installation of the packages locally using 

    # opam install .

at the root directory.

Compiling from sources
-------

To compile locally without using `opam`, use `./configure.sh local` at the root, then use:

- `make` to compile the `template-coq` plugin, the `checker`, the `pcuic`
  development and the `safechecker` and `erasure` plugins.
  You can also selectively build each target.

- `make translations` to compile the translation plugins

- `make test-suite` to compile the test suite

- `make install` to install the plugin in `Coq`'s `user-contrib` local
  library. Then the `MetaCoq` namespace can be used for `Require
  Import` statements, e.g. `From MetaCoq.Template Require Import All.`.
