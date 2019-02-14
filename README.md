MetaCoq
=======

<img src="https://github.com/MetaCoq/metacoq/raw/master/docs/assets/LOGO.png" alt="MetaCoq" width="50px"/>

[![Build Status](https://travis-ci.org/MetaCoq/metacoq.svg?branch=coq-8.9)](https://travis-ci.org/MetaCoq/metacoq)
[![Gitter](https://img.shields.io/gitter/room/nwjs/nw.js.svg)](https://gitter.im/coq/Template-Coq)

MetaCoq is a project formalizing Coq in Coq and providing tools for
manipulating Coq terms and developing certified plugins
(i.e. translations, compilers or tactics) in Coq.

At the center of this project is the Template-Coq quoting library for
Coq. The project currently has a single repository extending
Template-Coq with additional features:

Template-Coq
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
  the stype of MTac.
  
Checker
-------
  
- A partial type-checker for the Calculus of Inductive Constructions,
  runable as a plugin.

PCUIC and Extraction
--------------------

- A cleaned up version of the term language of Coq and its associated
  type system, equivalent to the one of Coq.
  
- An extraction procedure to untyped lambda-calculus accomplishing the
  same as the Extraction plugin of Coq

Translations
------------

- Example of plugin built on top of this.


Branches
========

The [coq-8.9](https://github.com/MetaCoq/metacoq/tree/coq-8.9) branch is the active development branch. If possible, it's strongly recommended to use this branch.

The branches [coq-8.6](https://github.com/MetaCoq/metacoq/tree/coq-8.6),
[coq-8.7](https://github.com/MetaCoq/metacoq/tree/coq-8.7) and
[coq-8.8](https://github.com/MetaCoq/metacoq/tree/coq-8.8)
are stable but may not receive new features.

The branch [master](https://github.com/MetaCoq/metacoq/tree/master) tracks the current Coq `master` branch.


Documentation
=============

You may want to start by a demo: [demo.v](https://github.com/MetaCoq/metacoq/tree/coq-8.9/test-suite/demo.v)

The 8.7 branch [documentation (coqdoc files)](html/Template.All.html)
and pretty-printed HTML versions of the [translations](html/translations) are available.

ident vs. qualid. vs kername
---------------------------

TemplateCoq uses three types convertible to `string` which have a different intended meaning:

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

`Set / Unset Strict Unquote Universe Mode`. When this mode is on (on by default):

- the unquoting of a universe level fails if this level does not exists

- the unquoting of a sort which is an empty list fails

Otherwise:

- the level is added to the current context

- or a fresh level is added.

Examples of plugins
-------------------

- a plugin to add a constructor in [test-suite/add_constructor.v](https://github.com/MetaCoq/metacoq/tree/coq-8.9/test-suite/add_constructor.v)
- a parametricity plugin in [translations/param_original.v](https://github.com/MetaCoq/metacoq/tree/coq-8.9/translations/param_original.v)
- a plugin to negate funext in [translations/times_bool_fun.v](https://github.com/MetaCoq/metacoq/tree/coq-8.9/translations/times_bool_fun.v)


Papers
======

- ["The MetaCoq Project"](https://www.irif.fr/~sozeau/research/publications/drafts/The_MetaCoq_Project.pdf)
  Matthieu Sozeau, Abhishek Anand, Simon Boulier, Cyril Cohen, Yannick Forster, Fabian Kunze,
  Gregory Malecha, Nicolas Tabareau, Théo Winterhalter.
  Extended version of the ITP 2018 paper. Submitted.

  This includes a full documentation of the Template Monad.

- ["Towards Certified Meta-Programming with Typed Template-Coq"](https://hal.archives-ouvertes.fr/hal-01809681/document)
  Abhishek Anand, Simon Boulier, Cyril Cohen, Matthieu Sozeau and Nicolas Tabareau.
  ITP 2018.

- The system was presented at [Coq'PL 2018](https://popl18.sigplan.org/event/coqpl-2018-typed-template-coq)

Credits
=======

Template-Coq was originally developed by
[Gregory Malecha](https://github.com/gmalecha), and is now developed by
[Abhishek Anand](https://github.com/aa755), [Simon
Boulier](https://github.com/simonboulier) and [Matthieu
Sozeau](https://github.com/mattam82).

Contributors include [Yannick Forster](https://github.com/yforster),
[Cyril Cohen](https://github.com/CohenCyril) and [Nicolas
Tabareau](https://github.com/Tabareau).

Copyright (c) 2014-2018 Gregory Malecha\
Copyright (c) 2015-2018 Abhishek Anand, Matthieu Sozeau\
Copyright (c) 2017-2018 Simon Boulier, Nicolas Tabareau, Cyril Cohen

This software is distributed under the terms of the MIT license.
See [LICENSE](LICENSE) for details.


Installation instructions
=========================

Install from GitHub repository
------------------------------

To get the source code:

    # git clone https://github.com/MetaCoq/metacoq.git
    # git checkout -b coq-8.9 origin/coq-8.9
    # git status
    
Check that you are indeed on the `coq-8.9` branch.

Requirements
------------

To compile the library, you need:

- `Coq 8.8.2` (older versions of `8.8` might also work)
- `OCaml` (tested with `4.04.1`, beware that `OCaml 4.06.0` can 
  produce linking errors on some platforms)
- [`Equations 1.2`](http://mattam82.github.io/Coq-Equations/)

Requirements through opam
-------------------------

The easiest way to get all is through [opam](http://opam.ocaml.org):

You might want to create a "switch" (an environment of `opam` packages) for `Coq` if
<<<<<<< HEAD
you don't have one yet. You need to use **opam 2** to obtain the right version of `Equations`.

    # opam switch create coq.8.8.2 4.04.1 
    # eval $(opam env)
    
This creates the `coq.8.8.2` switch which initially contains only the
=======
you don't have one yet:
    
    # opam switch -A 4.04.1 coq.8.9
    # eval `opam config env`
    
This creates the `coq.8.9` switch which initially contains only the
>>>>>>> Update Readme to 8.9
basic `OCaml` `4.04.1` compiler, and puts you in the right environment
(check with `ocamlc -v`).

Once in the right switch, you can install `Coq` and the `Equations` package using:
    
<<<<<<< HEAD
    # opam pin add coq 8.8.2
    # opam pin add coq-equations 1.2+8.8
=======
    # opam pin add coq 8.9
>>>>>>> Update Readme to 8.9
    
Pinning the packages prevents opam from trying to upgrade it afterwards, in
this switch. If the commands are successful you should have `coq`
available (check with `coqc -v`).

Compile
-------

Once in the right environment, Use:

- `make` to compile the template-coq plugin, the checker and the
  extraction plugin.

- `make translations` to compile the translation plugins

- `make test-suite` to compile the test suite

- `make install` to install the plugin in `coq`'s user-contrib local
  library. Then the `Template` namespace can be used for `Require
  Import` statements, e.g. `From Template Require Import All.`.

Install with OPAM
-----------------
Alternatively, you can install MetaCoq through Opam.

Add the Coq repository:

    opam repo add coq-released https://coq.inria.fr/opam/released

and run:

    opam install coq-template-coq

To get beta versions of Coq, you might want to activate the repository:

    opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev

Packages `2.1~beta` and `2.1~beta3` are for Coq 8.8. Package `2.0~beta` is for Coq 8.7.

How to Use
==========

Check `test-suite/demo.v` for examples.

Unless you installed the library (with `make install`), you must add the theories directory to
your Coq load path with the prefix Template. This can be done on the
command line by adding:

```
coqc ... -R <path-to-theories> -as Template ...
```
or inside a running Coq session with:

```
Add LoadPath "<path-to-theories>" as Template.
```

Because paths are often not portable the later is not recommended.

If you use Emacs and Proof General, you can set up a .dir-locals.el with the
following code:
```
((coq-mode . ((coq-load-path . (
 (nonrec "<absolute-path-to-theories>" "Template")
 )))))
```
As long as you don't check this file into a repository things should work out
well.

Bugs
====

Please report any bugs (or feature requests) on the github [issue tracker](https://github.com/MetaCoq/metacoq/issues)
