Template Coq
============

<img src="https://github.com/Template-Coq/template-coq/raw/master/docs/assets/LOGO_TYPO.png" alt="Template Coq" width="10px"/>

[![Build Status](https://travis-ci.org/Template-Coq/template-coq.svg?branch=coq-8.7)](https://travis-ci.org/Template-Coq/template-coq)
[![Gitter](https://img.shields.io/gitter/room/nwjs/nw.js.svg)](https://gitter.im/coq/Template-Coq)

Template Coq is a quoting library for [Coq](http://coq.inria.fr). It
takes `Coq` terms and constructs a representation of their syntax tree as
a `Coq` inductive data type. The representation is based on the kernel's
term representation.

In addition to this representation of terms, Template Coq includes:

- Reification of the environment structures, for constant and inductive
  declarations.

- Denotation of terms and global declarations

The branch `master` is stable and works with Coq 8.6, an opam package is
available.

The [coq-8.7](https://github.com/Template-Coq/template-coq/tree/coq-8.7),
branch is in development and contains additional features:

- Complete reification and denotation of CIC terms, including universes

- A monad for manipulating global declarations, calling the type
  checker, and inserting them in the global environment, in
  the stype of MetaCoq/MTac.
  
- A partial type-checker for the Calculus of Inductive Constructions,
  runable as a plugin.
  
- Example plugins built on top of this.

Documentation
=============

The 8.7 branch [documentation (coqdoc files)](html/Template.All.html)
and pretty-printed HTML versions of the [translations](html/translations) are available.

Papers
======

- The system was presented at 
  [Coq'PL 2018](https://popl18.sigplan.org/event/coqpl-2018-typed-template-coq)

- ["Towards Certified Meta-Programming with Typed Template-Coq"](https://github.com/Template-Coq/template-coq/raw/master/docs/submission.pdf)
  A. Anand, S. Boulier, C. Cohen, M. Sozeau and N. Tabareau.
  Submitted.

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

Branches
========

- The current stable branch is
  [master](https://github.com/Template-Coq/template-coq/tree/master) and
  works with *Coq 8.6*. It includes only the syntax part of Template-Coq
  and the ability to make plugins.
 
- The development branch is
  [coq-8.7](https://github.com/Template-Coq/template-coq/tree/coq-8.7),
  which includes:

  - The full syntax of CIC:
    [Ast](https://github.com/Template-Coq/template-coq/blob/coq-8.7/theories/Ast.v)

  - The typing judgment of CIC: 
    [Typing](https://github.com/Template-Coq/template-coq/blob/coq-8.7/theories/Typing.v#L488)
    
  - A partial type-checker implementation:
    [Checker](https://github.com/Template-Coq/template-coq/blob/coq-8.7/theories/Checker.v)

  - The `TemplateMonad` datatype and the `Run TemplateProgram` command
    to run template programs:
    [Ast](https://github.com/Template-Coq/template-coq/blob/coq-8.7/theories/Ast.v#L193)
        
Examples of plugins
-------------------
- a plugin to add a constructor in [test-suite/add_constructor.v](https://github.com/Template-Coq/template-coq/tree/coq-8.7/test-suite/add_constructor.v)
- a parametricity plugin in [translations/tsl_param.v](https://github.com/Template-Coq/template-coq/tree/coq-8.7/translations/tsl_param.v)
- a plugin to negate funext in [translations/fun.v](https://github.com/Template-Coq/template-coq/tree/coq-8.7/translations/tsl_fun.v)


Installation instructions
=========================

Install from scratch (for 8.6 and development versions)
-------------------------------------------------------

To get the source code:

    # git clone https://github.com/Template-Coq/template-coq.git
    # git checkout -b coq-8.7 origin/coq-8.7
    # git status
    
Check that you are indeed on the `coq-8.7` branch.

Requirements
------------

To compile the library, you need:

- `Coq 8.7.1` (8.7.0 might work as well) and
- `OCaml` (tested with `4.04.1`, beware that `OCaml 4.06.0` can 
  produce linking errors on some platforms).

Requirements through opam
-------------------------

The easiest way to get both is through [opam](http://opam.ocaml.org):

You might want to create a "switch" (an environment of `opam` packages) for `Coq` if
you don't have one yet:
    
    # opam switch -A 4.04.1 coq.8.7.1
    # eval `opam config env`
    
This creates the `coq.8.7.1` switch which initially contains only the
basic `OCaml` `4.04.1` compiler, and puts you in the right environment
(check with `ocamlc -v`).

Once in the right switch, you can install `Coq` using:
    
    # opam pin add coq 8.7.1 
    
Pinning `coq` prevents opam from trying to upgrade it afterwards, in
this switch. If the command is successful you should have `coq`
available (check with `coqc -v`).

Compile
-------

Once in the right environment, Use:

- `make` to compile the template-coq plugin (and the checker in `coq-8.7`)

- `make translations` to compile the translation plugins (in `coq-8.7`)

- `make test-suite` to compile the test suite

- `make install` to install the plugin in `coq`'s user-contrib local
  library. Then the `Template` namespace can be used for `Require
  Import` statements, e.g. `From Template Require Import All.`.

Install with OPAM (for 8.6 version only)
----------------------------------------
Add the Coq repository:

    opam repo add coq-released https://coq.inria.fr/opam/released

and run:

    opam install coq-template-coq

To get beta versions of Coq, you might want to activate the repository:

    opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev

How to Use
==========

Check `test-suite/demo.v` for examples.

Unless you installed the library, you must add the theories directory to
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

Please report any bugs (or feature requests) on the github [issue tracker](https://github.com/Template-Coq/template-coq/issues)
