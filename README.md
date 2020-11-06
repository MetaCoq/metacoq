MetaCoq
=======

<img src="https://raw.githubusercontent.com/MetaCoq/metacoq.github.io/master/assets/LOGO.png" alt="MetaCoq" width="50px"/>

[![Build Status](https://travis-ci.com/MetaCoq/metacoq.svg?branch=coq-8.12)](https://travis-ci.com/MetaCoq/metacoq)
[![MetaCoq Chat](https://img.shields.io/badge/zulip-join_chat-brightgreen.svg)](https://coq.zulipchat.com)

MetaCoq is a project formalizing Coq in Coq and providing tools for
manipulating Coq terms and developing certified plugins
(i.e. translations, compilers or tactics) in Coq.

See the [website](https://metacoq.github.io/) for a documentation,
related papers and introduction to the system, along with installation instructions
for targeted at users.

```
Copyright (c) 2014-2020 Gregory Malecha
Copyright (c) 2015-2020 Abhishek Anand, Matthieu Sozeau
Copyright (c) 2017-2020 Simon Boulier, Nicolas Tabareau, Cyril Cohen
Copyright (c) 2018-2020 Danil Annenkov, Yannick Forster, Théo Winterhalter
```

This software is distributed under the terms of the MIT license.
See [LICENSE](LICENSE) for details.

Bugs
====

Please report any bugs (or feature requests) on the github [issue tracker](https://github.com/MetaCoq/metacoq/issues).

Branches and compatibility
========

Coq's kernel API is not stable yet, and changes there are reflected in MetaCoq's reified structures,
so we do not ensure any compatibility from version to version.

The [master](https://github.com/MetaCoq/metacoq/tree/master) branch is following Coq's master 
branch and gets regular updates from the the main development branch which follows the latest 
stable release of Coq.

Currently, the [coq-8.12](https://github.com/MetaCoq/metacoq/tree/coq-8.12) branch is the main stable branch.
The branch [coq-8.11](https://github.com/MetaCoq/metacoq/tree/coq-8.12) 
gets backports from `coq-8.11` when possible. Both `coq-8.12` and `coq-8.11` have associated 
"alpha"-quality `opam` packages.
The `opam` packages of `coq-8.10` are usable, but are no longer updated.

The branches [coq-8.6](https://github.com/MetaCoq/metacoq/tree/coq-8.6),
[coq-8.7](https://github.com/MetaCoq/metacoq/tree/coq-8.7), [coq-8.8](https://github.com/MetaCoq/metacoq/tree/coq-8.8), [coq-8.9](https://github.com/MetaCoq/metacoq/tree/coq-8.9), and [coq-8.10](https://github.com/MetaCoq/metacoq/tree/coq-8.10) are frozen.

Installation instructions (for developers only)
=========================

The recommended way to build a development environment for MetaCoq is
to have a dedicated `opam` switch.

Setting up an `opam` switch
---------------

To setup a fresh `opam` installation, you might want to create a
"switch" (an environment of `opam` packages) for `Coq` if you don't have
one yet. You need to use **opam 2** to obtain the right version of
`Equations`.

    # opam switch create coq.8.12 4.07.1
    # eval $(opam env)

This creates the `coq.8.11` switch which initially contains only the
basic `OCaml` `4.07.1` compiler, and puts you in the right environment
(check with `ocamlc -v`).

Once in the right switch, you can install `Coq` and the `Equations` package using:

    # opam install . --deps-only

If the commands are successful you should have `coq` available (check with `coqc -v`). 

Installing from GitHub repository (for developers)
------------------------------

To get the source code:

    # git clone https://github.com/MetaCoq/metacoq.git
    # git checkout -b coq-8.12 origin/coq-8.12
    # git status

This checks that you are indeed on the `coq-8.12` branch.

You can create a [local
switch](https://opam.ocaml.org/blog/opam-20-tips/#Local-switches) for
developing using (in the root directory of the sources):

    # opam switch create . 4.07.1

Or use `opam switch link foo` to link an existing `opam` switch `foo` with
the sources directory.

Requirements
------------

To compile the library, you need:

- The `Coq` version corresponding to your branch (you can use the `coq.dev` package 
  for the `master` branch).
- `OCaml` (tested with `4.07.1` and `4.09.1`, beware that `OCaml 4.06.0`
  can produce linking errors on some platforms)
- [`Equations 1.2.3`](http://mattam82.github.io/Coq-Equations/)

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


Contributions Guidelines
========================

Robustness
----------

To ease reparing the broken code:

- Please use as many bullets as possible.
  You even can be forced to do so with `Set Default Goal Selector "!".`

- Plese use as few as possible generated names and name hypothesis in `intros` and
  `destruct`.
  It is more difficult for `induction` and above all for `inversion`.


Program/Equations
-----------------

Please don't use `Program`. It inserts some JMeq and UIP axioms silently.  You can
use `Equations` to do some dependent induction (`dependent induction`,
`dependent destruction`, `depelim`). You may need to add:
```
Require Import Equations.Prop.DepElim.
```

*Important*: we keep the template-coq folder not relying on Equations (to be able
to compile it without external dependency).
