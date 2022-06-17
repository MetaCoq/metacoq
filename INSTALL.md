# Installation instructions

## Installing with OPAM

The easiest way to get all packages is through [`opam`](http://opam.ocaml.org).
See [Coq's opam documentation](https://coq.inria.fr/opam-using.html)
for installing an `opam` switch for Coq.
See [releases](https://github.com/MetaCoq/metacoq/releases) and
[Coq's Package Index](https://coq.inria.fr/opam/www/) for information on
the available releases and opam packages.

To add the Coq repository to available `opam` packages, use:

    # opam repo add coq-released https://coq.inria.fr/opam/released

To update the list of available packages at any point use:

    # opam update

Then, simply issue:

    # opam install coq-metacoq

MetaCoq is split into multiple packages that get all installed using the
`coq-metacoq` meta-package:

 - `coq-metacoq-template` for the Template Monad and quoting plugin
 - `coq-metacoq-pcuic` for the PCUIC development and proof of the
   Template-Coq -> PCUIC translation
 - `coq-metacoq-safechecker` for the verified checker on PCUIC terms
 - `coq-metacoq-erasure` for the verifed erasure from PCUIC to
   untyped lambda-calculus.
 - `coq-metacoq-translations` for example translations from type theory
   to type theory: e.g. variants of parametricity.

There are also `.dev` packages available in the `extra-dev` repository
of Coq, to get those you will need to activate the following repositories:

    opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev
    opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev


## Installing from source code

### Requirements

To compile the library, you need:

- The `Coq` version corrsponding to your branch (you can use the `coq.dev` package
  for the `master` branch).
- `OCaml` (tested with `4.06.1`, `4.07.1`, and `4.10.0`, beware that `OCaml 4.06.0`
  can produce linking errors on some platforms)
- [`Equations 1.3`](http://mattam82.github.io/Coq-Equations/)

The recommended way to build a development environment for MetaCoq is
to have a dedicated `opam` switch (see below).

### Getting the sources

To get the source code:

    # git clone https://github.com/MetaCoq/metacoq.git
    # git checkout -b coq-8.14 origin/coq-8.14
    # git status

This checks that you are indeed on the `coq-8.14` branch.

### Setting up an `opam` switch

To setup a fresh `opam` installation, you might want to create a
"switch" (an environment of `opam` packages) for `Coq` if you don't have
one yet. You need to use **opam 2** to obtain the right version of
`Equations`.

    # opam switch create coq.8.16 --packages=ocaml-variants.4.13.1+options,ocaml-option-flambda
    # eval $(opam env)

This creates the `coq.8.16` switch which initially contains only the
basic `OCaml` `4.13.1` compiler with the `flambda` option enabled,
and puts you in the right environment (check with `ocamlc -v`).

Once in the right switch, you can install `Coq` and the `Equations` package using:

    # opam install . --deps-only

If the commands are successful you should have `coq` available (check with `coqc -v**).


**Remark:** You can create a [local switch](https://opam.ocaml.org/blog/opam-20-tips/#Local-switches) for
developing using (in the root directory of the sources):

    # opam switch create . 4.07.1

Or use `opam switch link foo` to link an existing opam switch `foo` with
the sources directory.


### Compiling from sources

**Important**: To compile locally without using `opam`, use `./configure.sh local` at the root.

Then use:

- `make` to compile the `template-coq` plugin, the `pcuic`
  development and the `safechecker` and `erasure` plugins.
  You can also selectively build each target.

- `make translations` to compile the translation plugins

- `make test-suite` to compile the test suite

- `make install` to install the plugin in `Coq`'s `user-contrib` local
  library. Then the `MetaCoq` namespace can be used for `Require
  Import` statements, e.g. `From MetaCoq.Template Require Import All.`.

- `make uninstall` to undo the last line.

For faster development one can use:

- `make vos` to compile `vos` files (bypassing proofs)
  for `pcuic`, `safechecker` and `erasure`. The template-coq library is still using the regular `vo` target to be able
  to construct the template-coq plugin. The `safechecker` and
  `erasure` ML plugins *cannot* be built using this mode.

- `make quick` is a synonymous for `make vos` with the addition of a global `Unset Universe Checking` option, i.e. 
universes are not checked anywhere.
