template-coq
============

Template Coq is a quoting library for Coq. It takes Coq terms and constructs a representation of their syntax tree as a Coq inductive data type.
The representatino is based on the kernel's term representation. Reasoning about this data type can only be done informally, i.e. there is no Coq function that can take this syntax and produce its meaning.

Install with OPAM
-----------------
Add the Coq repository:

    opam repo add coq-released https://coq.inria.fr/opam/released

and run:

    opam install coq-template-coq

To get the beta versions of Coq, activate the repository:

    opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev

How to Use
----------

Check test-suite/demo.v for examples.

You must add the theories directory to your Coq load path with the prefix
Template. This can be done on the command line by adding:
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

Compile
-------
Use:
- `make` to compile the plugin
- `make translations` to compile the translation plugins
- `make test-suite` to compile the test suite

Bugs
----

Please report any bugs (or feature requests) on the github issue tracker:

   https://github.com/gmalecha/template-coq/issues
