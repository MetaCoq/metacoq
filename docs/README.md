Template Coq
============

Template Coq is a quoting library for [Coq](http://coq.inria.fr). It
takes Coq terms and constructs a representation of their syntax tree as
a Coq inductive data type. The representation is based on the kernel's
term representation.

In addition to this representation of terms, Template Coq includes:

- Reification of the environment structures, for constant and inductive
  declarations.

- Denotation of terms and global declarations

There is work in progress to integrate a monad for manipulating
global declarations, and inserting them in the global environment, in
the stype of MetaCoq/MTac.

Credits
=======

Template-Coq was originally developed by
[Gregory Malecha](https://github.com/gmalecha), and is now developed by
[Abhishek Anand](https://github.com/aa755), [Simon
Boulier](https://github.com/simonboulier), [Yannick
Forster](https://github.com/yforster) and [Matthieu Sozeau](https://github.com/mattam82).

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

Bugs
----

Please report any bugs (or feature requests) on the [github issue
tracker](https://github.com/Template-Coq/template-coq/issues).

