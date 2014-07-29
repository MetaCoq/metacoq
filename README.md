template-coq
============

Template Coq is a quoting library for Coq. It takes Coq terms and constructs a representation of their syntax tree as a Coq inductive data type.
The representatino is based on the kernel's term representation. Reasoning about this data type can only be done informally, i.e. there is no Coq function that can take this syntax and produce its meaning.

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

Please report any bugs (or feature requests) on the github issue tracker:

   https://github.com/gmalecha/template-coq/issues
