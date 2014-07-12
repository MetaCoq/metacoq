template-coq
============

Template Coq is a quoting library for Coq. It takes Coq terms and constructs a representation of their syntax tree as a Coq inductive data type.
The representatino is based on the kernel's term representation. Reasoning about this data type can only be done informally, i.e. there is no Coq function that can take this syntax and produce its meaning.

How to Use
----------

Check test-suite/demo.v for examples.

Bugs
----

Please report any bugs (or feature requests) on the github issue tracker:

   https://github.com/gmalecha/template-coq/issues
