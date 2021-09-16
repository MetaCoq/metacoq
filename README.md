# Bidirectional PCUIC


## MetaCoq

For general documentation about MetaCoq, see [the corresponding readme](./METACOQ.md).


## Installing the artefact

### Requirements

To compile the library, you need:

- `Coq` version `8.11`.
- `OCaml` (tested with `4.07.1`).
- [`Equations 1.2.3`](http://mattam82.github.io/Coq-Equations/).

The recommended way to build a development environment for MetaCoq is
to have a dedicated `opam` switch (see below).

### Setting up an `opam` switch

To setup a fresh `opam` installation, you might want to create a
"switch" (an environment of `opam` packages) for `Coq` if you don't have
one yet. You need to use `opam 2` to obtain the right version of
`Equations`.

    # opam switch create coq.8.11 4.07.1
    # eval $(opam env)

This creates the `coq.8.11` switch which initially contains only the
basic `OCaml` `4.07.1` compiler, and puts you in the right environment
(check with `ocamlc -v`).

Once in the right switch, you can install `Coq` and the `Equations` package using:

    # opam install . --deps-only


### Compiling the sources

**Important**: Use `./configure.sh local` at the root to setup the installation files.

Then use:

    # make

 to compile the MetaCoq project, or
    
    # make pcuic

 to compile only the part relevant for the ITP submission.
 
## Structure of the artefact

| File                    | Description                                  |
|-------------------------|----------------------------------------------|
| [BDEnvironmentTyping] | Variant of MetaCoq.Template.EnvironmentTyping, to accommodate for the distinction between checking and sorting in the checking of the environment |
| [BDTyping]            | Definition of the bidirectional typing mutual inductive type, proof of a good induction principle |
| [BDToPCUIC]           | Proof that bidirectional typing implies undirected typing |
| [BDFromPCUIC]         | Proof that undirected typing implies bidirectional typing |
| [BDUnique]            | Proof of the uniqueness of inferred types upto cumulativity, and principal types as corollary |

[BDEnvironmentTyping]: ./pcuic/theories/bidirectional/BDEnvironmentTyping.v
[BDTyping]: ./pcuic/theories/bidirectional/BDTyping.v
[BDToPCUIC]: ./pcuic/theories/bidirectional/BDToPCUIC.v
[BDFromPCUIC]: ./pcuic/theories/bidirectional/BDFromPCUIC.v
[BDUnique]: ./pcuic/theories/bidirectional/BDUnique.v

## Assumptions

No assumptions remain in the files mentioned above.

However, the proofs rely on the new structure for case nodes introduced very recently in Coq and MetaCoq. The MetaCoq files underlying the artefact are branched off pull-request [#547] of the MetaCoq GitHub repository, that introduces this change. The adaptation of the metatheory of MetaCoq to this new representation is ongoing in that PR, so some of the metatheoretical properties of PCUIC we rely on in [BDToPCUIC] and [BDFromPCUIC] are not yet fully proven – although they were prior to the modification.

Finally, MetaCoq contains axioms pertaining to the normalization of PCUIC and the guard condition for (co)fixpoints, since normalization of the system cannot cannot be proven in Coq itself due to Gödel incompleteness.

[#547]: https://github.com/MetaCoq/metacoq/pull/534