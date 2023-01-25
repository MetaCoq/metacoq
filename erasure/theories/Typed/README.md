# typed-extraction

Extraction of types, certifying transformations (eta, inlining), type annotations, the dearg optimisation and corresponding proofs.
The repository is an intermadiate step towards moving this functionality to MetaCoq.

Builds with Coq 8.14-8.16 and MetaCoq 1.1.1

## How to build

Our development works with Coq 8.16 and depends on MetaCoq and coq-equations.
The dependencies can be installed through `opam`.

To set up a switch with the necessary dependencies run the following commands from the root of the project:

```bash
opam switch create . 4.10.2 --repositories default,coq-released=https://coq.inria.fr/opam/released --deps-only
eval $(opam env)
```

If Coq 8.16 is already installed, run

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam install ./coq-concert.opam --deps-only
```

After completing the procedures above, run `make` to build the development.
