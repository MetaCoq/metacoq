# Documentation for MetaCoq users and developers

## Branches and compatibility

**tl;dr** You should do your PRs against [coq-8.20](https://github.com/MetaCoq/metacoq/tree/coq-8.20).

Coq's kernel API is not stable yet, and changes there are reflected in MetaCoq's reified structures,
so we do not ensure any compatibility from version to version. There is one branch for each Coq version.

The *main branch* or *current branch* is the one which appers when you go on
[https://github.com/MetaCoq/metacoq](https://github.com/MetaCoq/metacoq).
Currently (unless you are reading the README of an outdated branch),
it is the [coq-8.20](https://github.com/MetaCoq/metacoq/tree/coq-8.20).
You should use it both for usage of MetaCoq and development of MetaCoq.

The [main](https://github.com/MetaCoq/metacoq/tree/main) branch is following Coq's master
branch and gets regular updates from the the main development branch which follows the latest
stable release of Coq.

<!-- The branch ... -->
<!-- gets backports from `coq-8.11` when possible. Both `coq-8.11` and `coq-8.10` have associated -->
<!-- "alpha"-quality `opam` packages. -->

## Program and Equations

MetaCoq relies on `Program` and `Equations` plugins, however try to avoid `Program` as it
inserts some JMeq and UIP axioms silently, whereas we try to keep the development axiom-free.
You can use `Equations` to do some dependent induction (`dependent induction`,
`dependent destruction`, `depelim`). You may need to add:
```
Require Import Equations.Prop.DepElim.
```

## ident vs. qualid. vs kername

MetaCoq uses three types convertible to `string` which have a different intended meaning:

- `ident` is the type of identifiers, they should not contains any dot.
  E.g. `nat`

- `qualid` is the type of partially qualified names.
  E.g. `Datatypes.nat`

- `kername` is a structured type of fully qualified names.
  E.g. `Stdlib.Init.Datatypes.nat`

Quoting always produce fully qualified names. On the converse, unquoting allow to
have only partially qualified names and rely on Coq to resolve them. The commands
of the TemplateMonad also allow partially qualified names.

## Hint databases

The development uses three main hint databases:

- The "len" databases which gathers all relevant length lemmas (mainly list length lemmas
  relevant to the operations). This database is large (> 100 lemmas) for a given theory
  (PCUIC or Template-Coq) and it is advisable to not mix together both databases,
  as autorewrite would become very slow.
  BEWARE: If working in the PCUIC theory, do not require anything besides the BasicAst and utils modules from the Template-Coq module.
- The "pcuic" rewrite and auto database gathers lemmas helping solving side-conditions
  of typing judgements.

## Options


`Set / Unset MetaCoq Strict Unquote Universe Mode`. When this mode is on,
the unquoting of a universe level fails if this level does not exists.
Otherwise the level is added to the current context. It is on by default.

There is also an "opaque" universe `fresh_universe` which is unquoted to
a fresh level when `MetaCoq Strict Unquote Universe Mode` is off.



## Contribution guidelines

- Please use as many bullets as possible.
  You even can be forced to do so with `Set Default Goal Selector "!".`

- Please use as few as possible generated names and name hypothesis in `intros`
  and `destruct`. It is more difficult for `induction` and above all for
  `inversion`.



## Dependency graph between files

Generated on 2022/07/01, sources [there](https://github.com/MetaCoq/metacoq/tree/coq-8.20/dependency-graph).

<center>
<img src="https://raw.githubusercontent.com/MetaCoq/metacoq.github.io/master/assets/depgraph-2022-07-01.png"
	 alt="Dependency graph" width="700px" display="inline"/>
</center>



## MetaDocumentation (documentation about documentation)

The file `README.md` in https://github.com/MetaCoq/metacoq.github.io is supposed to be synchronized with
`README.md` in [https://github.com/MetaCoq/metacoq/](https://github.com/MetaCoq/metacoq/).

That's why we can't use relative links and have to use absolute ones.
E.g. [INSTALL.md](https://github.com/MetaCoq/metacoq/tree/coq-8.20/INSTALL.md) and not [INSTALL.md](INSTALL.md).

Thus, when switching to a new default branch, we have to search and replace the old branch with the new one.
