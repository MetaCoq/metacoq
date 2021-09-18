# Documentation for MetaCoq users and developpers

## Branches and compatibility

**tl;dr** You should do your PRs against [coq-8.11](https://github.com/MetaCoq/metacoq/tree/coq-8.11).


Coq's kernel API is not stable yet, and changes there are reflected in MetaCoq's reified structures,
so we do not ensure any compatibility from version to version. There is one branch for each Coq version.

The *main branch* or *current branch* is the one which appers when you go on
[https://github.com/MetaCoq/metacoq](https://github.com/MetaCoq/metacoq).
Currently (unless you are reading the README of an outdated branch),
it is the [coq-8.11](https://github.com/MetaCoq/metacoq/tree/coq-8.11).
You should use it both for usage of MetaCoq and development of MetaCoq.
We should move soon to [coq-8.12](https://github.com/MetaCoq/metacoq/tree/coq-8.12).

The [master](https://github.com/MetaCoq/metacoq/tree/master) branch is following Coq's master
branch and gets regular updates from the the main development branch which follows the latest
stable release of Coq.

The branch [coq-8.10](https://github.com/MetaCoq/metacoq/tree/coq-8.10)
gets backports from `coq-8.11` when possible. Both `coq-8.11` and `coq-8.10` have associated
"alpha"-quality `opam` packages.

The branches [coq-8.6](https://github.com/MetaCoq/metacoq/tree/coq-8.6),
[coq-8.7](https://github.com/MetaCoq/metacoq/tree/coq-8.7), [coq-8.8](https://github.com/MetaCoq/metacoq/tree/coq-8.8)
and [coq-8.9](https://github.com/MetaCoq/metacoq/tree/coq-8.9) are frozen.



## Program and Equations

MetaCoq relies on `Program` and `Equations` plugins.

**Important**: We keep the `template-coq` folder not relying on Equations so that
it compiles without external dependency.
That's why first lemmas involving Equations are in `PCUICUtils.v`.

Besides, try to avoid `Program`. It inserts some JMeq and UIP axioms silently. You can
use `Equations` to do some dependent induction (`dependent induction`,
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

- `kername` is the type of fully qualified names.
  E.g. `Coq.Init.Datatypes.nat`

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


`Set / Unset Strict Unquote Universe Mode`. When this mode is on,
the unquoting of a universe level fails if this level does not exists.
Otherwise the level is added to the current context. It is on by default.

There is also an "opaque" universe `fresh_universe` which is unquoted to
a fresh level when `Strict Unquote Universe Mode` is off.



## Contribution guidelines

- Please use as many bullets as possible.
  You even can be forced to do so with `Set Default Goal Selector "!".`

- Please use as few as possible generated names and name hypothesis in `intros`
  and `destruct`. It is more difficult for `induction` and above all for
  `inversion`.



## Dependency graph between files

Generated on 2020/09/24, sources [there](https://github.com/MetaCoq/metacoq/tree/coq-8.11/dependency-graph).

<center>
<img src="https://raw.githubusercontent.com/MetaCoq/metacoq.github.io/master/assets/depgraph-2020-09-24.png"
	 alt="Dependency graph" width="700px" display="inline"/>
</center>



## MetaDocumentation (documentation about documentation)

The file `README.md` in https://github.com/MetaCoq/metacoq.github.io is supposed to be synchronized with
`README.md` in [https://github.com/MetaCoq/metacoq/](https://github.com/MetaCoq/metacoq/).

That's why we can't use relative links and have to use absolute ones.
E.g. [INSTALL.md](https://github.com/MetaCoq/metacoq/tree/coq-8.11/INSTALL.md) and not [INSTALL.md](INSTALL.md).

Thus, when switching to a new default branch, we have to search and replace by the old branch by the new one.
