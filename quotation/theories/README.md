# Quotation

The `Quotation` module is geared at providing functions `□T → □□T` for
`□T := Ast.term` (currently implemented) and for `□T := { t : Ast.term
& Σ ;;; [] |- t : T }` (still in the works).

Ultimately the goal of this development is to prove that `□` is a lax monoidal
semicomonad (a functor with `cojoin : □T → □□T` that codistributes over `unit`
and `×`), which is sufficient for proving Löb's theorem.

The public-facing interface of this development is provided in [`MetaCoq.Quotation.ToTemplate.All`](./ToTemplate/All.v) and [`MetaCoq.Quotation.ToPCUIC.All`](./ToPCUIC/All.v).

## Public-Facing Interface

### Template

In [`MetaCoq.Quotation.ToTemplate.All`](./ToTemplate/All.v):

- `Raw.quote_term : Ast.term -> Ast.term` (the function `cojoin : □T → □□T` for `□T := Ast.term`)

- `Raw.quote_typing {cf : checker_flags} {Σ Γ t T} : (Σ ;;; Γ |- t : T) -> Ast.term`

- `Raw.quote_red {Σ Γ x y} : @red Σ Γ x y -> Ast.term`

- `Raw.quote_wf_local {cf : checker_flags} {Σ Γ} : wf_local Σ Γ -> Ast.term`

- `Raw.quote_wf {cf Σ} : @wf cf Σ -> Ast.term`

- `Raw.quote_wf_ext {cf Σ} : @wf_ext cf Σ -> Ast.term`

- (experimental) `Raw.WfAst.quote_wf {Σ t} : @WfAst.wf Σ t -> Ast.term`


### PCUIC

In [`MetaCoq.Quotation.PCUIC.All`](./ToPCUIC/All.v):

- `Raw.quote_term : PCUICAst.term -> PCUICAst.term` (the function `cojoin : □T → □□T` for `□T := PCUICAst.term`)

- `Raw.quote_typing {cf : checker_flags} {Σ Γ t T} : (Σ ;;; Γ |- t : T) -> PCUICAst.term`

- `Raw.quote_red {Σ Γ x y} : @red Σ Γ x y -> PCUICAst.term`

- `Raw.quote_wf_local {cf : checker_flags} {Σ Γ} : wf_local Σ Γ -> PCUICAst.term`

- `Raw.quote_wf {cf Σ} : @wf cf Σ -> PCUICAst.term`

- `Raw.quote_wf_ext {cf Σ} : @wf_ext cf Σ -> PCUICAst.term`

## Internal File Organization

The rest of the files in this development should be considered as not
part of the public interface.  The organization described here is
subject to change, and is provided for developers and contributors.


Some design principles:

- Quotation is organized around typeclasses for managing automation for finding and constructing functions `T -> Ast.term` for various `T`: `ground_quotable T` for indicating that all ground terms of type `T` can be quoted (by case analysis or induction, generally); `@quotation_of T t` for indicating that the particular term `t : T` has a quotation in `Ast.term`.

- Hints, settings / flags / options, etc are marked `#[export]` and are *not* exported by the `All.v` files, so that such settings remain internal to the development

- Universes associated to types are systematically refreshed / mangled, to avoid universe inconsistencies; universe polymorphism, which is more painful to manage in the TemplateMonad (due in large part to the fact that `tmAxiom` and `tmDefinition` do not support emitting universe-polymorphic constants), is used judiciously.

- To make performance of typeclass resolution managable in the face of hundreds of possible instances for goals of the form `quotation_of _`, typeclass resolution is set up so as to need backtracking as little as possible, and so that constants are opaque to typeclass resolution by default.  On a case-by-case basis, constants are specifically marked transparent (and added to a `quotation` unfold hint database, which is used to unfold constants without associated instances early and all-at-once).

- General quotability of `T` for `T : Prop` or `T := forall a, B` with `B` being subsingleton is proven via decidability: we write a constant `dec : {T} + {~T}`, the obvious function `bdec : {T} + {~T} -> bool`, a proof that `reconstruct : bdec dec = true -> T`, the function `dec_true : T -> bdec dec = true`, and then we can get a function `T -> Ast.term` as `<% reconstruct %>` applied to the quotation of `dec_true t` for some `t : T`, by virtue of the fact that we can quote any equality proof of booleans as either `<% eq_refl true %>` or `<% eq_refl false %>` depending on the booleans.

- In most cases, inductive types are given explicit `ground_quotable` instances, while most defined constants are just made transparent to typeclass inference.  Defined constants containing `match`es or other constructions that make quoting non-trivial are the exception, and are given `ground_quotable` instances as well.  In general, either a constant is made transparent and added to the `quotation` unfolding hint database, *or* it is given a `ground_quotable` instance, (almost) never both.

- Directory and file structure is mirrored between the `Quotation` development and the underlying Coq development for which quotation theory is being developed.  Sometimes directories are compressed into single files (e.g., [`ToTemplate/Coq/Init.v`](./ToTemplate/Coq/Init.v) contains quotation theory for everything in the `Coq.Init.*` namespace), and other times single files are expanded into a directory (e.g., [`ToTemplate/QuotationOf/Template/Ast/`](./ToTemplate/QuotationOf/Template/Ast/) contains `Foo/Instances.v` for every module `Foo` defined in `MetaCoq.Template.Ast` ([`template-coq/theories/Ast.v`](https://github.com/MetaCoq/metacoq/tree/coq-8.16/template-coq/theories/Ast.v))).  Directories are compressed into single files when the quotation theory is quick to typecheck and relatively short; files are expanded into directories when components of the quotation theory take a long time to typecheck, so that file-level parallelism can be better leveraged.

- When possible, we try to minimize the content in `ground_quotable` proofs (in particular, using named induction principles rather than bare fixpoints and avoiding excess conversion, when easy), so that proving that these constructions are well-typed is easier.  (This is still very much a work in progress, and principles making the proving of well-typedness easy are still in the works.)

The important files and directories:

- [`CommonUtils.v`](./CommonUtils.v) - This file defines the utility functions that are shared between Template and PCUIC quotation, including various manipulations of kernames, adjustment of universes for automating quotation, and a utility for getting the body of opaque constants for ease of quotation.

Almost all other strucucture is mirrored between the `ToTemplate/` and `ToPCUIC/` folders, with code being identical whenever possible.


- [`ToTemplate/Init.v`](./ToTemplate/Init.v), [`ToPCUIC/Init.v`](./ToPCUIC/Init.v) - Most of the code is character-for-character identical between these files, differing only in whether the constants refer to `Template.Ast` definitions or `PCUIC.PCUICAst` definitions.  Minor differences are required due to differences in how `term` is structured.  These files define:

  - the typeclasses `quotation_of {T} (t : T) := quoted_term_of : Ast.term` and `ground_quotable T := quote_ground : forall t : T, quotation_of t` which are used for managing quotation in the rest of the development.

  - (The typeclass `inductive_quotation_of` is defined for managing automation of quoting inductives, which have slightly different replacement rules.)

  - Automation `replace_quotation_of` and `make_quotation_of` are defined for solving goals of the form `quotation_of t` when `<% t %>` will contain local variables (`tVar "v"`) or functor-bound constants or inductives (modpaths containing `MPbound` or which share a common prefix with the currently open module in a way that suggests they may reference constants in a currently-open functor): such local variables and transient constants and inductives are replaced via typeclass inference with constants or variables of type `quotation_of v`.  The automation will deliberately error if such a replacement cannot be made.  Setting `Instance: debug_opt := true. Set Printing Implicit.` before running one of these methods will result in a printout of the variables replaced as well as the `quotation_of` goals which could not be solved.

  - Modules `Instances`, `PolymorphicInstances`, and `StrongerInstances` for exposing typeclass instance hints and flags around `quotation_of` and `ground_quotable`.  (Note that no instances nor flag settings are exported by the `All.v` files, allowing for containment of the flag settings and hints used to automate quotation.)

  - `ground_quotable_of_dec`, `ground_quotable_neg_of_dec`, `ground_quotable_neq_of_EqDec` for making use of decidability to quote otherwise-uninspectable terms (`Prop`s and functions)

  - Universe polymorphic `_cps` quotations of projections of some common template-polymorphic inductives, used to avoid universe inconsistencies

  - `ground_quotable_of_iffT`, `ground_quotable_of_iff`, `quote_neg_of_iffT`, `quote_neg_of_iff` for leveraging equivalences to transfer quotations

  - The tactic `unfold_quotation_of` for allowing quotation of `Qed`-opaque terms by routing through Template Monad lookup of the opaque body.

  - Automation `tmDeclareQuotationOfModule` and `tmMakeQuotationOfModule` for declaring and defining `quotation_of` instances for all constants in a module; this is used for managing `Module Type`s and functors containing constants whose quotability needs to be assumed.


- [`ToTemplate/QuotationOf/`](./ToTemplate/QuotationOf/), [`ToPCUIC/QuotationOf/`](./ToPCUIC/QuotationOf/) - These directories develop `quotation_of` instances for various `Module Type`s and functors.  The various `Sig.v` files contain `Module Type`s declaring the instances, while the various `Instances.v` files contain the definitions of `Module`s having these `Module Type`s defining the `quotation_of` instances.  The `Module`s in `Instances.v` files *do not* export `Instance`s, while the `Module Type`s in `Sig.v` files *do*; if the concrete constant needs to be quoted, it can be quoted with `<% ... %>` directly and does not need an instance; when functors take in a `Module Type` argument, by contrast, they do need access to the instances declared.  When `Module`s are nested inside `Module Type`s, the top-level `Module Type` exports all declared instances in the submodules.  Nearly all declarations and definitions in files under `QuotationOf` are fully automated; when well-typedness is eventually proven, that should be fully automated as well for these directories, likely by invoking the Safe Checker.

- Under `ToTemplate/` / `ToPCUIC/`, folders `Coq/`, `Equations/`, `Utils/`, `Common/`, and `Template/` or `PCUIC/` develop the `ground_quotable` instances for `Coq.*`, `Equations.*`, `MetaCoq.Utils.*`, `MetaCoq.Common.*`, and `MetaCoq.Template.*` or `MetaCoq.PCUIC.*`, respectively.  In `Coq/` and `Equations/`, generally one file is given to each folder of the underlying development; in `Utils/`, `Common/`, `Template/`, and `PCUIC/`, files generally correspond one-to-one with the underlying development.
