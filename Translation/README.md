# About ETT to ITT

If you're only interested in the translation from ETT to ITT, you should only look at the following files
(which are the only ones brought by this fork).

- `SAst.v` describes common syntax (in a similar fashion to `Ast.v`) of both ETT and ITT.
- `SLiftSubst.v` describes meta-operations on the syntax (namely lifting and substitution).
- `SCommon.v` states common definitions like context.

- `ITyping.v` contains the typing rules of ITT.
- `XTyping.v` contains the typing rules of ETT.

- `PackLifts.v` contains the necessary lifts to deal with packing.

- `Translation.v` contains the translation itself and the necessary lemmata.
- `FinalTranslation.v` containes the transaltion from ITT to
  TemplateCoq (meaning we can reify terms of ITT).
- `Example.v` contains an example of the two translations chained to
  build a Coq term from an ETT derivation.
