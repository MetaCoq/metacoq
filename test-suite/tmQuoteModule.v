From MetaCoq.Template Require Import bytestring Loader All.
Import MCMonadNotation.
Module Foo.
    Inductive bar : Set := .
  Definition t := nat.
End Foo.

MetaCoq Run (tmQuoteModule "Foo"%bs).
MetaCoq Run (tmQuoteModule "Datatypes"%bs).