From MetaCoq.Quotation.ToTemplate Require Import Stdlib.Init.
From MetaCoq.Utils Require Import MCReflect.

#[export] Instance quote_reflectT {A} {qA : quotation_of A} {quoteA : ground_quotable A} {quote_negA : ground_quotable (A -> False)} {b} : ground_quotable (@reflectT A b) := ltac:(destruct 1; exact _).
