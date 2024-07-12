From MetaCoq.Quotation.ToTemplate Require Import Stdlib.Init.
From MetaCoq.Common Require Import config.

#[export] Instance quote_checker_flags : ground_quotable checker_flags := ltac:(destruct 1; exact _).
