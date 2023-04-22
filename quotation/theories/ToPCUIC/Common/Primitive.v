From MetaCoq.Quotation.ToPCUIC Require Import Coq.Init.
From MetaCoq.Common Require Import Primitive.

#[export] Instance quote_prim_tag : ground_quotable prim_tag := ltac:(destruct 1; exact _).
