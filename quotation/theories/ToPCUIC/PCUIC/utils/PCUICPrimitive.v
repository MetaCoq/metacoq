From MetaCoq.PCUIC Require Import utils.PCUICPrimitive.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC Require Import (hints) Coq.Init Coq.Numbers Coq.Floats.
From MetaCoq.Quotation.ToPCUIC.Common Require Import (hints) Universes Primitive.

#[export] Instance quote_array_model {term} {qterm : quotation_of term} {quote_term : ground_quotable term} : ground_quotable (array_model term) := ltac:(destruct 1; exact _).

#[export] Instance quote_prim_model {term tag} {qterm : quotation_of term} : ground_quotable (prim_model term tag) := ltac:(destruct 1; exact _).

#[export] Instance quote_prim_model_of {term tag} : ground_quotable (prim_model_of term tag) := ltac:(cbv [prim_model_of]; exact _).

#[export] Instance quote_prim_val {term} {qterm : quotation_of term} : ground_quotable (prim_val term) := ltac:(cbv [prim_val]; exact _).
