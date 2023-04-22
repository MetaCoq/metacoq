From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate Require Import (hints) Coq.Init Coq.Floats Coq.Numbers.
From MetaCoq.Quotation.ToTemplate.Utils Require Import (hints) utils.
From MetaCoq.Quotation.ToTemplate.Common Require Import (hints) Kernames.
From MetaCoq.Common Require Import BasicAst.
From MetaCoq.Utils Require Import MCUtils.
From MetaCoq.Template Require Import AstUtils (* for tFixType *).

#[export] Instance quote_name : ground_quotable name := ltac:(destruct 1; exact _).
#[export] Instance quote_relevance : ground_quotable relevance := ltac:(destruct 1; exact _).
#[export] Instance quote_binder_annot {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (binder_annot A) := ltac:(destruct 1; exact _).
#[export] Instance quote_cast_kind : ground_quotable cast_kind := ltac:(destruct 1; exact _).
#[export] Instance quote_case_info : ground_quotable case_info := ltac:(destruct 1; exact _).
#[export] Instance quote_recursivity_kind : ground_quotable recursivity_kind := ltac:(destruct 1; exact _).
#[export] Instance quote_conv_pb : ground_quotable conv_pb := ltac:(destruct 1; exact _).
#[export] Hint Unfold aname : quotation.
#[export] Typeclasses Transparent aname.
#[export] Instance quote_def {term} {qterm : quotation_of term} {quote_term : ground_quotable term} : ground_quotable (def term) := ltac:(destruct 1; exact _).
#[export] Instance quote_typ_or_sort_ {term} {qterm : quotation_of term} {quote_term : ground_quotable term} : ground_quotable (typ_or_sort_ term) := ltac:(destruct 1; exact _).
#[export] Instance quote_context_decl {term} {qterm : quotation_of term} {quote_term : ground_quotable term} : ground_quotable (context_decl term) := ltac:(destruct 1; exact _).
#[export] Hint Unfold mfixpoint : quotation.
#[export] Typeclasses Transparent mfixpoint.
#[local] Hint Unfold dtype dbody : quotation.
#[export] Instance quotation_of_mfixpoint {term} {m : mfixpoint term} {qterm : quotation_of term} {qm : tFixType quotation_of quotation_of m} : quotation_of m := ltac:(induction qm; destruct_head'_prod; destruct_head' def; exact _).
#[export] Hint Unfold eq_binder_annot : quotation.
#[export] Typeclasses Transparent eq_binder_annot.
