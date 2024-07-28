From MetaCoq.PCUIC Require Import PCUICAst Syntax.PCUICReflect Syntax.PCUICInduction.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC Require Import (hints) Stdlib.Init Stdlib.Lists Stdlib.Numbers Stdlib.Floats.
From MetaCoq.Quotation.ToPCUIC.Common Require Import (hints) Universes BasicAst Kernames.
From MetaCoq.Quotation.ToPCUIC.Common Require Import Environment EnvironmentTyping.
From MetaCoq.Quotation.ToPCUIC.PCUIC Require Import (hints) utils.PCUICPrimitive.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Common Require Import Environment.Sig EnvironmentTyping.Sig.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.PCUIC Require Import PCUICAst.Instances Syntax.PCUICReflect.Instances.

#[export] Instance quote_predicate {term} {qterm : quotation_of term} {quote_term : ground_quotable term} : ground_quotable (predicate term) := ltac:(destruct 1; exact _).
#[export] Instance quote_branch {term} {qterm : quotation_of term} {quote_term : ground_quotable term} : ground_quotable (branch term) := ltac:(destruct 1; exact _).
#[local] Hint Extern 1 => assumption : typeclass_instances.

#[export] Instance quote_term : ground_quotable term := ltac:(induction 1 using term_forall_list_ind; exact _).

Module QuotePCUICTerm <: QuoteTerm PCUICTerm.
  #[export] Instance quote_term : ground_quotable PCUICTerm.term := ltac:(cbv [PCUICTerm.term]; exact _).
End QuotePCUICTerm.
Export (hints) QuotePCUICTerm.

Module QuotePCUICEnvironment := QuoteEnvironment PCUICTerm PCUICEnvironment QuotePCUICEnvironmentHelper qPCUICTerm qPCUICEnvironment qQuotePCUICEnvironmentHelper QuotePCUICTerm.
Export (hints) QuotePCUICEnvironment.

Module QuotePCUICLookup := QuoteLookup PCUICTerm PCUICEnvironment PCUICLookup PCUICEnvironmentDecide qPCUICEnvironment qPCUICLookup qPCUICEnvironmentDecide QuotePCUICEnvironment.
Export (hints) QuotePCUICLookup.

Module QuotePCUICEnvTyping := QuoteEnvTyping PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping qPCUICTerm qPCUICEnvironment qPCUICEnvTyping QuotePCUICTerm QuotePCUICEnvironment.
Export (hints) QuotePCUICEnvTyping.

Module QuotePCUICConversion := QuoteConversion PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping PCUICConversion qPCUICTerm qPCUICEnvironment qPCUICConversion QuotePCUICTerm QuotePCUICEnvironment.
Export (hints) QuotePCUICConversion.

Module QuotePCUICGlobalMaps := QuoteGlobalMaps PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping PCUICConversion PCUICLookup PCUICGlobalMaps qPCUICTerm qPCUICEnvironment qPCUICEnvTyping qPCUICConversion qPCUICLookup qPCUICGlobalMaps QuotePCUICTerm QuotePCUICEnvironment QuotePCUICEnvTyping QuotePCUICConversion QuotePCUICLookup.
Export (hints) QuotePCUICGlobalMaps.

#[export] Instance quote_parameter_entry : ground_quotable parameter_entry := ltac:(destruct 1; exact _).
#[export] Instance quote_definition_entry : ground_quotable definition_entry := ltac:(destruct 1; exact _).
#[export] Instance quote_constant_entry : ground_quotable constant_entry := ltac:(destruct 1; exact _).
#[export] Instance quote_one_inductive_entry : ground_quotable one_inductive_entry := ltac:(destruct 1; exact _).
#[export] Instance quote_mutual_inductive_entry : ground_quotable mutual_inductive_entry := ltac:(destruct 1; exact _).
