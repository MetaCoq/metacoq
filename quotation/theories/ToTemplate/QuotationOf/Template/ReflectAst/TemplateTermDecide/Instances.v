From MetaCoq.Template Require Import Ast ReflectAst.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Common Require Import Environment.Sig.

Module qTemplateTermDecide <: QuotationOfTermDecide TemplateTerm TemplateTermDecide.
  MetaCoq Run (tmMakeQuotationOfModule everything None "TemplateTermDecide").
End qTemplateTermDecide.
