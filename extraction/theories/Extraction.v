(** Extraction setup for template-coq.

    Any extracted code planning to link with the plugin's OCaml reifier
    should use these same directives for consistency.
*)

Require Import FSets.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString ExtrOcamlZInt.

(* Ignore [Decimal.int] before the extraction issue is solved:
   https://github.com/coq/coq/issues/7017. *)
Extract Inductive Decimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".

Extraction Blacklist config uGraph univ Ast AstUtils String List Nat UnivSubst UnivSubst0
           LiftSubst Induction Typing Retyping Typing0 Checker.
Set Warnings "-extraction-opaque-accessed".

From TemplateExtraction Require Import Ast.
Extraction Library Ast.

From TemplateExtraction Require Import AstUtils.
Extraction Library AstUtils.

From TemplateExtraction Require Import UnivSubst.
Extraction Library UnivSubst.

From TemplateExtraction Require Import Induction.
Extraction Library Induction.

From TemplateExtraction Require Import LiftSubst.
Extraction Library LiftSubst.

From TemplateExtraction Require Import Typing.
Extraction Library Typing.

(** Do it here, otherwise, LiftSubst, Typing etc refer to the ones of Template!
    Side-effect of Require... *)
From TemplateExtraction Require Extract.
Extraction Library Extract.
