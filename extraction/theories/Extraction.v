(** Extraction setup for template-coq.

    Any extracted code planning to link with the plugin's OCaml reifier
    should use these same directives for consistency.
*)

From TemplateExtraction Require Import Ast.
From TemplateExtraction Require Import Induction.
From TemplateExtraction Require Import LiftSubst.
From TemplateExtraction Require Import UnivSubst.
From TemplateExtraction Require Import Typing.

Require Import FSets.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString ExtrOcamlZInt.

(* Ignore [Decimal.int] before the extraction issue is solved:
   https://github.com/coq/coq/issues/7017. *)
Extract Inductive Decimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".

Extraction Blacklist config uGraph univ Ast String List Nat UnivSubst UnivSubst0
           LiftSubst Induction Typing Retyping Typing0 Checker.
Set Warnings "-extraction-opaque-accessed".

Extraction Library Ast.
Extraction Library UnivSubst.
Extraction Library Induction.
Extraction Library LiftSubst.
Extraction Library Typing.

(** Do it here, otherwise, LiftSubst, Typing etc refer to the ones of Template!
    Side-effect of Require... *)
From TemplateExtraction Require Extract.
Extraction Library Extract.
