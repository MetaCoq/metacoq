(** Extraction setup for the extraction phase of template-coq.

    Any extracted code planning to link with the plugin's OCaml reifier
    should use these same directives for consistency.
*)

Require Import FSets.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString ExtrOcamlZInt.

(* Ignore [Decimal.int] before the extraction issue is solved:
   https://github.com/coq/coq/issues/7017. *)
Extract Inductive Decimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".

Extraction Blacklist config uGraph univ Ast String List Nat UnivSubst
           LiftSubst Induction Typing Retyping Checker.
Set Warnings "-extraction-opaque-accessed".

From TemplateExtraction Require Import EAst EAstUtils EUnivSubst EInduction ELiftSubst ETyping Extract.

Extraction Library EAst.
Extraction Library EAstUtils.
Extraction Library EUnivSubst.
Extraction Library EInduction.
Extraction Library ELiftSubst.
Extraction Library ETyping.
Extraction Library Extract.
