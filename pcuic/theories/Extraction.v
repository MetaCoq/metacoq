(** Extraction setup for the pcuic phase of template-coq.

    Any extracted code planning to link with the plugin's OCaml reifier
    should use these same directives for consistency.
*)

Require Import FSets.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString ExtrOcamlZInt.

(* Ignore [Decimal.int] before the extraction issue is solved:
   https://github.com/coq/coq/issues/7017. *)
Extract Inductive Decimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".

Extraction Blacklist config uGraph univ Ast String List Nat Int
           UnivSubst Typing Checker Retyping OrderedType.
Set Warnings "-extraction-opaque-accessed".

From PCUIC Require Import PCUICAst PCUICAstUtils PCUICUnivSubst PCUICInduction PCUICLiftSubst PCUICTyping
     TemplateToPCUIC.

Extraction Library PCUICAst.
Extraction Library PCUICAstUtils.
Extraction Library PCUICUnivSubst.
Extraction Library PCUICInduction.
Extraction Library PCUICLiftSubst.
Extraction Library PCUICTyping.
Extraction Library TemplateToPCUIC.
