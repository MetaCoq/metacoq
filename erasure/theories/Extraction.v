(** Extraction setup for the erasure phase of template-coq.

    Any extracted code planning to link with the plugin
    should use these same directives for consistency.
*)

Require Import FSets.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString ExtrOcamlZInt.

(* Ignore [Decimal.int] before the extraction issue is solved:
   https://github.com/coq/coq/issues/7017. *)
Extract Inductive Decimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".

Extraction Blacklist config uGraph Universes Ast String List Nat UnivSubst
           LiftSubst Induction Typing Retyping Checker.
Set Warnings "-extraction-opaque-accessed".

From MetaCoq.Erasure Require Import EAst EAstUtils EInduction ELiftSubst ETyping Extract ErasureFunction.

(* Extraction Library ssreflect. *)
(* Extraction Library EAst. *)
(* Extraction Library EAstUtils. *)
(* Extraction Library EInduction. *)
(* Extraction Library ELiftSubst. *)
(* Extraction Library ETyping. *)
(* Extraction Library Extract. *)
(* Extraction Library ErasureFunction. *)

Separate Extraction ErasureFunction.erase.