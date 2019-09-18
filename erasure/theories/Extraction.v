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

Extraction Blacklist config uGraph Universes Ast String List Nat Int
           UnivSubst Typing Checker Retyping OrderedType Logic Common Equality Classes.
Set Warnings "-extraction-opaque-accessed".

From MetaCoq.Erasure Require Import EAst EAstUtils EInduction ELiftSubst ETyping Extract ErasureFunction
     SafeTemplateErasure.

Extract Inductive Equations.Init.sigma => "(*)" ["(,)"].

Extract Constant PCUICTyping.fix_guard => "(fun x -> true)".
Extract Constant PCUICTyping.ind_guard => "(fun x -> true)".
Extract Constant PCUICSafeChecker.check_one_ind_body => "(fun _ _ _ _ _ _ _ -> ret envcheck_monad __)".
(* Extract Constant erase_mfix_obligation_1 => "(fun _ _ _ _ => ret typing_monad __)". *)

Cd "src".

Separate Extraction ErasureFunction.erase SafeTemplateErasure
         (* The following directives ensure separate extraction does not produce name clashes *)
         String utils UnivSubst ELiftSubst ETyping.

Cd "..".
