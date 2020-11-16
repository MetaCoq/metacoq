(* Distributed under the terms of the MIT license. *)
Require Import FSets ExtrOcamlBasic ExtrOcamlString ExtrOcamlZInt.

(** * Extraction setup for the erasure phase of template-coq.

    Any extracted code planning to link with the plugin
    should use these same directives for consistency.
*)


(* Ignore [Decimal.int] before the extraction issue is solved:
   https://github.com/coq/coq/issues/7017. *)
Extract Inductive Decimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".

Extraction Blacklist Classes config uGraph Universes Ast String List Nat Int
           UnivSubst Typing Checker Retyping OrderedType Logic Common Equality Classes.
Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-reserved-identifier".

From MetaCoq.Erasure Require Import EAst EAstUtils EInduction ELiftSubst ETyping Extract ErasureFunction Erasure.

Extraction Inline Equations.Prop.Classes.noConfusion.
Extraction Inline Equations.Prop.Logic.eq_elim.
Extraction Inline Equations.Prop.Logic.eq_elim_r.
Extraction Inline Equations.Prop.Logic.transport.
Extraction Inline Equations.Prop.Logic.transport_r.
Extraction Inline Equations.Prop.Logic.False_rect_dep.
Extraction Inline Equations.Prop.Logic.True_rect_dep.
Extraction Inline Equations.Init.pr1.
Extraction Inline Equations.Init.pr2.
Extraction Inline Equations.Init.hidebody.
Extraction Inline Equations.Prop.DepElim.solution_left.

Extract Inductive Equations.Init.sigma => "( * )" ["(,)"].

Extract Constant PCUICTyping.fix_guard => "(fun x -> true)".
Extract Constant PCUICTyping.cofix_guard => "(fun x -> true)".
Extract Constant PCUICTyping.ind_guard => "(fun x -> true)".
Extract Constant PCUICSafeChecker.check_one_ind_body => "(fun _ _ _ _ _ _ _ -> ret envcheck_monad __)".
(* Extract Constant erase_mfix_obligation_1 => "(fun _ _ _ _ => ret typing_monad __)". *)

Cd "src".

Separate Extraction ErasureFunction.erase Erasure
         (* The following directives ensure separate extraction does not produce name clashes *)
         Coq.Strings.String utils Template.UnivSubst ELiftSubst ETyping.

Cd "..".
