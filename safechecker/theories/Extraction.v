(* Distributed under the terms of the MIT license. *)
Require Import OrdersTac ExtrOcamlBasic ExtrOcamlString ExtrOcamlZInt.
Require Import MetaCoq.Template.utils.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker PCUICSafeConversion
     SafeTemplateChecker.

(** * Extraction setup for the safechecker phase of MetaCoq.

    Any extracted code planning to link with the plugin's OCaml reifier
    should use these same directives for consistency.
*)


(* Ignore [Decimal.int] before the extraction issue is solved:
   https://github.com/coq/coq/issues/7017. *)
Extract Inductive Decimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".

Extract Constant ascii_compare =>
 "fun x y -> match Char.compare x y with 0 -> Eq | x when x < 0 -> Lt | _ -> Gt".

Extraction Blacklist Classes config uGraph Universes Ast String List Nat Int Init
           UnivSubst Typing Checker Retyping OrderedType Logic Common Equality Classes.
Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-reserved-identifier".

Extraction Inline PCUICSafeConversion.Ret.

Extract Inductive Equations.Init.sigma => "( * )" ["(,)"].
Extract Constant Equations.Init.pr1 => "fst".
Extract Constant Equations.Init.pr2 => "snd".
Extraction Inline Equations.Init.pr1 Equations.Init.pr2.
Extraction Inline Equations.Prop.Logic.transport Equations.Prop.Logic.transport_r MCEquality.transport.

Extract Constant PCUICTyping.fix_guard => "(fun x -> true)".
Extract Constant PCUICTyping.cofix_guard => "(fun x -> true)".
Extract Constant PCUICTyping.ind_guard => "(fun x -> true)".

Cd "src".

Separate Extraction MakeOrderTac PCUICSafeChecker.typecheck_program
         SafeTemplateChecker.infer_and_print_template_program
         (* The following directives ensure separate extraction does not produce name clashes *)
         Coq.Strings.String utils UnivSubst PCUICPretty.

Cd "..".
