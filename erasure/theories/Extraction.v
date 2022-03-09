(* Distributed under the terms of the MIT license. *)
From Coq Require Import Ascii FSets ExtrOcamlBasic ExtrOcamlString ExtrOcamlZInt ExtrOCamlFloats ExtrOCamlInt63.
From MetaCoq.Template Require Import utils.

(** * Extraction setup for the erasure phase of template-coq.

    Any extracted code planning to link with the plugin
    should use these same directives for consistency.
*)

Extract Constant ascii_compare =>
 "fun x y -> match Char.compare x y with 0 -> 0 | x when x < 0 -> -1 | _ -> 1".
 
Extraction Blacklist Classes config uGraph Universes Ast String List Nat Int
           UnivSubst Typing Checker Retyping OrderedType Logic Common ws_cumul_pb Classes Numeral
           Uint63.
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
Extract Constant Equations.Init.pr1 => "fst".
Extract Constant Equations.Init.pr2 => "snd".
Extraction Inline Equations.Init.pr1 Equations.Init.pr2.

Extract Constant PCUICWfEnv.guard_impl => 
  "(fun _ _ _ _ -> true)".

Extract Constant PCUICTyping.guard_checking => "{ fix_guard = (fun _ _ _ -> true); cofix_guard = (fun _ _ _ -> true) }".

Cd "src".

Separate Extraction ErasureFunction.erase Erasure
         (* The following directives ensure separate extraction does not produce name clashes *)
         Coq.Strings.String utils Template.UnivSubst ELiftSubst ETyping.

Cd "..".
