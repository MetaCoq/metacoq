(* Distributed under the terms of the MIT license. *)
From Coq Require Import OrdersTac Ascii ExtrOcamlBasic ExtrOcamlString ExtrOcamlZInt ExtrOCamlInt63 ExtrOCamlFloats.
From MetaCoq.Template Require Import utils MC_ExtrOCamlZPosInt.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker PCUICSafeConversion
     SafeTemplateChecker.

(** * Extraction setup for the safechecker phase of MetaCoq.

    Any extracted code planning to link with the plugin's OCaml reifier
    should use these same directives for consistency.
*)
        
(* Ignore [Decimal.int] before the extraction issue is solved:
    https://github.com/coq/coq/issues/7017. *)
Extract Inductive Decimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".
Extract Inductive Hexadecimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".
Extract Inductive Number.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".

(** Here we could extract uint63_from/to_model to the identity *)

Extract Constant ascii_compare =>
 "fun x y -> Char.compare".

Extraction Blacklist Classes config uGraph Universes Ast String List Nat Int Init
           UnivSubst Typing Checker Retyping OrderedType Logic Common Equality Classes
           Uint63.
Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-reserved-identifier".

Extraction Inline PCUICSafeConversion.Ret.

Extract Inductive Equations.Init.sigma => "( * )" ["(,)"].
Extract Constant Equations.Init.pr1 => "fst".
Extract Constant Equations.Init.pr2 => "snd".
Extraction Inline Equations.Init.pr1 Equations.Init.pr2.
Extraction Inline Equations.Prop.Logic.transport Equations.Prop.Logic.transport_r MCEquality.transport.
Extraction Inline Equations.Prop.Logic.True_rect_dep Equations.Prop.Logic.False_rect_dep.

(** This Inline is because of a problem of weak type variables (partial application?) *)
Extraction Inline PCUICPrimitive.prim_val_reflect_eq.

Extract Constant PCUICTyping.guard_checking => 
  "(fun _ _ _ _ -> true)".

Cd "src".

Separate Extraction MakeOrderTac PCUICSafeChecker.typecheck_program
         SafeTemplateChecker.infer_and_print_template_program
         (* The following directives ensure separate extraction does not produce name clashes *)
         Coq.Strings.String utils UnivSubst PCUICPretty.

Cd "..".
