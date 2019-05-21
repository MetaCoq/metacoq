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

Extraction Blacklist config uGraph universes Ast String List Nat Int
           UnivSubst Typing Checker Retyping OrderedType Classes.
Set Warnings "-extraction-opaque-accessed".

From PCUIC Require Import PCUICAst PCUICAstUtils PCUICUnivSubst PCUICInduction PCUICLiftSubst PCUICTyping
     (* PCUICWeakeningEnv *)
     (* PCUICWeakening *)
     (* PCUICSubstitution *)
     PCUICChecker PCUICRetyping PCUICMetaTheory TemplateToPCUIC.
From Equations Require Import Equations.

(* Should be in Equations *)
(* Extraction Inline Equations.Prop.Classes.noConfusion. *)
(* Extraction Inline Equations.Prop.Logic.eq_elim. *)
(* Extraction Inline Equations.Prop.Logic.eq_elim_r. *)
(* Extraction Inline Equations.Prop.Logic.transport. *)
(* Extraction Inline Equations.Prop.Logic.transport_r. *)
(* Extraction Inline Equations.Prop.Logic.False_rect_dep. *)
(* Extraction Inline Equations.Prop.Logic.True_rect_dep. *)
(* Extraction Inline Equations.Init.pr1. *)
(* Extraction Inline Equations.Init.pr2. *)
(* Extraction Inline Equations.Init.hidebody. *)
(* Extraction Inline Equations.Prop.DepElim.solution_left. *)

(* Extraction Inline NoConfusionPackage_All_local_env_over. *)
(* Extraction Inline NoConfusionPackage_context_decl. *)

Extraction Library Classes.
(* Extraction Library CRelationClasses. *)

Extraction Library PCUICAst.
Extraction Library PCUICAstUtils.
Extraction Library PCUICUnivSubst.
Extraction Library PCUICLiftSubst.
Extraction Library PCUICTyping.
(* Extraction Library PCUICReduction. *)
(* Extraction Library PCUICCumulativity. *)
(* Extraction Library PCUICWeakeningEnv. *)
(* Extraction Library PCUICWeakening. *)
(* Extraction Library PCUICSubstitution. *)
Extraction Library PCUICChecker.
Extraction Library PCUICRetyping.
Extraction Library PCUICMetaTheory.
Extraction Library TemplateToPCUIC.
