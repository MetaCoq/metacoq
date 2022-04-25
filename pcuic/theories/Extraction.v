(* Distributed under the terms of the MIT license. *)
Require Import MetaCoq.Template.utils.
Require Import FSets ssreflect ExtrOcamlBasic ExtrOcamlZInt.

(** * Extraction setup for the pcuic phase of MetaCoq.

    Any extracted code planning to link with the plugin's OCaml reifier
    should use these same directives for consistency.
*)

Extraction Blacklist Classes config uGraph universes Ast String List Logic Logic0 Nat Int
           UnivSubst Typing Checker Retyping OrderedType Classes equality.
Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-reserved-identifier".

Cd "src".

Extraction Library Init.

From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICUnivSubst
  PCUICInduction PCUICLiftSubst PCUICTyping PCUICNormal PCUICSafeLemmata
  PCUICEquality (* PCUICWeakeningEnv *) (* PCUICWeakening *)
  (* PCUICSubstitution *) PCUICPretty TemplateToPCUIC.
From Equations Require Import Equations.

(* Should be in Equations *)
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

Extraction Inline MCEquality.transport.
(* Extraction Inline NoConfusionPackage_All_local_env_over. *)
(* Extraction Inline NoConfusionPackage_context_decl. *)
Extraction Library Signature.
Extraction Library Classes.
Extraction Library ssreflect.
(* Extraction Library Relation. *)
Extraction Library CMorphisms.
(* The following allows to test the failure of extraction Bugs in extraction! *)
(* Extract Constant Relation_Properties.clos_rt_is_preorder => "(Obj.magic 0)". *)
(* Extract Constant CRelationClasses.eq_equivalence => "(Obj.magic __)". *)
(* Separate Extraction PCUICNormal PCUICAst PCUICAstUtils PCUICUnivSubst PCUICLiftSubst PCUICReflect PCUICPosition *)
(*          PCUICCumulativity PCUICSubstitution *)
(*          (* PCUICTyping PCUICEquality *) *)
(*          TemplateToPCUIC (* PCUICSafeLemmata *). *)
Extraction Library PCUICAst.
Extraction Library PCUICAstUtils.
Extraction Library PCUICUtils.
Extraction Library PCUICInduction.
Extraction Library PCUICUnivSubst.
Extraction Library PCUICLiftSubst.
Extraction Library PCUICReflect.
Extraction Library EqDecInstances.
Extraction Library PCUICEquality.
Extraction Library PCUICTyping.
Extraction Library TemplateToPCUIC.
Extraction Library PCUICPretty.
Cd "..".
