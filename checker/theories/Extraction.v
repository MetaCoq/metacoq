(** Extraction setup for template-coq.

    Any extracted code planning to link with the plugin's OCaml reifier
    should use these same directives for consistency.
*)

(* From MetaCoq.Template Require All. *)
Require Import MetaCoq.Template.utils.
Require Import FSets.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString ExtrOcamlZInt.

(* Ignore [Decimal.int] before the extraction issue is solved:
   https://github.com/coq/coq/issues/7017. *)
Extract Inductive Decimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".

Extract Constant utils.ascii_compare =>
 "fun x y -> match Char.compare x y with 0 -> Eq | x when x < 0 -> Lt | _ -> Gt".

Extraction Blacklist config uGraph Universes Ast String List Nat Int
           Reduction Conversion
           UnivSubst Typing Checker Retyping OrderedType Logic (* Logic0 *) Common Equality.
Set Warnings "-extraction-opaque-accessed".

Require Export MetaCoq.Template.Ast.
From MetaCoq.Checker Require All.

Cd "src".

(** From Coq: well-founded relations *)
Extraction Library Wf.
Extraction Library Compare_dec.
Extraction Library MSetList.

Extraction Library Init.

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

(* Extraction Library Logic. *)
Extraction Library Signature.
Extraction Library Classes.
(* Extraction Library Relation_Properties. *)
Extraction Library ssreflect.
(* Extraction Library Relation. *)
Extraction Library CMorphisms.

(** From checker *)
Extraction Library EnvironmentTyping.
Extraction Library Reflect.
Extraction Library LiftSubst.
Extraction Library UnivSubst.
Extraction Library monad_utils.
Extraction Library Reduction.
Extraction Library Conversion.
Extraction Library Typing.
Extraction Library TypingWf.
Extraction Library wGraph.
Extraction Library uGraph.
Extraction Library Checker.
Extraction Library Retyping.

Cd "..".