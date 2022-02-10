(* Distributed under the terms of the MIT license. *)
(** * Extraction setup for template-coq.

    Any extracted code planning to link with the plugin's OCaml reifier
    should use these same directives for consistency.
*)

From Coq Require Ascii Extraction ZArith NArith.
From MetaCoq.Template Require Import utils Ast Reflect Induction.
From Coq Require Import FSets ExtrOcamlBasic ExtrOcamlString ExtrOCamlFloats
    ExtrOCamlInt63.
From MetaCoq.Template Require Import MC_ExtrOCamlNatInt MC_ExtrOCamlZPosInt.

Extract Constant ascii_compare =>
 "fun x y -> match Char.compare x y with 0 -> Eq | x when x < 0 -> Lt | _ -> Gt".
Extract Constant Ascii.compare =>
 "fun x y -> match Char.compare x y with 0 -> Eq | x when x < 0 -> Lt | _ -> Gt".
 
Extract Inductive Equations.Init.sigma => "( * )" ["(,)"].
Extract Constant Equations.Init.pr1 => "fst".
Extract Constant Equations.Init.pr2 => "snd".
Extraction Inline Equations.Init.pr1 Equations.Init.pr2.

Extraction Blacklist Classes config uGraph Universes Ast String List Nat Int
           UnivSubst Typing Checker Retyping OrderedType Logic Common Equality UnivSubst Numeral
           Uint63.
Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-reserved-identifier".

Cd "gen-src".

From MetaCoq.Template Require Import TemplateMonad.Extractable config Induction
     LiftSubst UnivSubst Pretty.
Import Init.Nat.

(* Silence the warnings for specifications axioms of int63 *)
Set Warnings "-extraction-logical-axiom".
(* Floats *)
(* Extraction Library Zeven.
Extraction Library Zeven.
Extraction Library ZArith_dec.
Extraction Library Sumbool.
Extraction Library Zbool.
Extraction Library SpecFloat. *)
Separate Extraction FloatOps.Prim2SF.

Recursive Extraction Library Extractable.
Extraction Library MCPrelude.
Extraction Library MCOption.
Extraction Library MCUtils.
Extraction Library MCList.
Extraction Library EqDecInstances.
Extraction Library Induction.
Extraction Library LiftSubst.
Extraction Library UnivSubst.
Extraction Library BasicAst.

Extraction Library Reflect.
Extraction Library Pretty.
Extraction Library config.

Cd "..".
