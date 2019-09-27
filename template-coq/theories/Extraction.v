(** Extraction setup for template-coq.

    Any extracted code planning to link with the plugin's OCaml reifier
    should use these same directives for consistency.
*)

(* From MetaCoq Require All. *)
Require Import MetaCoq.Template.utils MetaCoq.Template.Ast.
Require Import FSets.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString ExtrOcamlZInt.

(* Ignore [Decimal.int] before the extraction issue is solved:
   https://github.com/coq/coq/issues/7017. *)
Extract Inductive Decimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".

Extract Constant utils.ascii_compare =>
 "fun x y -> match Char.compare x y with 0 -> Eq | x when x < 0 -> Lt | _ -> Gt".

Extraction Blacklist config uGraph Universes Ast String List Nat Int
           UnivSubst Typing Checker Retyping OrderedType Logic Common Equality UnivSubst.
Set Warnings "-extraction-opaque-accessed".

Cd "gen-src".

Require Import MetaCoq.Template.TemplateMonad.Extractable.
From MetaCoq.Template Require Import config Induction LiftSubst UnivSubst Pretty.

Recursive Extraction Library Extractable.
Extraction Library Induction.
Extraction Library LiftSubst.
Extraction Library UnivSubst.
Extraction Library Pretty.
Extraction Library config.

Cd "..".