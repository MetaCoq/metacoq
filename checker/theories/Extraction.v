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
           UnivSubst Typing Checker Retyping OrderedType Logic Common Equality.
Set Warnings "-extraction-opaque-accessed".

Require Export MetaCoq.Template.Ast.
From MetaCoq.Checker Require All.

Cd "src".

(** From Coq: well-founded relations *)
Extraction Library Wf.
Extraction Library Compare_dec.
Extraction Library MSetList.

(** From checker *)
Extraction Library LiftSubst.
Extraction Library UnivSubst.
Extraction Library monad_utils.
Extraction Library Typing.
Extraction Library TypingWf.
Extraction Library wGraph.
Extraction Library uGraph.
Extraction Library Checker.
Extraction Library Retyping.

Cd "..".