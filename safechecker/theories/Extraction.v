(** Extraction setup for the safechecker phase of MetaCoq.

    Any extracted code planning to link with the plugin's OCaml reifier
    should use these same directives for consistency.
*)

Require Import FSets.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString ExtrOcamlZInt.

From MetaCoq.SafeChecker Require Import PCUICSafeChecker PCUICSafeConversion.
From MetaCoq.Template Require Import Extraction.


(* Ignore [Decimal.int] before the extraction issue is solved:
   https://github.com/coq/coq/issues/7017. *)
Extract Inductive Decimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".

Extract Constant utils.ascii_compare =>
 "fun x y -> match Char.compare x y with 0 -> Eq | x when x < 0 -> Lt | _ -> Gt".

Extraction Blacklist config uGraph universes Ast String List Nat Int
           UnivSubst Typing Checker Retyping OrderedType Classes.
Set Warnings "-extraction-opaque-accessed".

Extraction Inline PCUICSafeConversion.Ret.

Cd "src".

Separate Extraction MakeOrderTac PCUICSafeChecker.infer_term.

Cd "..".