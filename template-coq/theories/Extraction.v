(** Extraction setup for template-coq.

    Any extracted code planning to link with the plugin's OCaml reifier
    should use these same directives for consistency.
*)

From Template Require All.

Require Import FSets.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString ExtrOcamlZInt.

(* Ignore [Decimal.int] before the extraction issue is solved:
   https://github.com/coq/coq/issues/7017. *)
Extract Inductive Decimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".

Extract Constant utils.ascii_compare =>
 "fun x y -> match Char.compare x y with 0 -> Eq | x when x < 0 -> Lt | _ -> Gt".

Extraction Blacklist config uGraph univ Ast String List Nat Int
           UnivSubst Typing Checker Retyping OrderedType.
Set Warnings "-extraction-opaque-accessed".

Require Export Template.Ast.

Cd "src".

Require Import Template.TemplateMonad.Extractable.

Recursive Extraction Library TypingWf.
Recursive Extraction Library Checker.
Recursive Extraction Library Retyping.
Recursive Extraction Library Extractable.

Cd "..".