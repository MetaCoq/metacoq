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

Require Import Template.Ast.

Extract Inductive BasicAst.cast_kind => "Constr.cast_kind"
  [ "Constr.VMcast" "Constr.NATIVEcast" "Constr.DEFAULTcast" "Constr.REVERTcast" ].

Extract Inductive Ast.term =>
  "Constr.t" [ "Coq_constr.tRel"
             "Coq_constr.tVar"
             "Coq_constr.tMeta"
             "Coq_constr.tEvar"
             "Coq_constr.tSort"
             "Coq_constr.tCast"
             "Coq_constr.tProd"
             "Coq_constr.tLambda"
             "Coq_constr.tLetIn"
             "Coq_constr.tApp"
             "Coq_constr.tConst"
             "Coq_constr.tInd"
             "Coq_constr.tConstruct"
             "Coq_constr.tCase"
             "Coq_constr.tProj"
             "Coq_constr.tFix"
             "Coq_constr.tCoFix" ] "Coq_constr.constr_match".

Cd "gen-src".

Require Import Template.TemplateMonad.Extractable.

Recursive Extraction Library Extractable.

Cd "..".