(* Distributed under the terms of the MIT license. *)
From Coq Require Import OrdersTac Ascii ExtrOcamlBasic ExtrOCamlInt63 ExtrOCamlFloats.
From MetaCoq.Template Require Import utils. 
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

Cd "src".
Axiom fake_abstract_guard_impl_properties:
  forall (fix_cofix : PCUICTyping.FixCoFix)
    (Σ : PCUICAst.PCUICEnvironment.global_env_ext)
    (Γ : PCUICAst.PCUICEnvironment.context)
    (mfix : BasicAst.mfixpoint PCUICAst.term),
    PCUICTyping.guard fix_cofix Σ Γ mfix <->
      PCUICWfEnvImpl.fake_guard_impl fix_cofix Σ Γ mfix.

#[local,program] Instance fake_abstract_guard_impl : PCUICWfEnvImpl.abstract_guard_impl := 
  {
    guard_impl := PCUICWfEnvImpl.fake_guard_impl
  }.
Next Obligation. eapply fake_abstract_guard_impl_properties. Qed.

Definition infer_and_print_template_program_with_guard {cf} {nor} := 
  @SafeTemplateChecker.infer_and_print_template_program cf nor fake_abstract_guard_impl.

Separate Extraction MakeOrderTac PCUICSafeChecker.typecheck_program
         infer_and_print_template_program_with_guard
         (* The following directives ensure separate extraction does not produce name clashes *)
         Coq.Strings.String utils UnivSubst PCUICPretty.

Cd "..".
