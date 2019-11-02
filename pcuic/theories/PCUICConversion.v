(* Distributed under the terms of the MIT license.   *)
From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega Lia.
From MetaCoq.Template Require Import config utils AstUtils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICReduction PCUICEquality.

Require Import Equations.Type.Relation Equations.Type.Relation_Properties.


(** ** Cumulativity and Conversion ** *)

Reserved Notation " Σ ;;; Γ |- t <= u " (at level 50, Γ, t, u at next level).
Reserved Notation " Σ ;;; Γ |- t = u " (at level 50, Γ, t, u at next level).

Inductive cumul `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| cumul_refl t u : leq_term (global_ext_constraints Σ) t u -> Σ ;;; Γ |- t <= u
| cumul_red_l t u v : red1 Σ.1 Γ t v -> Σ ;;; Γ |- v <= u -> Σ ;;; Γ |- t <= u
| cumul_red_r t u v : Σ ;;; Γ |- t <= v -> red1 Σ.1 Γ u v -> Σ ;;; Γ |- t <= u
where " Σ ;;; Γ |- t <= u " := (cumul Σ Γ t u) : type_scope.


Inductive conv `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| conv_refl t u : eq_term (global_ext_constraints Σ) t u -> Σ ;;; Γ |- t = u
| conv_red_l t u v : red1 Σ Γ t v -> Σ ;;; Γ |- v = u -> Σ ;;; Γ |- t = u
| conv_red_r t u v : Σ ;;; Γ |- t = v -> red1 (fst Σ) Γ u v -> Σ ;;; Γ |- t = u
where " Σ ;;; Γ |- t = u " := (@conv _ Σ Γ t u) : type_scope.


Lemma cumul_alt {cf:checker_flags} Σ Γ t u :
  Σ ;;; Γ |- t <= u <~> ∑ v v', red Σ Γ t v × red Σ Γ u v' × leq_term Σ v v'.
Proof.
  split.
  { induction 1. exists t, u. intuition auto; constructor.
    destruct IHX as (v' & v'' & redv & redv' & leqv).
    exists v', v''. intuition auto. now eapply red_step.
    destruct IHX as (v' & v'' & redv & redv' & leqv).
    exists v', v''. intuition auto. now eapply red_step. }
  { intros [v [v' [redv [redv' Hleq]]]]. apply red_alt in redv.
    apply red_alt in redv'.
    apply clos_rt_rt1n in redv.
    apply clos_rt_rt1n in redv'.
    induction redv. induction redv'. constructor; auto.
    econstructor 3; eauto.
    econstructor 2; eauto. }
Qed.


Lemma conv_alt {cf:checker_flags} Σ Γ t u :
  Σ ;;; Γ |- t = u <~> ∑ v v', red Σ Γ t v × red Σ Γ u v' × eq_term Σ v v'.
Proof.
  split.
  { induction 1. exists t, u. intuition auto; constructor.
    destruct IHX as (v' & v'' & redv & redv' & leqv).
    exists v', v''. intuition auto. now eapply red_step.
    destruct IHX as (v' & v'' & redv & redv' & leqv).
    exists v', v''. intuition auto. now eapply red_step. }
  { intros [v [v' [redv [redv' Hleq]]]]. apply red_alt in redv.
    apply red_alt in redv'.
    apply clos_rt_rt1n in redv.
    apply clos_rt_rt1n in redv'.
    induction redv. induction redv'. constructor; auto.
    econstructor 3; eauto.
    econstructor 2; eauto. }
Qed.




(** ** Context conversion ** *)

Inductive context_relation
          (P : context -> context -> context_decl -> context_decl -> Type)
          : forall (Γ Γ' : context), Type :=
| ctx_rel_nil : context_relation P nil nil
| ctx_rel_vass na na' T U Γ Γ' :
    context_relation P Γ Γ' ->
    P Γ Γ' (vass na T) (vass na' U) ->
    context_relation P (vass na T :: Γ) (vass na' U :: Γ')
| ctx_rel_def na na' t T u U Γ Γ' :
    context_relation P Γ Γ' ->
    P Γ Γ' (vdef na t T) (vdef na' u U) ->
    context_relation P (vdef na t T :: Γ) (vdef na' u U :: Γ').
Derive Signature for context_relation.
Arguments context_relation P Γ Γ' : clear implicits.

Section ConvContext.

  Context {cf:checker_flags} (Σ : global_env_ext).

  Inductive conv_decls (Γ Γ' : context) : forall (x y : context_decl), Type :=
  | conv_vass na na' T T' :
      (* isType Σ Γ' T' -> *)
      Σ ;;; Γ |- T = T' ->
      conv_decls Γ Γ' (vass na T) (vass na' T')

  | conv_vdef_type na na' b T T' :
      (* isType Σ Γ' T' -> *)
      Σ ;;; Γ |- T = T' ->
      conv_decls Γ Γ' (vdef na b T) (vdef na' b T')

  | conv_vdef_body na na' b b' T T' :
      (* isType Σ Γ' T' -> *)
      (* Σ ;;; Γ' |- b' : T' -> *)
      Σ ;;; Γ |- b = b' ->
      Σ ;;; Γ |- T = T' ->
      conv_decls Γ Γ' (vdef na b T) (vdef na' b' T').

End ConvContext.

Notation conv_context Σ Γ Γ' := (context_relation (conv_decls Σ) Γ Γ').
