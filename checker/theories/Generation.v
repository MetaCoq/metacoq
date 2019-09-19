(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega Lia.
From MetaCoq.Template Require Import config utils Ast AstUtils Induction utils LiftSubst UnivSubst.
From MetaCoq.Checker Require Import Typing.
Require Import ssreflect ssrbool.

(** * Substitution lemmas for typing derivations. *)

Set Asymmetric Patterns.
Close Scope string_scope.

Lemma invert_type_App `{checker_flags} Σ Γ f u T :
  Σ ;;; Γ |- tApp f u : T ->
  { T' : term & { U' & ((Σ ;;; Γ |- f : T') * typing_spine Σ Γ T' u U' *
                        (isApp f = false) * (u <> []) *
                        (Σ ;;; Γ |- U' <= T))%type } }.
Proof.
  intros Hty.
  dependent induction Hty.
  exists t_ty, t'. intuition.
  specialize (IHHty _ _ eq_refl) as [T' [U' [H' H'']]].
  exists T', U'. split; auto.
  eapply cumul_trans; eauto.
Qed.

Lemma type_mkApp `{checker_flags} Σ Γ f u T T' :
  Σ ;;; Γ |- f : T ->
  typing_spine Σ Γ T [u] T' ->
  Σ ;;; Γ |- mkApp f u : T'.
Proof.
  intros Hf Hu. inv Hu.
  simpl. destruct (isApp f) eqn:Happ.
  destruct f; try discriminate. simpl.
  eapply invert_type_App in Hf.
  destruct Hf as (T'' & U' & (((Hf & HU) & Happf) & Hunil) & Hcumul).
  eapply type_App; eauto. intro. destruct args; discriminate.
  inv X2. clear Happ Hf Hunil.
  induction HU. simpl. econstructor; eauto.
  eapply cumul_trans; eauto.
  econstructor. econstructor. eapply t. eauto. eauto.
  apply IHHU; eauto.
  rewrite -> mkApp_tApp; eauto.
  econstructor; eauto. congruence.
  econstructor; eauto.
Qed.

Lemma type_mkApps `{checker_flags} Σ Γ f u T T' :
  Σ ;;; Γ |- f : T ->
  typing_spine Σ Γ T u T' ->
  Σ ;;; Γ |- mkApps f u : T'.
Proof.
  intros Hf Hu. induction Hu in f, Hf |- *. auto.
  rewrite <- mkApps_mkApp.
  eapply IHHu. eapply type_mkApp. eauto.
  econstructor; eauto. constructor.
Qed.
