(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega Lia.
From Template Require Import config utils monad_utils BasicAst AstUtils.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICTyping PCUICWeakening PCUICSubstitution PCUICChecker PCUICRetyping PCUICMetaTheory PCUICWcbvEval PCUICSR PCUICValidity.
From TemplateExtraction Require Import EAst ELiftSubst ETyping EWcbvEval Extract Prelim.
From Equations Require Import Equations.
Require Import String.
Local Open Scope list_scope.
Set Asymmetric Patterns.
Import MonadNotation.

Existing Instance config.default_checker_flags.
Module PA := PCUICAst.
Module P := PCUICWcbvEval.

Inductive free : nat -> term -> Prop :=
| free_tRel x : free x (tRel x)
| free_tApp1 x s t : free x s -> free x (tApp s t)
| free_tApp2 x s t : free x t -> free x (tApp s t)
| free_tLambda x na s : free (S x) s -> free x (tLambda na s)
| free_tProj x p s : free x s -> free x (tProj p s)
| free_tFix x mfix n d : free (#|mfix| + x) (d.(dbody)) -> In d mfix -> free x (tFix mfix n)
(* | free_tCoFix x m n : free x (tCoFix m n) *)
| free_tCase1 x p s brs : free x s -> free x (tCase p s brs)
| free_tCase2 x p s brs n b : free x b -> In (n, b) brs -> free x (tCase p s brs).

Lemma subst_free_ext sigma tau t :
  (forall n, free n t -> nth_error sigma n = nth_error tau n) -> subst sigma 0 t = subst tau 0 t.
Admitted.




(** ** Weakening *)

Lemma extract_weakening (Σ : PCUICAst.global_context) (Γ Γ' : PCUICAst.context) (t T : PCUICAst.term) :
    wf Σ ->
    wf_local Σ (Γ ,,, Γ') ->
    Σ;;; Γ |- t : T ->
    extract Σ (Γ ,,, Γ') (PCUICLiftSubst.lift #|Γ'| 0 t) = lift #|Γ'| 0 (extract Σ Γ t).
Admitted.

(* (** ** Substitution *) *)
  
(* Lemma is_arity_subst Σ Γ Γ' Δ a s : *)
(*   wf Σ -> subslet Σ Γ s Γ' -> *)
(*   (* Σ ;;; Γ ,,, Γ' ,,, Δ |- a : T -> *) *)
(*   wf_local Σ (Γ ,,, subst_context s 0 Δ) -> *)
(*   is_arity Σ (Γ ,,, Γ' ,,, Δ) _ a = is_arity Σ (Γ ,,, subst_context s 0 Δ) _ (PCUICLiftSubst.subst s #|Δ| a).  *)
(* Proof. *)
(* Admitted. *)

(* (* this is probably too strict, a might also be an algebraic universe *) *)
(* Lemma type_of_subst Σ Γ Γ' Δ a T s T' : *)
(*   wf Σ -> subslet Σ Γ s Γ' -> *)
(*   Σ ;;; Γ ,,, Γ' ,,, Δ |- a : T -> *)
(*   wf_local Σ (Γ ,,, subst_context s 0 Δ) -> *)
(*   type_of Σ (Γ ,,, Γ' ,,, Δ) a = Checked T' -> *)
(*   type_of Σ (Γ ,,, subst_context s 0 Δ) (PCUICLiftSubst.subst s #|Δ| a) = Checked (PCUICLiftSubst.subst s #|Δ| T'). *)
(* Proof. *)
(* Admitted. *)

(* Lemma reduce_to_sort_subst: *)
(*   forall (H : Fuel) (Σ : PCUICAst.global_context) (Γ Γ' Δ : PCUICAst.context) *)
(*     (s : list PCUICAst.term), *)
(*     wf Σ -> *)
(*     subslet Σ Γ s Γ' -> *)
(*     wf_local Σ (Γ ,,, subst_context s 0 Δ) -> *)
(*     forall a0 : PCUICAst.term, *)
(*       reduce_to_sort (fst Σ) (Γ ,,, subst_context s 0 Δ) (PCUICLiftSubst.subst s #|Δ| a0) = *)
(*       reduce_to_sort (fst Σ) (Γ ,,, Γ' ,,, Δ) a0. *)
(* Proof. *)
(*   intros H Σ Γ Γ' Δ s X X0 X2 a0. *)
(* Admitted. *)

(* Lemma type_of_as_sort_subst Σ Γ Γ' Δ a s T : *)
(*   wf Σ -> subslet Σ Γ s Γ' -> *)
(*   Σ ;;; Γ ,,, Γ' ,,, Δ |- a : T -> *)
(*   wf_local Σ (Γ ,,, subst_context s 0 Δ) -> *)
(*   type_of_as_sort Σ (type_of Σ) (Γ ,,, subst_context s 0 Δ) *)
(*       (PCUICLiftSubst.subst s #|Δ| a) = type_of_as_sort Σ (type_of Σ) (Γ ,,, Γ' ,,, Δ) a. *)
(* Proof. *)
(*   intros. unfold type_of_as_sort. *)
(*   destruct type_of eqn:E at 2. *)
(*   eapply type_of_subst in E; eauto. *)
(*   - rewrite E. simpl. eapply reduce_to_sort_subst; eauto. *)
(*   - edestruct type_of_complete; eauto. congruence. *)
(* Qed. *)

Lemma is_type_subst Σ Γ Γ' Δ a T s :
  wf Σ -> subslet Σ Γ s Γ' ->
  Σ ;;; Γ ,,, Γ' ,,, Δ |- a : T ->
  wf_local Σ (Γ ,,, subst_context s 0 Δ) ->
  is_type_or_proof Σ (Γ ,,, subst_context s 0 Δ) (PCUICLiftSubst.subst s #|Δ| a) = Extract.is_type_or_proof Σ (Γ ,,, Γ' ,,, Δ) a.
Proof.
  intros.
  (* unfold is_type_or_proof. *)
  (* destruct type_of eqn:E at 2. *)
  (* - assert (E' := E). *)
  (*   eapply type_of_sound in E' as []; eauto. *)
  (*   eapply type_of_subst in E; eauto. rewrite E. simpl. *)
  (*   destruct is_arity eqn:Ea at 2. *)
  (*   + erewrite is_arity_subst in Ea; eauto. rewrite Ea. reflexivity. *)
  (*   + erewrite is_arity_subst in Ea; eauto. rewrite Ea. *)
  (*     erewrite type_of_as_sort_subst with (Γ'0 := Γ'); eauto. admit.  *)
  (* - edestruct type_of_complete; eauto. congruence. *)
Admitted.


Lemma extract_subst Σ Γ Γ' Δ a s T :
  wf Σ ->
  subslet Σ Γ s Γ' ->
  wf_local Σ (Γ ,,, subst_context s 0 Δ) ->
  Σ ;;; Γ ,,, Γ'  ,,, Δ |- a : T ->
  extract Σ (Γ ,,, subst_context s 0 Δ) (PCUICLiftSubst.subst s #|Δ| a) = subst  (map (extract Σ Γ) s) #|Δ| (extract Σ (Γ,,,Γ',,,Δ) a).
Proof.
  (* intros HΣ HΔ Hs Ha. *)
  (* pose proof (typing_wf_local Ha). *)
  (* generalize_eqs Ha. intros eqw. rewrite <- eqw in X. *)
  (* revert Γ Γ' Δ s Hs HΔ eqw. *)
  (* revert Σ HΣ Γ0 X a T Ha. *)
  (* eapply (typing_ind_env (fun Σ Γ0 a T => *)
  (*                           forall (Γ Γ' : PCUICAst.context) Δ (s : list PCUICAst.term), *)
  (*                             wf_local Σ (Γ ,,, subst_context s 0 Δ) -> *)
  (*                             subslet Σ Γ s Γ' -> *)
  (*                             Γ0 = Γ ,,, Γ' ,,, Δ -> *)
  (*                             extract Σ (Γ ,,, Γ' ,,, Δ) a = Checked a' -> *)
  (*                             Forall2 (fun (a0 : PCUICAst.term) (b : E.term) => extract Σ Γ a0 = Checked b) s s' -> *)
  (*                             extract Σ (Γ ,,, subst_context s 0 Δ) (PCUICLiftSubst.subst s #|Δ| a) = Checked (subst s' #|Δ| a'))); *)
  (* intros Σ wfΣ Γ0 wfΓ0; intros; simpl in * |-; subst Γ0. *)
  (* - destruct ? in H2; try congruence. *)
  (*   destruct a. *)
  (*   + inv H2. eapply is_type_extract. *)
  (*     erewrite is_type_subst; eauto. *)
  (*     econstructor; eauto. *)
  (*   + inv H2. simpl. *)
  (*     elim (leb_spec_Set); intros Hn. *)
  (*     elim nth_error_spec. *)
  (*     * intros x Heq Hlt. *)
  (*       pose proof (substlet_length X1). rewrite H1 in *. *)
  (*       rewrite -> nth_error_app_context_ge in H0 by lia. *)
  (*       rewrite -> nth_error_app_context_lt in H0 by lia. *)
  (*       eapply Forall2_nth_error_Some in H3 as (? & ? & ?); eauto. *)
  (*       rewrite H2. *)
  (*       eapply subslet_nth_error in Heq; eauto. *)
  (*        destruct decl, decl_body; *)
  (*          cbn -[skipn] in Heq. *)
  (*       -- destruct Heq as [-> ]. *)
  (*          eapply (extract_weakening _ _ (subst_context s 0 Δ)) in H3; eauto. *)
  (*          rewrite subst_context_length in H3; eauto. *)
  (*       -- eapply (extract_weakening _ _ (subst_context s 0 Δ)) in H3; eauto. *)
  (*          rewrite subst_context_length in H3; eauto. *)
  (*     * intros Hs. *)
  (*       pose proof (substlet_length X1). *)
  (*       eapply Forall2_length in H3. rewrite H3 in *. *)
  (*       assert (Hs' := Hs). *)
  (*       eapply nth_error_None in Hs. rewrite Hs. *)
  (*       simpl. *)
  (*       erewrite <- is_type_subst in E; eauto. *)
  (*       cbn - [is_type_or_proof] in E. *)
  (*       revert E. elim (leb_spec_Set); intros; try lia. *)
  (*       2: econstructor; eauto. *)
  (*       rewrite <- H3 in Hs'. *)
  (*       eapply nth_error_None in Hs'. *)
  (*       rewrite Hs' in E. *)
  (*       rewrite H3 in *. *)
  (*       now rewrite E. *)
  (*     * assert (sub := X1). *)
  (*       eapply subslet_nth_error_lt in X1; eauto. *)
  (*       rewrite H0 in X1. simpl in X1. *)
  (*       simpl. *)
  (*       erewrite <- is_type_subst in E; eauto. *)
  (*       cbn - [is_type_or_proof] in E. *)
  (*       revert E. elim (leb_spec_Set); intros; try lia. *)
  (*       2: econstructor; eauto. *)
  (*       now rewrite E. *)
  (* -  *)
Admitted.

Lemma extract_subst_alt Σ Γ Γ' Δ a s T :
  wf Σ ->
  subslet Σ Γ s Γ' ->
  Σ ;;; Γ ,,, Γ'  ,,, Δ |- a : T ->
  extract Σ (Γ ,,, subst_context s 0 Δ) (PCUICLiftSubst.subst s #|Δ| a) = subst  (map (extract Σ Γ) s) #|Δ| (extract Σ (Γ,,,Γ',,,Δ) a).
Proof.
  intros.
  eapply extract_subst; eauto. (* clear H0 H1 a' H s'. *)
  eapply All_local_env_app_inv.
  apply typing_wf_local in X1; eauto.
  apply All_local_env_app in X1 as [X1 X2].
  apply All_local_env_app in X1. intuition.
  induction X2; simpl; rewrite ?subst_context_snoc0; econstructor; eauto.
  destruct t0 as [u tu].
  eapply substitution in tu; simpl in *; eauto.
  eapply All_local_env_app_inv; intuition.
  eapply substitution in t0; simpl in *; eauto.
  eapply All_local_env_app_inv; intuition.
Qed.

Lemma extract_subst1 
      (Σ : PCUICAst.global_context) (na : name) (t b a' : PCUICAst.term) T :
  wf Σ -> Σ ;;; [] ,, PCUICAst.vass na t |- b : T -> Σ ;;; [] |- a' : t ->
      extract Σ [] (PCUICLiftSubst.subst1 a' 0 b) = (extract Σ [PCUICAst.vass na t] b) {0 := extract Σ [] a'}.
Proof.
  intros HΣ Ht Hu.
  assert (wfΓ : wf_local Σ []).
  apply typing_wf_local in Hu; eauto. intros.
  pose proof (extract_subst_alt Σ [] [PCUICAst.vass na t] [] b [a'] T) as thm.
  forward thm. eauto.
  forward thm. econstructor. econstructor. rewrite PCUICLiftSubst.subst_empty; auto.
  now apply (thm Ht).
Qed.

Lemma extract_subst1_vdef
      (Σ : PCUICAst.global_context) (na : name) (t b a' : PCUICAst.term) T :
  wf Σ -> Σ ;;; [] ,, PCUICAst.vdef na a' t |- b : T -> Σ ;;; [] |- a' : t ->
      extract Σ [] (PCUICLiftSubst.subst1 a' 0 b) = (extract Σ [PCUICAst.vdef na a' t] b) {0 := extract Σ [] a'}.
Proof.
  intros HΣ Ht.
  assert ((wf_local Σ []) * (Σ ;;; [] |- a' : t)%type) as [wfΓ tyu].
  apply typing_wf_local in Ht; eauto with wf. 
  now depelim Ht; simpl in *; unfold PCUICAst.vdef, PCUICAst.vass in H; noconf H. 
  intros.
  epose proof (extract_subst_alt Σ [] [PCUICAst.vdef na a' t] [] b _ T HΣ) as thm.
  forward thm. econstructor. econstructor. rewrite !PCUICLiftSubst.subst_empty in *; auto.
  rewrite !PCUICLiftSubst.subst_empty in *.
  cbn in *. 
  eapply thm; eauto.
Qed.
