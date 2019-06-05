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
Proof.
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

Lemma bool_equiv b1 b2 T1 T2 : 
(b1 = true <~> T1) -> (b2 = true <~> T2) -> T1 <~> T2 -> b1 = b2.
Proof.
Admitted.
  

Lemma is_type_subst Σ Γ Γ' Δ a T s :
  wf Σ -> subslet Σ Γ s Γ' ->
  Σ ;;; Γ ,,, Γ' ,,, Δ |- a : T ->
  wf_local Σ (Γ ,,, subst_context s 0 Δ) ->
  is_type_or_proof Σ (Γ ,,, Γ' ,,, Δ) a ->
  is_type_or_proof Σ (Γ ,,, subst_context s 0 Δ) (PCUICLiftSubst.subst s #|Δ| a).
Proof.
  intros.
  eapply is_type_or_proof_spec in H; eauto.
  eapply is_type_or_proof_spec.
  eapply substitution; eauto.
  destruct H as [ | (u & ? & ?) ].
  - left. generalize (#|Δ|). intros n.
    induction T in n, i |- *; (try now inv i); cbn in *; eauto.
  - right. exists u. split; eauto.
    pose proof (substitution Σ Γ Γ' s Δ).
    eapply X3 in t; eauto.
Qed.


Lemma extract_subst Σ Γ Γ' Δ a s T :
  wf Σ ->
  subslet Σ Γ s Γ' ->
  wf_local Σ (Γ ,,, subst_context s 0 Δ) ->
  Σ ;;; Γ ,,, Γ'  ,,, Δ |- a : T ->
  is_type_or_proof Σ (Γ ,,, Γ' ,,, Δ) a =
  is_type_or_proof Σ (Γ ,,, subst_context s 0 Δ) (PCUICLiftSubst.subst s #|Δ| a) ->
  extract Σ (Γ ,,, subst_context s 0 Δ) (PCUICLiftSubst.subst s #|Δ| a) = subst  (map (extract Σ Γ) s) #|Δ| (extract Σ (Γ,,,Γ',,,Δ) a).
Proof.
  intros HΣ HΔ Hs Ha He.
  pose proof (typing_wf_local Ha).
  generalize_eqs Ha. intros eqw. rewrite <- eqw in X.
  revert Γ Γ' Δ s Hs HΔ He eqw.
  revert Σ HΣ Γ0 X a T Ha.
  eapply (typing_ind_env (fun Σ Γ0 a T =>
                            forall (Γ Γ' : PCUICAst.context) Δ (s : list PCUICAst.term),
                              wf_local Σ (Γ ,,, subst_context s 0 Δ) ->
                              subslet Σ Γ s Γ' ->
                              _ ->
                                Γ0 = Γ ,,, Γ' ,,, Δ ->
                                extract Σ (Γ ,,, subst_context s 0 Δ) (PCUICLiftSubst.subst s #|Δ| a) =
                                subst (map (extract Σ Γ) s) #|Δ| (extract Σ (Γ ,,, Γ' ,,, Δ) a)
));
  intros Σ wfΣ Γ0 wfΓ0; intros; simpl in * |-; subst Γ0.
  - cbn. destruct (_ <=? _) eqn:E1.
    * destruct (nth_error s (n- #|_|)) eqn:E2.
      -- destruct ?. 
         ++ cbn. now rewrite is_type_extract.
         ++ cbn. rewrite E1.
            rewrite nth_error_map. rewrite E2. cbn.
            erewrite <- subst_context_length.
            erewrite extract_weakening; eauto. admit.
      -- cbn. destruct ?.
         destruct ?. reflexivity. 
         destruct ?.
         ++ reflexivity.
         ++ cbn. rewrite E1. rewrite nth_error_map, E2. cbn.
            now rewrite map_length.
    * cbn. rewrite H0.
      destruct ?. reflexivity.
      cbn. rewrite E1. reflexivity.
  - cbn. rewrite <- H.
    destruct ?; reflexivity.
  - cbn. rewrite <- H1.
    destruct ?; reflexivity.
  - cbn. rewrite <- H1.
    destruct ?.
    + reflexivity.
    + cbn. f_equal.
      specialize (H0 Γ Γ' (PCUICAst.vass n t :: Δ) s).
      cbn [app length] in H0.
      rewrite <- H0; eauto.
      f_equal. f_equal.
      now rewrite subst_context_snoc0.
      admit. (* some wf_local stuff *)
      rewrite subst_context_snoc0.
      Lemma is_type_or_proof_lambda  Σ Γ na t b :
        Extract.is_type_or_proof Σ Γ (PCUICAst.tLambda na t b) =
        Extract.is_type_or_proof Σ (Γ ,, PCUICAst.vass na t) b.
      Admitted.
      rewrite is_type_or_proof_lambda in *.
      now rewrite E, <- H1.
  - cbn. rewrite <- H2.
    destruct ?.
    + reflexivity.
    + cbn. f_equal.
      * eapply H0; eauto.
        admit.
      * specialize (H1 Γ Γ' (PCUICAst.vdef n b b_ty :: Δ) s).
        unfold app_context in *.
        cbn [List.length List.app] in H1. rewrite <- H1; eauto.
        f_equal. rewrite subst_context_snoc0. reflexivity.
        admit. (* wf_local stuff *)
        
        Lemma is_type_or_proof_letin Σ Γ na t b0 b1 :
          is_type_or_proof Σ Γ (PCUICAst.tLetIn na b0 t b1) =
          Extract.is_type_or_proof Σ (Γ ,, PCUICAst.vdef na b0 t) b1.
        Admitted.
        rewrite is_type_or_proof_letin in *.
        rewrite E, H2.
        f_equal. now rewrite !subst_context_snoc0.
  - cbn. rewrite <- H1.
    destruct ?; cbn; try reflexivity.

    Lemma is_type_App_false  Σ Γ a l T :
      Σ ;;; Γ |- PCUICAst.mkApps a l : T -> 
                                      is_type_or_proof Σ Γ (PCUICAst.mkApps a l) = false ->
                                      is_type_or_proof Σ Γ a = false.
    Proof.
    Admitted.

    f_equal.
    + eapply is_type_App_false with (l := [_]) in E. symmetry in H1.
      eapply is_type_App_false with (l := [_]) in H1.
      eapply H; eauto.
      econstructor; eauto.
      eapply substitution_alt in X0; eauto.
      eapply substitution_alt in X1; eauto.
      econstructor; eauto.
    + eapply H0; eauto.      
      Lemma is_type_App_false  Σ Γ a l T :
        Σ ;;; Γ |- PCUICAst.mkApps a l : T -> 
                                        is_type_or_proof Σ Γ (PCUICAst.mkApps a l) = false ->
                                        is_type_or_proof Σ Γ a = false.
      Proof.
      Admitted.
      eapply is_type_App_false with (l := [_]) in E. symmetry in H1.
      eapply is_type_App_false with (l := [_]) in H1.
      now rewrite H1, E.
      econstructor; eauto.
      eapply substitution_alt in X0; eauto.
      eapply substitution_alt in X1; eauto.
      econstructor; eauto.
    + eapply H0; eauto.
      
      
Admitted.

Lemma extract_subst_alt Σ Γ Γ' Δ a s T :
  wf Σ ->
  subslet Σ Γ s Γ' ->
  Σ ;;; Γ ,,, Γ'  ,,, Δ |- a : T ->
  is_type_or_proof Σ (Γ ,,, Γ' ,,, Δ) a =
  is_type_or_proof Σ (Γ ,,, subst_context s 0 Δ) (PCUICLiftSubst.subst s #|Δ| a) ->
  extract Σ (Γ ,,, subst_context s 0 Δ) (PCUICLiftSubst.subst s #|Δ| a) = subst  (map (extract Σ Γ) s) #|Δ| (extract Σ (Γ,,,Γ',,,Δ) a).
Proof.
  intros. 
  eapply extract_subst; eauto. clear H. (* clear H0 H1 a' H s'. *)
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
  is_type_or_proof Σ [] (PCUICLiftSubst.subst1 a' 0 b) = is_type_or_proof Σ  [PCUICAst.vass na t] b ->
  extract Σ [] (PCUICLiftSubst.subst1 a' 0 b) = (extract Σ [PCUICAst.vass na t] b) {0 := extract Σ [] a'}.
Proof.
  intros HΣ Ht Hu He.
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
is_type_or_proof Σ [] (PCUICLiftSubst.subst1 a' 0 b) = is_type_or_proof Σ  [PCUICAst.vdef na a' t] b ->
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
