(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaCoq.Template Require Import config monad_utils utils AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICSubstitution PCUICValidity
     PCUICChecker PCUICInversion.

Import MonadNotation.
Open Scope pcuic.

(* Section Infer_Complete. *)
(*   (* Context `{cf : checker_flags}. *) *)
(*   Existing Instance default_checker_flags. *)
(*   Context `{F : Fuel}. *)

(*   Theorem infer_complete : *)
(*     env_prop (fun Σ Γ t T => exists T', infer Σ Γ t = Checked T' /\ squash (cumul Σ Γ T' T)). *)
(*   Proof. *)
(*     apply typing_ind_env; intros Σ wfΣ Γ wfΓ; intros **; rename_all_hyps; simpl in *; *)
(*       try solve [econstructor; eauto]; *)
(*       unfold infer_type, infer_cumul in *; simpl; unfold infer_type, infer_cumul in *; *)
(*       repeat match goal with *)
(*         H : exists T', _ |- _ => destruct H as [? [-> H]] *)
(*       end; simpl; try (eexists; split; [ reflexivity | solve [ tc ] ]); unsquash; rename_all_hyps. *)

(*   - eexists. rewrite heq_nth_error. *)
(*     split; [ reflexivity | tc ]. *)

(*     - apply cumul_reduce_to_sort in cumulx0 as [s'' [-> Hs'']]. *)
(*       apply cumul_reduce_to_sort in cumulx as [s2' [-> Hs2']]. *)
(*       simpl. eexists. split; [reflexivity|]. *)
(*       constructor. admit. *)

(*     - apply cumul_reduce_to_sort in cumulx0 as [s'' [-> Hs'']]. *)
(*       eexists; intuition eauto. constructor. *)
(*       eapply congr_cumul_prod; tc. *)

(*     - apply cumul_convert_leq in cumulx0 as ->; simpl. *)
(*       apply cumul_reduce_to_sort in cumulx1 as [s'' [-> Hs'']]. *)
(*       simpl. eexists; split; [reflexivity|]. constructor. *)
(*       admit. (*Cumulativity *) *)

(*     - (* Application *) *)
(*       eapply cumul_reduce_to_product in cumulx0 as [dom [codom [-> Hpi]]]. *)
(*       simpl. *)
(*       destruct Hpi as [[Hdom Hcodom]]. *)
(*       assert (Σ;;; Γ |- x <= dom). *)
(*       destruct Hdom. eapply cumul_trans; eauto. *)
(*       apply cumul_convert_leq in X0 as ->. simpl. *)
(*       eexists; split; [reflexivity|]. *)
(*       constructor. apply (substitution_cumul Σ Γ (vass na A :: []) [] [u] codom B); eauto. *)
(*       { simpl. eapply validity in typet. destruct typet. *)
(*         destruct i as [[ctx [s [Ha Hb]]]|]. *)
(*         generalize (PCUICClosed.destArity_spec [] (tProd na A B)). *)
(*         rewrite Ha. simpl. destruct ctx using rev_ind; intros H; try discriminate. *)
(*         rewrite it_mkProd_or_LetIn_app in H. *)
(*         destruct x1 as [na' [b|] ty]; try discriminate. *)
(*         injection H. intros -> -> ->. *)
(*         rewrite app_context_assoc in Hb. *)
(*         eapply All_local_env_app in Hb. intuition auto. *)
(*         destruct i. constructor; eauto with wf. simpl. *)
(*         now eapply inversion_Prod in t0 as [? [? [? ?]]]. auto. auto. } *)
(*       constructor. constructor. rewrite subst_empty. apply typeu. *)

(*     - (* Constant *) *)
(*       erewrite lookup_constant_type_declared; eauto. *)
(*       eexists ; split; [ try reflexivity | tc ]. *)
(*       simpl. unfold consistent_universe_context_instance in H0. *)
(*       destruct cst_universes. *)
(*       -- simpl. reflexivity. *)
(*       -- simpl in *. destruct cst0. simpl in *. *)
(*          unfold check_consistent_instance. *)
(*          admit. *)
(*       -- simpl in *. destruct ctx as [[inst csts] variance]. simpl in *. *)
(*          unfold check_consistent_instance. *)
(*          admit. *)

(*     - (* Inductive *) *)
(*       admit. *)
(*     - (* Constructor *) admit. *)

(*     - (* Case *) *)
(*       (* destruct indpar. *) *)
(*       apply cumul_reduce_to_ind in cumulx as [args' [-> Hcumul]]. *)
(*       simpl in *. rewrite (proj2 (eq_ind_refl Σ ind ind) eq_refl). *)
(*       eexists ; split; [ reflexivity | tc ]. *)
(*       constructor. *)
(*       (* Conversion of applications congruence *) *)
(*       admit. *)

(*     - (* Proj *) admit. *)

(*     - (* Fix *) eexists. rewrite heq_nth_error. *)
(*       split; [ reflexivity | tc ]. *)

(*     - (* CoFix *) eexists. rewrite heq_nth_error. *)
(*       split; [ reflexivity | tc ]. *)

(*     - (* Conversion *) eexists. *)
(*       split; [ reflexivity | tc ]. constructor. *)
(*       eapply cumul_trans; eauto. *)
(*   Admitted. *)

(* End Infer_Complete. *)
(* (* *)
(* Extract Constant infer_type_correct => "(fun f sigma ctx t x -> assert false)". *)
(* Extract Constant infer_correct => "(fun f sigma ctx t ty -> assert false)". *)
(* *) *)