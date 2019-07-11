(* Distributed under the terms of the MIT license.   *)

 From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.RelationClasses Omega.
From MetaCoq.Template
Require Import config Universes monad_utils utils BasicAst AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICPosition
     PCUICNormal PCUICInversion PCUICCumulativity PCUICSafeLemmata PCUICGeneration PCUICValidity PCUICSR.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

 Import MonadNotation.
Open Scope type_scope.

 (* We assume normalisation of the reduction.
    We state is as well-foundedness of the reduction.
*)

 Section Normalisation.

   Context {cf : checker_flags}.
   Context (Σ : global_env_ext).

   Axiom normalisation :
    forall Γ t,
      welltyped Σ Γ t ->
      Acc (cored (fst Σ) Γ) t.

   Lemma Acc_cored_Prod Γ n t1 t2 :
     Acc (cored Σ Γ) t1 ->
     Acc (cored Σ (Γ,, vass n t1)) t2 ->
     Acc (cored Σ Γ) (tProd n t1 t2).
   Proof.
   Admitted.

   Lemma Acc_cored_LetIn Γ n t1 t2 t3 :
     Acc (cored Σ Γ) t1 ->
     Acc (cored Σ Γ) t2 -> Acc (cored Σ (Γ,, vdef n t1 t2)) t3 ->
     Acc (cored Σ Γ) (tLetIn n t1 t2 t3).
   Proof.
   Admitted.

   Lemma neq_mkApps u l : forall t, t <> tSort u -> mkApps t l <> tSort u.
   Proof.
     induction l; cbn; intros t e e'; try easy.
     eapply IHl. 2: eassumption. intros e''; discriminate e''.
   Qed.

   Corollary normalisation' :
     forall Γ t, wf Σ -> wellformed Σ Γ t -> Acc (cored (fst Σ) Γ) t.
   Proof.
     intros Γ t HΣ Ht. destruct Ht as [HH|[HH]].
     - now apply normalisation.
     - revert Γ HH; induction t;
         intros Γ [ctx [s [H1 H2]]]; cbn in *; try discriminate H1.
       + constructor. intros y Hy. cut False. intros [].
         dependent induction Hy.
         * inversion X. eapply neq_mkApps.
           2: eassumption. intro HH; discriminate HH.
         * easy.
       + eapply Acc_cored_Prod.
         * apply normalisation.
           apply destArity_app_Some in H1. destruct H1 as [ctx' [e1 e2]]; subst.
           rewrite app_context_assoc in H2. cbn in H2.
           apply wf_local_app in H2.
           destruct (wf_local_inv H2 _ _ eq_refl) as [_ [u [Ht1 _]]].
           econstructor; exact Ht1.
         * apply destArity_app_Some in H1. destruct H1 as [ctx' [e1 e2]]; subst.
           apply IHt2. exists ctx', s. split. assumption.
           now rewrite app_context_assoc in H2.
       + apply Acc_cored_LetIn.
         * apply normalisation.
           apply destArity_app_Some in H1. destruct H1 as [ctx' [e1 e2]]; subst.
           rewrite app_context_assoc in H2. cbn in H2.
           apply wf_local_app in H2.
           destruct (wf_local_inv H2 _ _ eq_refl) as [_ [_ [Ht1 _]]].
           econstructor; exact Ht1.
         * apply destArity_app_Some in H1. destruct H1 as [ctx' [e1 e2]]; subst.
           rewrite app_context_assoc in H2. cbn in H2.
           apply wf_local_app in H2.
           destruct (wf_local_inv H2 _ _ eq_refl) as [? [u [Ht1 _]]].
           apply validity_term in Ht1; cbn in Ht1; try assumption.
           destruct Ht1. now apply IHt2.
           apply normalisation. destruct i as [uu HH].
           econstructor; exact HH.
         * change (destArity ([vdef na t1 t2] ,,, []) t3 = Some (ctx, s)) in H1.
           apply destArity_app_Some in H1. destruct H1 as [ctx' [e1 e2]]; subst.
           apply IHt3. exists ctx', s. split. assumption.
           now rewrite app_context_assoc in H2.
   Qed.

   Lemma isWfArity_red1 :
     forall {Γ A B},
       red1 (fst Σ) Γ A B ->
       isWfArity typing Σ Γ A ->
       isWfArity typing Σ Γ B.
   Admitted.

   Lemma isWfArity_red :
     forall {Γ A B},
       red (fst Σ) Γ A B ->
       isWfArity typing Σ Γ A ->
       isWfArity typing Σ Γ B.
   Proof.
     induction 1.
     - easy.
     - intro. now eapply isWfArity_red1.
   Qed.

 End Normalisation.