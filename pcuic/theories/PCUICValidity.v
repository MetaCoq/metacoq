From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICTyping
     PCUICWeakeningEnv PCUICWeakening PCUICSubstitution PCUICReduction PCUICCumulativity PCUICGeneration.
From Equations Require Import Equations.
Require Import ssreflect.
Existing Instance config.default_checker_flags.

Derive NoConfusion for term.
Derive Signature for typing cumul.

Lemma isWfArity_or_Type_lift Σ n Γ ty (isdecl : n <= #|Γ|):
  wf Σ -> wf_local Σ Γ ->
  isWfArity_or_Type Σ (skipn n Γ) ty ->
  isWfArity_or_Type Σ Γ (lift0 n ty).
Proof.
  intros wfΣ wfΓ wfty. rewrite <- (firstn_skipn n Γ) in wfΓ |- *.
  assert (n = #|firstn n Γ|).
  { rewrite firstn_length_le; auto with arith. }
  destruct wfty.
  - red. left. destruct i as [ctx [u [da Hd]]].
    exists (lift_context n 0 ctx), u. split.
    now rewrite (lift_destArity [] ty n 0) da.
    eapply All_local_env_app_inv.
    eapply All_local_env_app in Hd. intuition eauto.
    rewrite {3}H.
    clear -wfΣ wfΓ isdecl a b.
    induction b; rewrite ?lift_context_snoc; econstructor; simpl; auto.
    destruct t0 as [u Hu]. exists u. rewrite Nat.add_0_r.
    unshelve eapply (weakening_typing Σ (skipn n Γ) Γ0 (firstn n Γ) t _ _ _ (tSort u)); eauto with wf.
    apply All_local_env_app_inv. intuition eauto.
    rewrite Nat.add_0_r.
    unshelve eapply (weakening_typing Σ (skipn n Γ) Γ0 (firstn n Γ) b _ _ _ t); eauto with wf.
    eapply All_local_env_app_inv. intuition eauto.
  - right. destruct i as [u Hu]. exists u.
    rewrite {3}H.
    unshelve eapply (weakening_typing Σ (skipn n Γ) [] (firstn n Γ) ty _ _ _ (tSort u)); eauto with wf.
Qed.

Lemma destArity_it_mkProd_or_LetIn ctx ctx' t :
  destArity ctx (it_mkProd_or_LetIn ctx' t) =
  destArity (ctx ,,, ctx') t.
Proof.
  induction ctx' in ctx, t |- *; simpl; auto.
  rewrite IHctx'. destruct a as [na [b|] ty]; reflexivity.
Qed.

Lemma type_Prod_invert Σ Γ na A B U :
  Σ ;;; Γ |- tProd na A B : U ->
  { s1 & { s2 &
           (Σ ;;; Γ |- A : tSort s1) *
           (Σ ;;; Γ ,, vass na A |- B : tSort s2) *
           (Σ ;;; Γ |- tSort (Universe.sort_of_product s1 s2) <= U) } }%type.
Proof.
  intros H; depind H.
  exists s1, s2; intuition auto.
  destruct IHtyping as [s1 [s2 Hs]].
  eexists _, _; intuition eauto.
  eapply cumul_trans; eauto.
  eapply cumul_trans; eauto.
Qed.

Lemma isWfArity_Sort Σ Γ s : wf_local Σ Γ -> isWfArity typing Σ Γ (tSort s).
Proof.
  intros. exists [], s; intuition auto.
Qed.
Hint Extern 10 (isWfArity _ _ _ (tSort _)) => apply isWfArity_Sort : pcuic.

Hint Extern 30 (wf_local ?Σ ?Γ) =>
  match goal with
    | [ H : typing Σ Γ _ _ |- _ ] => apply (typing_wf_local H)
  end : pcuic.

Ltac pcuic := try solve [ intuition typeclasses eauto with pcuic ].

Definition weaken_env_prop_full
           (P : global_context -> context -> term -> term -> Type) :=
  forall Σ Σ', wf Σ' -> extends Σ Σ' -> forall Γ t T, P Σ Γ t T -> P Σ' Γ t T.

Lemma isWfArity_or_Type_weaken_full : weaken_env_prop_full (fun Σ Γ t T => isWfArity_or_Type Σ Γ T).
Proof.
  red. intros.
  destruct X1. left. destruct i as [ctx [s [Heq Hs]]].
  exists ctx, s. pcuic. right. destruct i as [u Hu]; exists u; pcuic.
  unshelve eapply (weaken_env_prop_typing _ _ _ X0 _ _ (Some (tSort u))); eauto.
Qed.
Hint Resolve isWfArity_or_Type_weaken_full : pcuic.

Lemma isWfArity_or_Type_weaken :
 weaken_env_prop
   (lift_typing (fun Σ Γ (_ T : term) => isWfArity_or_Type Σ Γ T)).
Proof.
  red. intros. unfold lift_typing in *. destruct T. now eapply isWfArity_or_Type_weaken_full.
  destruct X1 as [s Hs]; exists s. now eapply isWfArity_or_Type_weaken_full.
Qed.
Hint Resolve isWfArity_or_Type_weaken : pcuic.

(** TODO: Universe instances *)
Lemma isWfArity_or_Type_subst_instance:
  forall (Σ : global_context) (Γ : context) (u : list Level.t) (ty : term), wf_local Σ Γ ->
    isWfArity_or_Type Σ [] ty -> isWfArity_or_Type Σ Γ (PCUICUnivSubst.subst_instance_constr u ty).
Proof.
  intros Σ Γ u ty wfΓ H.
  destruct H as [[ctx [s [Heq Hs]]]|].
  - left.
    exists ctx, s. split; pcuic.
Admitted.

Lemma invert_type_App Σ Γ f u T :
  Σ ;;; Γ |- tApp f u : T ->
  { A & { B & { na & ((Σ ;;; Γ |- f : tProd na A B) * (Σ ;;; Γ |- u : A) * (Σ ;;; Γ |- B {0:=u} <= T))%type } } }.
Proof.
  intros Hty.
  dependent induction Hty. exists A, B, na. intuition auto.
  specialize (IHHty _ _ eq_refl) as [T' [U' [na' [H' H'']]]].
  exists T', U', na'. split; auto.
  eapply cumul_trans; eauto.
Qed.

Lemma invert_type_mkApps Σ Γ f fty u T :
  Σ ;;; Γ |- mkApps f u : T ->
  (* Looks mutual with validity! *)
  Σ ;;; Γ |- f : fty -> isWfArity_or_Type Σ Γ fty ->
  { T' & { U & ((Σ ;;; Γ |- f : T') * (typing_spine Σ Γ T' u U) * (Σ ;;; Γ |- U <= T))%type } }.
Proof.
  induction u in f, fty, T |- *. simpl. intros. exists T, T. intuition auto. constructor.
  intros Hf Hty. simpl in Hty.
  specialize (IHu _ fty _ Hf) as [T' [U' [[H' H''] H''']]].
  simpl in Hf.
  econstructor.

Admitted.
(*   eapply invert_type_App in H' as (fA & fB & fna & Hf). intuition. *)
(*   exists (tProd fna fA fB), U'. intuition auto. *)
(*   econstructor. *)
(*   exists T', U'. split; auto. split; auto. *)
(*   eapply cumul_trans; eauto. *)
(* Qed. *)

Theorem validity :
  env_prop (fun Σ Γ t T => isWfArity_or_Type Σ Γ T).
Proof.

  apply typing_ind_env; intros; rename_all_hyps.

  - destruct (nth_error_All_local_env_over heq_nth_error X) as [HΓ' Hd].
    destruct decl as [na [b|] ty]; cbn -[skipn] in *.
    + eapply isWfArity_or_Type_lift; eauto. clear HΓ'; now apply nth_error_Some_length in heq_nth_error.
    + destruct lookup_wf_local_decl; cbn -[skipn] in *.
      destruct o. right. exists x0. simpl in Hd.
      rewrite <- (firstn_skipn (S n) Γ).
      assert (S n = #|firstn (S n) Γ|).
      { apply nth_error_Some_length in heq_nth_error. rewrite firstn_length_le; auto with arith. }
      rewrite {3}H.
      apply (weakening Σ (skipn (S n) Γ) (firstn (S n) Γ) ty (tSort x0)); eauto with wf.
      unfold app_context. now rewrite (firstn_skipn (S n) Γ).

  - (* Universe *) left. exists [], (Universe.super l). split; auto.
  - (* Product *) left. eexists [], _. split; eauto. simpl. reflexivity.
  - (* Lambda *)
    destruct X3.
    + left. destruct i as [ctx [s [Heq Hs]]].
      red. simpl. pose proof (PCUICClosed.destArity_spec [] bty).
      rewrite Heq in H. simpl in H. subst bty. clear Heq.
      eexists _, s. split; auto.
      rewrite destArity_it_mkProd_or_LetIn. simpl. reflexivity.
      apply All_local_env_app_inv; split; auto.
      apply All_local_env_app_inv; split; auto. repeat constructor.
      simpl. now exists s1.
      apply All_local_env_app in Hs. unfold snoc.
      intuition auto. clear -b0.
      induction b0; constructor; eauto.
      destruct t1 as [u Hu]. exists u.
      rewrite app_context_assoc. apply Hu.
      simpl in t1 |- *.
      rewrite app_context_assoc. apply t1.
    + destruct i as [u Hu].
      right. exists (Universe.sort_of_product s1 u); constructor; auto.

  - (* Let *)
    destruct X5.
    + left. destruct i as [ctx [s [Heq Hs]]].
      eexists _, s.
      simpl. split; auto.
      pose proof (PCUICClosed.destArity_spec [] b'_ty).
      rewrite Heq in H. simpl in H. subst b'_ty.
      rewrite destArity_it_mkProd_or_LetIn. simpl.
      reflexivity. rewrite app_context_assoc. simpl.
      apply All_local_env_app_inv; split; eauto with wf.
      apply All_local_env_app in Hs as [Hp Hs].
      apply Hs.
    + right.
      destruct i as [u Hu]. exists u.
      econstructor.
      eapply type_LetIn; eauto. left. exists [], u; intuition eauto with wf.
      eapply cumul_alt. exists (tSort u), (tSort u); intuition auto.
      apply red1_red; repeat constructor.

  - (* Application *)
    destruct X1 as [[ctx [s [Heq Hs]]]|].
    simpl in Heq. pose proof (PCUICClosed.destArity_spec ([],, vass na A) B).
    rewrite Heq in H.
    simpl in H. unfold mkProd_or_LetIn in H. simpl in H.
    destruct ctx using rev_ind; noconf H.
    simpl in H. rewrite it_mkProd_or_LetIn_app in H. simpl in H.
    destruct x as [na' [b|] ty]; noconf H.
    left. eexists _, s. split.
    unfold subst1. rewrite subst_it_mkProd_or_LetIn.
    rewrite destArity_it_mkProd_or_LetIn. simpl. reflexivity.
    rewrite app_context_nil_l. apply All_local_env_app_inv; intuition auto.
    apply All_local_env_app in Hs as [wf'Γ wfctx].
    apply All_local_env_app in wfctx as [wfd wfctx].
    eapply All_local_env_subst; eauto. simpl; intros.
    destruct T; simpl in *.
    + rewrite Nat.add_0_r. eapply substitution_alt; eauto. constructor. constructor.
      2: simpl; eauto; now rewrite app_context_assoc in X0.
      now rewrite subst_empty.
    + rewrite Nat.add_0_r. destruct X0 as [u' Hu']. exists u'.
      eapply (substitution_alt _ _ _ _ _ _ (tSort u')); eauto. constructor. constructor.
      2: simpl; eauto; now rewrite app_context_assoc in Hu'.
      now rewrite subst_empty.
    + right.
      destruct i as [u' Hu']. exists u'.
      eapply (substitution0 _ _ na _ _ _ (tSort u')); eauto.
      apply type_Prod_invert in Hu' as [s1 [s2 Hs]]. intuition.
      eapply type_Conv; pcuic.
      eapply (weakening_cumul Σ Γ [] [vass na A]) in b; pcuic.
      simpl in b. eapply cumul_trans. 2:eauto.
      constructor. constructor. simpl. apply leq_universe_product_r.

  - eapply declared_constant_inv in H; pcuic.
    destruct decl as [ty [b|] univs]. red in H. simpl in *.
    apply isWfArity_or_Type_subst_instance; pcuic.
    repeat red in H; simpl in *.
    apply isWfArity_or_Type_subst_instance; pcuic.
    destruct H.
    (* TODO: Fix Forall_decls_typing same way as local environments *)
    admit.
  - admit.
  - admit.

  - (* Case *)
    right. red.
    destruct X2.
    + destruct i as [ctx [s [Heq Hs]]].
      exists s.
      unfold check_correct_arity in *.
      assert (ctx = pctx). admit. (* WF of cases *)
      subst ctx.
      pose proof (PCUICClosed.destArity_spec [] pty). rewrite Heq in H.
      simpl in H. subst pty.
      assert (#|args| = #|pctx|). admit. (* WF of case *)
      eapply type_mkApps. eauto.
      destruct X4. destruct i as [ctx' [s' [Heq' Hs']]].
      elimtype False.
      { clear -Heq'.
        revert Heq'.
        assert (destArity [] (tInd ind u) = None) by reflexivity.
        revert H.
        generalize (tInd ind u). clear. induction args.
        intros. simpl in Heq'. congruence.
        intros. unshelve eapply (IHargs _ _ Heq').
        reflexivity. }
      destruct i as [si Hi].
      eapply (invert_type_mkApps _ _ (tInd ind u)) in Hi; pcuic.
      2:{ econstructor; eauto. admit. (* universes *) }
      2:{ admit. }
      (* Looks ok *)
      admit.

    + destruct i as [ui Hi]. exists ui.
      admit. (* Same idea *)

  - (* Proj *)
    right.
    admit.

  - admit. (* Fix *)
  - admit. (* CoFix *)

  - (* Conv *)
    destruct X2. red in i. left. exact (projT1 i).
    right. destruct s as [u [Hu _]]. now exists u.
Admitted.

