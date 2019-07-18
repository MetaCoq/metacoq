(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".

From Equations Require Import Equations.
Require Import Equations.Tactics.
From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaCoq.Template Require Import LibHypsNaming.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSubstitution PCUICClosed PCUICCumulativity PCUICGeneration
     PCUICSubstitution PCUICClosed PCUICCumulativity PCUICGeneration PCUICReduction
     PCUICParallelReduction PCUICEquality
     PCUICValidity PCUICParallelReductionConfluence PCUICConfluence
     PCUICContextConversion
     PCUICConversion PCUICInversion PCUICPrincipality.

Require Import ssreflect ssrbool.
Require Import String.
Set Asymmetric Patterns.
Set SimplIsCbn.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.

(* Commented otherwise extraction would produce an axiom making the whole
   extracted code unusable *)

Arguments Universe.sort_of_product : simpl nomatch.

Lemma mkApps_inj f a f' l :
  tApp f a = mkApps f' l -> l <> [] ->
  f = mkApps f' (removelast l) /\ (a = last l a).
Proof.
  induction l in f' |- *; simpl; intros H. noconf H. intros Hf. congruence.
  intros . destruct l; simpl in *. now noconf H.
  specialize (IHl _ H). forward IHl by congruence.
  apply IHl.
Qed.

Lemma last_app {A} (l l' : list A) d : l' <> [] -> last (l ++ l') d = last l' d.
Proof.
  revert l'. induction l; simpl; auto. intros.
  destruct l. simpl. destruct l'; congruence. simpl.
  specialize (IHl _ H). apply IHl.
Qed.

Lemma mkApps_nonempty f l :
  l <> [] -> mkApps f l = tApp (mkApps f (removelast l)) (last l f).
Proof.
  destruct l using rev_ind. intros; congruence.
  intros. rewrite <- mkApps_nested. simpl. f_equal.
  rewrite removelast_app. congruence. simpl. now rewrite app_nil_r.
  rewrite last_app. congruence.
  reflexivity.
Qed.

Lemma last_nonempty_eq {A} {l : list A} {d d'} : l <> [] -> last l d = last l d'.
Proof.
  induction l; simpl; try congruence.
  intros. destruct l; auto. apply IHl. congruence.
Qed.

Lemma nth_error_removelast {A} (args : list A) n :
  n < Nat.pred #|args| -> nth_error args n = nth_error (removelast args) n.
Proof.
  induction n in args |- *; destruct args; intros; auto.
  simpl. destruct args. depelim H. reflexivity.
  simpl. rewrite IHn. simpl in H. auto with arith.
  destruct args, n; reflexivity.
Qed.

(** Requires Validity *)
Lemma type_mkApps_inv {cf:checker_flags} (Σ : global_env_ext) Γ f u T : wf Σ ->
  Σ ;;; Γ |- mkApps f u : T ->
  { T' & { U & ((Σ ;;; Γ |- f : T') * (typing_spine Σ Γ T' u U) * (Σ ;;; Γ |- U <= T))%type } }.
Proof.
  intros wfΣ; induction u in f, T |- *. simpl. intros.
  { exists T, T. intuition auto. constructor. eapply validity; auto.
    now eapply typing_wf_local. eauto. eapply cumul_refl'. }
  intros Hf. simpl in Hf.
  destruct u. simpl in Hf.
  - eapply inversion_App in Hf as [na' [A' [B' [Hf' [Ha HA''']]]]].
    eexists _, _; intuition eauto.
    econstructor; eauto. eapply validity; eauto with wf.
    constructor.
Admitted.

(*   - specialize (IHu (tApp f a) T). *)
(*     specialize (IHu Hf) as [T' [U' [[H' H''] H''']]]. *)
(*     eapply inversion_App in H' as [na' [A' [B' [Hf' [Ha HA''']]]]]. *)
(*     exists (tProd na' A' B'), U'. intuition; eauto. *)
(*     econstructor. eapply validity; eauto with wf. *)
(*     eapply cumul_refl'. auto. *)
(*     clear -H'' HA'''. depind H''. *)
(*     econstructor; eauto. eapply cumul_trans; eauto. *)
(* Qed. *)

Lemma All_rev {A} (P : A -> Type) (l : list A) : All P l -> All P (List.rev l).
Proof.
  induction l using rev_ind. constructor.
  intros. rewrite rev_app_distr. simpl. apply All_app in X as [Alll Allx]. inv Allx.
  constructor; intuition eauto.
Qed.

Require Import Lia.

Lemma nth_error_rev {A} (l : list A) i : i < #|l| ->
  nth_error l i = nth_error (List.rev l) (#|l| - S i).
Proof.
  revert l. induction i. destruct l; simpl; auto.
  induction l using rev_ind; simpl. auto.
  rewrite rev_app_distr. simpl.
  rewrite app_length. simpl.
  replace (#|l| + 1 - 0) with (S #|l|) by lia. simpl.
  rewrite Nat.sub_0_r in IHl. auto with arith.

  destruct l. simpl; auto. simpl. intros. rewrite IHi. lia.
  assert (#|l| - S i < #|l|) by lia.
  rewrite nth_error_app_lt. rewrite List.rev_length; auto.
  reflexivity.
Qed.

Lemma type_tFix_inv {cf:checker_flags} (Σ : global_env_ext) Γ mfix idx T : wf Σ ->
  Σ ;;; Γ |- tFix mfix idx : T ->
  { T' & { rarg & {f & (unfold_fix mfix idx = Some (rarg, f)) * (Σ ;;; Γ |- f : T') * (Σ ;;; Γ |- T' <= T) }}}%type.
Proof.
  intros wfΣ H. depind H.
  unfold unfold_fix. rewrite e.
  specialize (nth_error_all e a0) as [Hty ->].
  destruct decl as [name ty body rarg]; simpl in *.
  clear e.
  eexists _, _, _. split. split. eauto.
  eapply (substitution _ _ types _ [] _ _ wfΣ); simpl; eauto with wf.
  - subst types. rename i into hguard. clear -a a0 hguard.
    pose proof a0 as a0'. apply All_rev in a0'.
    unfold fix_subst, fix_context. simpl.
    revert a0'. rewrite <- (@List.rev_length _ mfix).
    rewrite rev_mapi. unfold mapi.
    assert (#|mfix| >= #|List.rev mfix|) by (rewrite List.rev_length; lia).
    assert (He :0 = #|mfix| - #|List.rev mfix|) by (rewrite List.rev_length; auto with arith).
    rewrite {3}He. clear He. revert H.
    assert (forall i, i < #|List.rev mfix| -> nth_error (List.rev mfix) i = nth_error mfix (#|List.rev mfix| - S i)).
    { intros. rewrite nth_error_rev. auto.
      now rewrite List.rev_length List.rev_involutive. }
    revert H.
    generalize (List.rev mfix).
    intros l Hi Hlen H.
    induction H. simpl. constructor.
    simpl. constructor. unfold mapi in IHAll.
    simpl in Hlen. replace (S (#|mfix| - S #|l|)) with (#|mfix| - #|l|) by lia.
    apply IHAll. intros. simpl in Hi. specialize (Hi (S i)). apply Hi. lia. lia.
    clear IHAll. destruct p.
    simpl in Hlen. assert ((Nat.pred #|mfix| - (#|mfix| - S #|l|)) = #|l|) by lia.
    rewrite H0. rewrite simpl_subst_k. clear. induction l; simpl; auto with arith.
    eapply type_Fix; auto.
    simpl in Hi. specialize (Hi 0). forward Hi. lia. simpl in Hi.
    rewrite Hi. f_equal. lia.
  - subst types. rewrite simpl_subst_k. now rewrite fix_context_length fix_subst_length.
    auto.
  - destruct (IHtyping mfix idx wfΣ eq_refl) as [T' [rarg [f [[unf fty] Hcumul]]]].
    exists T', rarg, f. intuition auto. eapply cumul_trans; eauto.
    destruct b. eapply cumul_trans; eauto.
Qed.

(** The subject reduction property of the system: *)

Definition SR_red1 {cf:checker_flags} (Σ : global_env_ext) Γ t T :=
  forall u (Hu : red1 Σ Γ t u), Σ ;;; Γ |- u : T.

Hint Resolve conv_ctx_refl : pcuic.

Lemma sr_red1 {cf:checker_flags} : env_prop SR_red1.
Proof.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; unfold SR_red1; intros **; rename_all_hyps;
    match goal with
    | [H : (_ ;;; _ |- _ <= _) |- _ ] => idtac
    | _ =>
      depelim Hu; try solve [apply mkApps_Fix_spec in x; noconf x];
      try solve [econstructor; eauto]
    end.

  - (* Rel *)
    rewrite heq_nth_error in e. destruct decl as [na b ty]; noconf e.
    simpl.
    pose proof (nth_error_All_local_env_over heq_nth_error X); eauto.
    destruct lookup_wf_local_decl; cbn in *.
    rewrite <- (firstn_skipn (S n) Γ).
    assert(S n = #|firstn (S n) Γ|).
    { rewrite firstn_length_le; auto. apply nth_error_Some_length in heq_nth_error. auto with arith. }
    rewrite {3 4}H. apply weakening; auto.
    now unfold app_context; rewrite firstn_skipn.

  - (* Prod *)
    constructor; eauto.
    eapply (context_conversion _ wfΣ _ _ _ _ typeb).
    constructor; auto with pcuic.
    constructor; auto. exists s1; auto.

  - (* Lambda *)
    eapply type_Cumul. eapply type_Lambda; eauto.
    eapply (context_conversion _ wfΣ _ _ _ _ typeb).
    constructor; auto with pcuic.
    constructor; auto. exists s1; auto.
    assert (Σ ;;; Γ |- tLambda n t b : tProd n t bty). econstructor; eauto.
    edestruct (validity _ wfΣ _ wfΓ _ _ X0). apply i.
    eapply cumul_red_r.
    apply cumul_refl'. constructor. apply Hu.

  - (* LetIn body *)
    eapply type_Cumul.
    apply (substitution_let _ Γ n b b_ty b' b'_ty wfΣ typeb').
    specialize (typing_wf_local typeb') as wfd.
    assert (Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty). econstructor; eauto.
    edestruct (validity _ wfΣ _ wfΓ _ _ X0). apply i.
    eapply cumul_red_r.
    apply cumul_refl'. constructor.

  - (* LetIn value *)
    eapply type_Cumul.
    econstructor; eauto.
    eapply (context_conversion _ wfΣ _ _ _ _ typeb').
    constructor. auto with pcuic. constructor; eauto. constructor; auto.
    now exists s1. red. auto.
    assert (Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty). econstructor; eauto.
    edestruct (validity _ wfΣ _ wfΓ _ _ X0). apply i.
    eapply cumul_red_r.
    apply cumul_refl'. now constructor.

  - (* LetIn type annotation *)
    specialize (forall_u _ Hu).
    eapply type_Cumul.
    econstructor; eauto.
    eapply type_Cumul. eauto. right; exists s1; auto.
    apply red_cumul; eauto.
    eapply (context_conversion _ wfΣ _ _ _ _ typeb').
    constructor. auto with pcuic. constructor; eauto. constructor; auto.
    exists s1; auto. red; eauto.
    eapply type_Cumul. eauto. right. exists s1; auto. eapply red_cumul. now eapply red1_red.
    assert (Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty). econstructor; eauto.
    edestruct (validity _ wfΣ _ wfΓ _ _ X0). apply i.
    eapply cumul_red_r.
    apply cumul_refl'. now constructor.

  - (* Application *)
    eapply substitution0; eauto.
    pose proof typet as typet'.
    eapply inversion_Lambda in typet' as [s1 [B' [Ht [Hb HU]]]]=>//.
    apply cumul_Prod_inv in HU as [eqA leqB] => //.
    destruct (validity _ wfΣ _ wfΓ _ _ typet).

    eapply type_Cumul; eauto.
    unshelve eapply (context_conversion _ wfΣ _ _ _ _ Hb); eauto with wf.
    constructor. auto with pcuic. constructor ; eauto.
    constructor; auto with pcuic. red; eauto.
    admit.
    clear -wfΣ i.
    (** Awfully complicated for a well-formedness condition *)
    { destruct i as [[ctx [s [Hs Hs']]]|[s Hs]].
      left.
      simpl in Hs. red.
      generalize (destArity_spec ([] ,, vass na A) B). rewrite Hs.
      intros. simpl in H.
      apply tProd_it_mkProd_or_LetIn in H.
      destruct H as [ctx' [-> Hb]].
      exists ctx', s.
      intuition auto. rewrite app_context_assoc in Hs'. apply Hs'.
      right. exists s.
      eapply inversion_Prod in Hs as [s1 [s2 [Ha [Hp Hp']]]].
      eapply type_Cumul; eauto.
      left. exists [], s. intuition auto. now apply typing_wf_local in Hp.
      apply cumul_Sort_inv in Hp'.
      eapply cumul_trans with (tSort (Universe.sort_of_product s1 s2)). auto.
      constructor.
      cbn. constructor. apply leq_universe_product.
      constructor; constructor ; auto. auto. }

  - (* Fixpoint unfolding *)
    simpl in x.
    assert (args <> []) by (destruct args; simpl in *; congruence).
    symmetry in x. apply mkApps_inj in x as [-> Hu]; auto.
    rewrite mkApps_nonempty; auto.
    epose (last_nonempty_eq H). rewrite <- Hu in e1. rewrite <- e1.
    clear e1.
    specialize (type_mkApps_inv _ _ _ _ _ wfΣ typet) as [T' [U' [[appty spty] Hcumul]]].
    specialize (validity _ wfΣ _ wfΓ _ _ appty) as [_ vT'].
    eapply type_tFix_inv in appty as [T [arg [fn' [[Hnth Hty]]]]]; auto.
    rewrite e in Hnth. noconf Hnth.
    eapply type_App.
    eapply type_Cumul.
    eapply type_mkApps. eapply type_Cumul; eauto. eapply spty.
    eapply validity; eauto.
    eauto. eauto.

  - (* Congruence *)
    eapply type_Cumul; [eapply type_App| |]; eauto with wf.
    eapply validity. eauto. eauto.
    eapply type_App; eauto. eapply red_cumul_inv.
    eapply (red_red Σ Γ [vass na A] [] [u] [N2]); auto.
    constructor. constructor.

  - (* Constant unfolding *)
    eapply declared_constant_inv in wfΣ; eauto with pcuic.
    destruct decl0 as [ty body' univs]; simpl in *; subst body'.
    hnf in wfΣ. simpl in wfΣ. (* Substitutivity of typing w.r.t. universes *) admit.
    eapply weaken_env_prop_typing.

  - (* iota reduction *) admit.
  - (* Case congruence *) admit.
  - (* Case congruence *) admit.
  - (* Case congruence *) admit.
  - (* Case congruence *) admit.
  - (* Proj CoFix congruence *) admit.
  - (* Proj Constructor congruence *) admit.
  - (* Proj reduction *) admit.
  - (* Fix congruence *)
    apply mkApps_Fix_spec in x. simpl in x. subst args.
    simpl. destruct narg; discriminate.
  - (* Fix congruence *)
    admit.
  - (* Fix congruence *)
    admit.
  - (* CoFix congruence *)
    admit.
  - (* CoFix congruence *)
    admit.
  - (* Conversion *)
    specialize (forall_u _ Hu).
    eapply type_Cumul; eauto.
    destruct X2 as [[wf _]|[s Hs]].
    now left.
    now right.
Admitted.

Definition sr_stmt {cf:checker_flags} (Σ : global_env_ext) Γ t T :=
  forall u, red Σ Γ t u -> Σ ;;; Γ |- u : T.

Theorem subject_reduction {cf:checker_flags} : forall (Σ : global_env_ext) Γ t u T,
  wf Σ -> Σ ;;; Γ |- t : T -> red Σ Γ t u -> Σ ;;; Γ |- u : T.
Proof.
  intros * wfΣ Hty Hred.
  induction Hred. auto.
  eapply sr_red1 in IHHred; eauto with wf. now apply IHHred.
Qed.

Lemma subject_reduction1 {cf:checker_flags} {Σ Γ t u T}
  : wf Σ.1 -> Σ ;;; Γ |- t : T -> red1 Σ.1 Γ t u -> Σ ;;; Γ |- u : T.
Proof.
  intros. eapply subject_reduction; try eassumption.
  now apply red1_red.
Defined.
