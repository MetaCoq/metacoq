(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".

From Equations Require Import Equations.
Require Import Equations.Tactics.
From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaCoq Require Import LibHypsNaming.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSubstitution PCUICClosed PCUICCumulativity PCUICGeneration PCUICReduction
     PCUICParallelReduction PCUICEquality PCUICAlpha
     PCUICValidity PCUICParallelReductionConfluence PCUICConfluence
     PCUICContextConversion PCUICUnivSubstitution
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
    unshelve epose proof (declared_constant_inj decl decl0 _ _); tea; subst decl.
    destruct decl0 as [ty body' univs]; simpl in *; subst body'.
    eapply on_declared_constant in H; tas; cbn in H.
    rewrite <- (app_context_nil_l Γ).
    apply typecheck_closed in H as H'; tas; [|constructor].
    destruct H' as [_ H']. apply andb_and in H'.
    replace (subst_instance_constr u body)
      with (lift0 #|Γ| (subst_instance_constr u body)).
    replace (subst_instance_constr u ty)
      with (lift0 #|Γ| (subst_instance_constr u ty)).
    2-3: rewrite lift_subst_instance_constr lift_closed; cbnr; apply H'.
    eapply weakening; tea.
    now rewrite app_context_nil_l.
    eapply typing_subst_instance_decl with (Γ0:=[]); tea.

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

Section SRContext.
  Context {cf:checker_flags}.

  (* todo: rename wf_local_app *)
  Definition wf_local_app' {Σ Γ1 Γ2} :
    wf_local Σ Γ1 -> wf_local_rel Σ Γ1 Γ2
    -> wf_local Σ (Γ1 ,,, Γ2).
  Proof.
    intros H1 H2. apply wf_local_local_rel.
    apply wf_local_rel_local in H1.
    apply wf_local_rel_app_inv; tas.
    now rewrite app_context_nil_l.
  Qed.

  Definition cumul_red_l' `{checker_flags} :
    forall Σ Γ t u,
      wf Σ.1 ->
      red (fst Σ) Γ t u ->
      Σ ;;; Γ |- t <= u.
  Proof.
    intros Σ Γ t u hΣ h.
    induction h.
    - eapply cumul_refl'.
    - eapply PCUICConversion.cumul_trans ; try eassumption.
      eapply cumul_red_l.
      + eassumption.
      + eapply cumul_refl'.
  Defined.

  Hint Constructors OnOne2_local_env : aa.
  Hint Unfold red1_ctx : aa.


  Lemma red1_ctx_app Σ Γ Γ' Δ :
    red1_ctx Σ Γ Γ' ->
    red1_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ).
  Proof.
    induction Δ. trivial.
    intro H. simpl. constructor. now apply IHΔ.
  Qed.

  Lemma red1_red_ctx Σ Γ Γ' :
    red1_ctx Σ Γ Γ' ->
    red_ctx Σ Γ Γ'.
  Proof.
    induction 1; cbn in *.
    - constructor. reflexivity. cbn; eauto using red1_red.
    - constructor. reflexivity.
      destruct p as [[? []]|[? []]]; cbn; eauto using red1_red.
    - destruct d as [na [bo|] ty]; constructor; eauto.
      split; eapply refl_red.
      apply refl_red.
  Qed.

  Lemma nth_error_red1_ctx Σ Γ Γ' n decl :
    wf Σ ->
    nth_error Γ n = Some decl ->
    red1_ctx Σ Γ Γ' ->
    ∑ decl', nth_error Γ' n = Some decl'
              × red Σ Γ' (lift0 (S n) (decl_type decl))
              (lift0 (S n) (decl_type decl')).
  Proof.
    intros wfΣ h1 h2; induction h2 in n, h1 |- *.
    - destruct n.
      + inversion h1; subst. exists (vass na t').
        split; cbnr.
        eapply (weakening_red_0 wfΣ _ [_]); tas; cbnr.
        apply red1_red; tas.
      + exists decl. split; tas. apply refl_red.
    - destruct n.
      + inversion h1; subst.
        destruct p as [[? []]|[? []]].
        -- exists (vdef na b' t).
           split; cbnr.
           eapply (weakening_red_0 wfΣ _ [_]); tas; cbnr.
           apply refl_red.
        -- exists (vdef na b t').
           split; cbnr.
           eapply (weakening_red_0 wfΣ _ [_]); tas; cbnr.
           apply red1_red; tas.
      + exists decl. split; tas. apply refl_red.
    - destruct n.
      + exists d. split; cbnr. inv h1; apply refl_red.
      + cbn in h1. specialize (IHh2 _ h1).
        destruct IHh2 as [decl' [X1 X2]].
        exists decl'. split; tas.
        rewrite !(simpl_lift0 _ (S n)).
        eapply (weakening_red_0 wfΣ _ [_]); tas; cbnr.
  Qed.


  Lemma wf_local_isType_nth Σ Γ n decl :
    wf Σ.1 ->
    wf_local Σ Γ ->
    nth_error Γ n = Some decl ->
    ∑ s, Σ ;;; Γ |- lift0 (S n) (decl_type decl) : tSort s.
  Proof.
    induction n in Γ, decl |- *; intros hΣ hΓ e; destruct Γ;
      cbn; inversion e; inversion hΓ; subst.
    all: try (destruct X0 as [s Ht]; exists s;
              eapply (weakening _ _ [_] _ (tSort s)); tas).
    - eapply IHn in H0; tas. destruct H0 as [s Ht]. exists s.
      rewrite simpl_lift0.
      eapply (weakening _ _ [_] _ (tSort s)); tas; cbnr.
    - eapply IHn in H0; tas. destruct H0 as [s Ht]. exists s.
      rewrite simpl_lift0.
      eapply (weakening _ _ [_] _ (tSort s)); tas; cbnr.
  Qed.

  Ltac invs H := inversion H; subst.
  Ltac invc H := inversion H; subst; clear H.

  Lemma subject_reduction_ctx :
    env_prop (fun Σ Γ t A => forall Γ', red1_ctx Σ Γ Γ' -> Σ ;;; Γ' |- t : A).
  Proof.
    assert (X: forall Σ Γ wfΓ, All_local_env_over typing
                          (fun Σ Γ (_ : wf_local Σ Γ)  t T (_ : Σ;;; Γ |- t : T) =>
                             forall Γ', red1_ctx Σ Γ Γ' -> Σ;;; Γ' |- t : T) Σ Γ wfΓ
                          -> wf Σ -> forall Γ', red1_ctx Σ Γ Γ' -> wf_local Σ Γ'). {
      induction 1.
      - intros hΣ Γ' r. inv r.
      - intros hΣ Γ' r. inv r.
        + constructor; tas.
          destruct tu as [s Ht]. exists s. eapply subject_reduction1; tea.
        + constructor; tas. eapply IHX; tas.
          eexists. now eapply p.
      - intros hΣ Γ' r. inv r.
        + destruct X0 as [[? []]|[? []]]; constructor; cbn; tas.
          eapply subject_reduction1; tea.
          destruct tu as [s Ht]. exists s. eapply subject_reduction1; tea.
          econstructor; tea.
          2: eauto using red_cumul.
          right. destruct tu as [s ?]; exists s; eapply subject_reduction1; tea.
        + constructor; tas. eapply IHX; tas.
          eexists. now eapply p0.
          now eapply p. }
    eapply typing_ind_env; cbn; intros; try solve [econstructor; eauto with aa].
    - assert (X2: ∑ decl', nth_error Γ' n = Some decl'
             × red Σ.1 Γ' (lift0 (S n) (decl_type decl))
             (lift0 (S n) (decl_type decl'))) by now eapply nth_error_red1_ctx.
      destruct X2 as [decl' [H1 H2]].
      eapply type_Cumul. econstructor. eauto. exact H1.
      2: now eapply red_cumul_inv.
      right.
      clear decl' H1 H2.
      induction X1 in wfΓ, n, H, X0 |- *; cbn in *.
      + destruct n; cbn in *.
        * invc H. invs wfΓ. destruct X2 as [s Ht]; exists s.
          eapply (weakening _ _ [_] _ (tSort _)); tas; cbnr.
          constructor; tas. exists s.
          eapply subject_reduction; tea; auto.
        * invc H. invs wfΓ.
          eapply wf_local_isType_nth in H1; tea.
          destruct H1 as [s Ht]. exists s.
          rewrite simpl_lift0.
          eapply (weakening _ _ [_] _ (tSort _)); tas; cbnr.
          constructor; tas. destruct X2 as [s' ?]; exists s'.
          eapply subject_reduction; tea; auto.
      + destruct n; cbn in *.
        * invc H. invs wfΓ. destruct X2 as [s Ht]; exists s.
          eapply (weakening _ _ [_] _ (tSort _)); tas; cbnr.
          destruct p as [[? []]|[? []]]; constructor; cbn; tas.
          now exists s. 
          eapply subject_reduction; tea; auto.
          exists s. eapply subject_reduction; tea; auto.
          econstructor; tea.
          2: eauto using red_cumul.
          right. exists s; eapply subject_reduction1; tea.
        * invc H. invs wfΓ.
          eapply wf_local_isType_nth in H1; tea.
          destruct H1 as [s Ht]. exists s.
          rewrite simpl_lift0.
          eapply (weakening _ _ [_] _ (tSort _)); tas; cbnr.
          destruct p as [[? []]|[? []]]; constructor; cbn; tas.
          eapply subject_reduction; tea; auto.
          destruct X2 as [s' Ht']. exists s'.
          eapply subject_reduction; tea; auto.
          econstructor; tea.
          2: eauto using red_cumul.
          right. destruct X2 as [s' ?]; exists s'; eapply subject_reduction1; tea.
      + destruct n; cbn in *.
        * invc H. clear IHX1. invs wfΓ.
          -- invs X0. destruct tu as [s Ht]; exists s.
             eapply (weakening _ _ [_] _ (tSort _)); tas; cbnr.
             eapply (X _ _ wfΓ); tea. now constructor.
             eauto.
          -- invs X0. destruct tu as [s Ht]; exists s.
             eapply (weakening _ _ [_] _ (tSort _)); tas; cbnr.
             eapply (X _ _ wfΓ); tea. now constructor.
             eauto.
        * invs wfΓ; inv X0.
          -- specialize (IHX1 _ _ H X4).
             destruct IHX1 as [s ?]; exists s.
             rewrite simpl_lift0.
             eapply (weakening _ _ [_] _ (tSort _)); tas; cbnr.
             constructor. eauto.
             exists tu.π1. eauto.
          -- specialize (IHX1 _ _ H X5).
             destruct IHX1 as [s ?]; exists s.
             rewrite simpl_lift0.
             eapply (weakening _ _ [_] _ (tSort _)); tas; cbnr.
             constructor. eauto.
             exists tu.π1. eauto. cbn. eauto.
    - econstructor; tea; eauto.
      eapply All2_impl; tea; cbn.
      intros; utils.rdestruct; eauto.
    - assert (XX: red1_ctx Σ.1 (Γ ,,, fix_context mfix) (Γ' ,,, fix_context mfix))
        by now eapply red1_ctx_app.
      econstructor; tea.
      + set (Δ := Γ ,,, fix_context mfix) in *.
        assert (ZZ: ∑ wfΔ, All_local_env_over typing
                            (fun Σ Γ (_ : wf_local Σ Γ)  t T (_ : Σ;;; Γ |- t : T) =>
                               forall Γ', red1_ctx Σ Γ Γ' -> Σ;;; Γ' |- t : T) Σ Δ wfΔ). {
          clearbody Δ; clear -X0.
          induction X0.
          - eexists; constructor.
          - destruct t0 as [? [? ?]].
            eexists; unshelve econstructor; tea.
            exact IHX0.π1.
            eexists; eassumption.
            exact IHX0.π2. eassumption.
          - destruct IHX0 as [X1 X2].
            destruct t0 as [s [Y1 Y2]], t1 as [Y3 Y4].
            eexists.
            unshelve econstructor; tea. eexists; eassumption.
            eauto. }
        eapply X with (Γ ,,, fix_context mfix) ZZ.π1; tea. exact ZZ.π2.
      + eapply All_impl; tea.
        intros; utils.rdestruct; eauto. 
    - assert (XX: red1_ctx Σ.1 (Γ ,,, fix_context mfix) (Γ' ,,, fix_context mfix))
        by now eapply red1_ctx_app.
      econstructor; tea.
      + set (Δ := Γ ,,, fix_context mfix) in *.
        assert (ZZ: ∑ wfΔ, All_local_env_over typing
                            (fun Σ Γ (_ : wf_local Σ Γ)  t T (_ : Σ;;; Γ |- t : T) =>
                               forall Γ', red1_ctx Σ Γ Γ' -> Σ;;; Γ' |- t : T) Σ Δ wfΔ). {
          clearbody Δ; clear -X0.
          induction X0.
          - eexists; constructor.
          - destruct t0 as [? [? ?]].
            eexists; unshelve econstructor; tea.
            exact IHX0.π1.
            eexists; eassumption.
            exact IHX0.π2. eassumption.
          - destruct IHX0 as [X1 X2].
            destruct t0 as [s [Y1 Y2]], t1 as [Y3 Y4].
            eexists.
            unshelve econstructor; tea. eexists; eassumption.
            eauto. }
        eapply X with (Γ ,,, fix_context mfix) ZZ.π1; tea. exact ZZ.π2.
      + eapply All_impl; tea.
        intros; utils.rdestruct; eauto. 
    - econstructor.
      + now eapply X2.
      + destruct X3 as [[[ctx [s [H1 H2]]] X3]|X3]; [left|right].
        * cbn in *. exists ctx, s. split; eauto.
          eapply X; tea.
          now apply red1_ctx_app.
        * utils.rdestruct; eauto.
      + eapply cumul_red_ctx; tea. now apply red1_red_ctx.
  Qed.


  Lemma wf_local_red1 {Σ Γ Γ'} :
    wf Σ.1 -> 
    red1_ctx Σ.1 Γ Γ' -> wf_local Σ Γ -> wf_local Σ Γ'.
  Proof.
    intro hΣ. induction 1; cbn in *.
    - intro e. inversion e; subst; cbn in *.
      constructor; tas. destruct X0 as [s Ht]. exists s.
      eapply subject_reduction1; tea.
    - intro e. inversion e; subst; cbn in *.
      destruct p as [[? []]|[? []]]; constructor; cbn; tas.
      + eapply subject_reduction1; tea.
      + destruct X0; eexists; eapply subject_reduction1; tea.
      + econstructor; tea.
        right; destruct X0; eexists; eapply subject_reduction1; tea.
        econstructor 2. eassumption. reflexivity.
    - intro H; inversion H; subst; constructor; cbn in *; auto.
      + destruct X1 as [s Ht]. exists s. 
        eapply subject_reduction_ctx; tea.
      + destruct X1 as [s Ht]. exists s. 
        eapply subject_reduction_ctx; tea.
      + eapply subject_reduction_ctx; tea.
  Qed.

  Lemma eq_context_upto_names_upto_names Γ Δ :
    eq_context_upto_names Γ Δ -> Γ ≡Γ Δ.
  Proof.
    induction 1; cbnr; try constructor; eauto.
    destruct x as [? [] ?], y as [? [] ?]; cbn in *; subst; inversion e.
    all: constructor; cbnr; eauto.
  Qed.


  Lemma wf_local_red {Σ Γ Γ'} :
    wf Σ.1 -> 
    red_ctx Σ.1 Γ Γ' -> wf_local Σ Γ -> wf_local Σ Γ'.
  Proof.
    intros hΣ h. apply red_ctx_clos_rt_red1_ctx in h.
    induction h; eauto using wf_local_red1.
    apply eq_context_upto_names_upto_names in e.
    eauto using wf_local_alpha.
  Qed.


  Lemma wf_local_subst1 Σ (wfΣ : wf Σ.1) Γ na b t Γ' :
      wf_local Σ (Γ ,,, [],, vdef na b t ,,, Γ') ->
      wf_local Σ (Γ ,,, subst_context [b] 0 Γ').
  Proof.
    induction Γ' as [|d Γ']; [now inversion 1|].
    change (d :: Γ') with (Γ' ,, d).
    destruct d as [na' [bd|] ty]; rewrite !app_context_cons; intro HH.
    - rewrite subst_context_snoc0. simpl.
      inversion HH; subst; cbn in *. destruct X0 as [s X0].
      change (Γ,, vdef na b t ,,, Γ') with (Γ ,,, [vdef na b t] ,,, Γ') in *.
      assert (subslet Σ Γ [b] [vdef na b t]). {
        pose proof (cons_let_def Σ Γ [] [] na b t) as XX.
        rewrite !subst_empty in XX. apply XX. constructor.
        apply wf_local_app in X. inversion X; subst; cbn in *; assumption. }
      constructor; cbn; auto. exists s.
      change (tSort s) with (subst [b] #|Γ'| (tSort s)).
      all: eapply substitution_alt; tea.
    - rewrite subst_context_snoc0. simpl.
      inversion HH; subst; cbn in *. destruct X0 as [s X0].
      change (Γ,, vdef na b t ,,, Γ') with (Γ ,,, [vdef na b t] ,,, Γ') in *.
      assert (subslet Σ Γ [b] [vdef na b t]). {
        pose proof (cons_let_def Σ Γ [] [] na b t) as XX.
        rewrite !subst_empty in XX. apply XX. constructor.
        apply wf_local_app in X. inversion X; subst; cbn in *; assumption. }
      constructor; cbn; auto. exists s.
      change (tSort s) with (subst [b] #|Γ'| (tSort s)).
      all: eapply substitution_alt; tea.
  Qed.


  Lemma red_ctx_app_context_l {Σ Γ Γ' Δ}
    : red_ctx Σ Γ Γ' -> red_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ).
  Proof.
    induction Δ as [|[na [bd|] ty] Δ]; [trivial| |];
      intro H; simpl; constructor; cbn; eauto; now apply IHΔ.
  Qed.


   Lemma isWfArity_red1 {Σ Γ A B} :
     wf Σ.1 ->
       red1 (fst Σ) Γ A B ->
       isWfArity typing Σ Γ A ->
       isWfArity typing Σ Γ B.
   Proof.
     intro wfΣ. induction 1 using red1_ind_all.
     all: intros [ctx [s [H1 H2]]]; cbn in *; try discriminate.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         [|rewrite ee in H1; discriminate].
       pose proof (subst_destArity [] b' [b] 0) as H; cbn in H.
       rewrite ee in H. eexists _, s'. split. eassumption.
       rewrite ee in H1. cbn in *. inversion H1; subst.
       rewrite app_context_assoc in H2.
       now eapply wf_local_subst1.
     - rewrite destArity_tFix in H1; discriminate.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       eexists _, s'; split. cbn. rewrite destArity_app ee. reflexivity.
       cbn in H1. inversion H1; subst.
       eapply wf_local_red; try exact H2; tas.
       rewrite !app_context_assoc. apply red_ctx_app_context_l.
       constructor; cbn. reflexivity. split; auto.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       eexists _, s'; split. cbn. rewrite destArity_app ee. reflexivity.
       cbn in H1. inversion H1; subst.
       eapply wf_local_red; try exact H2; tas.
       rewrite !app_context_assoc. apply red_ctx_app_context_l.
       constructor; cbn. reflexivity. split; auto.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       forward IHX. {
         eexists _, s'; split; tea. cbn in H1.
         inversion H1; subst. now rewrite app_context_assoc in H2. }
       destruct IHX as [ctx'' [s'' [ee' ?]]].
       eexists _, s''; split. cbn. rewrite destArity_app ee'. reflexivity.
       now rewrite app_context_assoc.
     - rewrite destArity_app in H1.
       case_eq (destArity [] M2); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       eexists _, s'; split. cbn. rewrite destArity_app ee. reflexivity.
       cbn in H1. inversion H1; subst.
       eapply wf_local_red; try exact H2; tas.
       rewrite !app_context_assoc. apply red_ctx_app_context_l.
       constructor; cbn. reflexivity. auto.
     - rewrite destArity_app in H1.
       case_eq (destArity [] M2); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       forward IHX. {
         eexists _, s'; split; tea. cbn in H1.
         inversion H1; subst. now rewrite app_context_assoc in H2. }
       destruct IHX as [ctx'' [s'' [ee' ?]]].
       eexists _, s''; split. cbn. rewrite destArity_app ee'. reflexivity.
       now rewrite app_context_assoc.
   Qed.

   Lemma isWfArity_red {Σ Γ A B} :
     wf Σ.1 ->
     red (fst Σ) Γ A B ->
     isWfArity typing Σ Γ A ->
     isWfArity typing Σ Γ B.
   Proof.
     induction 2.
     - easy.
     - intro. now eapply isWfArity_red1.
   Qed.

   Lemma isWfArity_or_Type_red {Σ Γ A B} :
     wf Σ.1 ->
     red (fst Σ) Γ A B ->
     isWfArity_or_Type Σ Γ A ->
     isWfArity_or_Type Σ Γ B.
   Proof.
     intros ? ? [?|[? ?]]; [left|right].
     eapply isWfArity_red; eassumption.
     eexists. eapply subject_reduction; tea.
   Qed.

  Lemma type_reduction {Σ Γ t A B}
    : wf Σ.1 -> wf_local Σ Γ -> Σ ;;; Γ |- t : A -> red (fst Σ) Γ A B -> Σ ;;; Γ |- t : B.
  Proof.
    intros HΣ' HΓ Ht Hr.
    econstructor. eassumption.
    2: now eapply cumul_red_l'.
    destruct (validity_term HΣ' HΓ Ht).
    - left. eapply isWfArity_red; try eassumption.
    - destruct i as [s HA]. right.
      exists s. eapply subject_reduction; eassumption.
  Defined.

End SRContext.
