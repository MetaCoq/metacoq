From Equations Require Import Equations.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.PCUIC Require Import PCUICAstUtils.
From MetaCoq.PCUIC Require Import PCUICContextConversion.
From MetaCoq.PCUIC Require Import PCUICCumulativity.
From MetaCoq.PCUIC Require Import PCUICCumulProp.
From MetaCoq.PCUIC Require Import PCUICEquality.
From MetaCoq.PCUIC Require Import PCUICLiftSubst.
From MetaCoq.PCUIC Require Import PCUICNormal.
From MetaCoq.PCUIC Require Import PCUICReduction.
From MetaCoq.PCUIC Require Import PCUICTyping.
From MetaCoq.Template Require Import config.
From MetaCoq.Template Require Import utils.

Local Set Keyed Unification.

Set Default Goal Selector "!".

Section fixed.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (wf : ∥wf_ext Σ∥).
  
  Definition conv_pb_rel (pb : conv_pb) :=
    match pb with
    | Conv => eq_universe
    | Cumul => leq_universe
    end.
  
  Definition eq_termp_napp leq napp :=
    eq_term_upto_univ_napp Σ (eq_universe Σ) (conv_pb_rel leq Σ) napp.
  
  Notation eq_termp leq := (eq_termp_napp leq 0).
  
  Definition isIndConstructApp (t : term) : bool :=
    match (decompose_app t).1 with
    | tInd _ _
    | tConstruct _ _ _ => true
    | _ => false
    end.

  Lemma isIndConstructApp_mkApps hd args :
    isIndConstructApp (mkApps hd args) = isIndConstructApp hd.
  Proof.
    unfold isIndConstructApp.
    destruct (mkApps_elim hd args).
    now rewrite !decompose_app_mkApps by easy.
  Qed.

  Lemma eq_term_upto_univ_napp_nonind Re Rle napp t t' :
    eq_term_upto_univ_napp Σ Re Rle napp t t' ->
    isIndConstructApp t = false ->
    eq_term_upto_univ Σ Re Rle t t'.
  Proof.
    intros eq not_ind.
    generalize 0.
    intros k.
    induction eq in k, not_ind |- *; eauto using eq_term_upto_univ_napp.
    - rewrite (isIndConstructApp_mkApps _ [u]) in not_ind.
      constructor; auto.
    - discriminate not_ind.
    - discriminate not_ind.
  Qed.

  Lemma whne_red1_isIndConstructApp Γ t t' :
    whne RedFlags.default Σ Γ t ->
    red1 Σ Γ t t' ->
    isIndConstructApp t' = isIndConstructApp t.
  Proof.
    apply (whne_red1_ind
             RedFlags.default Σ Γ
             (fun t t' => isIndConstructApp t' = isIndConstructApp t)); intros; cbn in *; try easy.
    - now rewrite !(isIndConstructApp_mkApps _ [v]).
    - now rewrite (isIndConstructApp_mkApps _ [v]), (isIndConstructApp_mkApps _ [N2]).
    - now rewrite !isIndConstructApp_mkApps.
    - now rewrite !isIndConstructApp_mkApps.
    - now rewrite !isIndConstructApp_mkApps.
  Qed.
  
  Lemma whnf_red1_isIndConstructApp Γ t t' :
    whnf RedFlags.default Σ Γ t ->
    red1 Σ Γ t t' ->
    isIndConstructApp t' = isIndConstructApp t.
  Proof.
    intros wh r.
    depelim wh.
    - eapply whne_red1_isIndConstructApp; eauto.
    - depelim r; solve_discr.
    - depelim r; auto; solve_discr.
    - depelim r; auto; solve_discr.
    - apply red1_mkApps_tConstruct_inv in r as (?&->&?).
      now rewrite !isIndConstructApp_mkApps.
    - apply red1_mkApps_tInd_inv in r as (?&->&?).
      now rewrite !isIndConstructApp_mkApps.
    - apply red1_mkApps_tFix_inv in r.
      2: { destruct unfold_fix as [(?&?)|]; [|easy].
           now unfold is_constructor; rewrite H. }
      now destruct r as [[(?&->&o)|(?&->&o)]|(?&->&o)];
        rewrite !isIndConstructApp_mkApps.
    - apply red1_mkApps_tCoFix_inv in r.
      now destruct r as [[(?&->&o)|(?&->&o)]|(?&->&o)];
        rewrite !isIndConstructApp_mkApps.
  Qed.
  
  Lemma whnf_red_isIndConstructApp Γ t t' :
    whnf RedFlags.default Σ Γ t ->
    red Σ Γ t t' ->
    isIndConstructApp t' = isIndConstructApp t.
  Proof.
    intros wh r.
    induction r in wh |- * using red_rect_n1.
    - easy.
    - apply whnf_red1_isIndConstructApp in X as ->; eauto.
      eapply whnf_pres; eauto.
  Qed.

  Lemma conv_cum_alt leq Γ t t' :
    conv_cum leq Σ Γ t t' <->
    ∥∑ v v', (red Σ Γ t v × red Σ Γ t' v') × eq_termp leq v v'∥.
  Proof.
    assert (forall P Q, (P <~> Q) -> (∥P∥ <-> ∥Q∥)) by
        (intros P Q H; split; intros [p]; constructor; apply H in p; auto).
    destruct leq; cbn; apply H; [apply conv_alt_red|apply cumul_alt].
  Qed.

  Lemma eq_term_eq_termp leq x y :
    eq_term Σ Σ x y ->
    eq_termp leq x y.
  Proof.
    destruct leq; [easy|].
    cbn.
    now apply PCUICCumulProp.eq_term_upto_univ_napp_leq.
  Qed.
  
  Lemma eq_termp_mkApps_inv leq v args v' args' :
    isApp v = false ->
    isApp v' = false ->
    eq_termp leq (mkApps v args) (mkApps v' args') ->
    eq_termp_napp leq #|args| v v' × All2 (fun x y => eq_term Σ Σ x y) args args'.
  Proof.
    intros noapp1 noapp2 eq.
    now apply eq_term_upto_univ_mkApps_inv in eq as (?&?).
  Qed.

  Lemma conv_cum_mkApps_inv leq Γ hd args hd' args' :
    conv_cum leq Σ Γ (mkApps hd args) (mkApps hd' args') ->
    match hd with
    | tApp _ _
    | tInd _ _
    | tConstruct _ _ _ => False
    | _ => True
    end ->
    match hd' with
    | tApp _ _
    | tInd _ _
    | tConstruct _ _ _ => False
    | _ => True
    end ->
    whnf RedFlags.default Σ Γ (mkApps hd args) ->
    whnf RedFlags.default Σ Γ (mkApps hd' args') ->
    ∥conv_cum leq Σ Γ hd hd' × All2 (conv Σ Γ) args args'∥.
  Proof.
    intros conv shape shape' wh wh'.
    apply conv_cum_alt in conv as [(?&?&(r1&r2)&e)].
    apply whnf_red_from_mkApps in r1 as [(?&?&->&?&?)]; auto.
    apply whnf_red_from_mkApps in r2 as [(?&?&->&?&?)]; auto.
    assert (isApp x1 = false).
    { erewrite whnf_red_isApp.
      3: eauto.
      1: now destruct hd.
      apply whnf_mkApps_inv in wh; auto.
      now destruct hd. }
    assert (isApp x = false).
    { erewrite whnf_red_isApp.
      3: eauto.
      1: now destruct hd'.
      apply whnf_mkApps_inv in wh'; auto.
      now destruct hd'. }
    apply eq_termp_mkApps_inv in e as (?&?); auto.
    constructor.
    split.
    - apply conv_cum_alt.
      constructor.
      exists x1, x.
      split; [split|]; eauto with pcuic.
      eapply eq_term_upto_univ_napp_nonind; eauto.
      erewrite whnf_red_isIndConstructApp; [| |now eauto].
      1: now destruct hd.
      apply whnf_mkApps_inv in wh; auto.
      now destruct hd.
    - clear -a1 a a0.
      induction a1 in args, args', x2, a, x3, a0, a1 |- *; depelim a; depelim a0; [now constructor|].
      constructor.
      + apply conv_alt_red.
        now exists x, y.
      + now apply IHa1.
  Qed.
  
  Lemma conv_cum_tCase_inv leq Γ p motive discr brs p' motive' discr' brs' :
    conv_cum leq Σ Γ (tCase p motive discr brs) (tCase p' motive' discr' brs') ->
    whnf RedFlags.default Σ Γ (tCase p motive discr brs) ->
    whnf RedFlags.default Σ Γ (tCase p' motive' discr' brs') ->
    ∥ p = p' ×
      Σ;;; Γ |- motive = motive' ×
      Σ;;; Γ |- discr = discr' ×
      All2 (fun br br' => br.1 = br'.1 × Σ;;; Γ |- br.2 = br'.2) brs brs'∥.
  Proof.
    intros conv whl whr.
    depelim whl; solve_discr.
    depelim H; solve_discr; try discriminate.
    depelim whr; solve_discr.
    depelim H0; solve_discr; try discriminate.
    apply conv_cum_alt in conv as [(?&?&(r1&r2)&?)].
    apply whne_red_from_tCase in r1 as [(?&?&?&->&?&?&?)]; auto.
    apply whne_red_from_tCase in r2 as [(?&?&?&->&?&?&?)]; auto.
    depelim e.
    constructor.
    split; [easy|].
    split; [apply conv_alt_red; now exists x1, x|].
    split; [apply conv_alt_red; now exists x2, x4|].
    clear -a a0 a1.
    induction a1 in brs, brs', x3, a, x5, a0, a1 |- *; depelim a; depelim a0; [now constructor|].
    constructor.
    + destruct p, p0, r.
      split; [congruence|].
      apply conv_alt_red; now exists x.2, y.2.
    + now apply IHa1.
  Qed.
  
  Lemma fix_context_change_decl_types Γ mfix mfix' :
    #|mfix| = #|mfix'| ->
    context_relation (fun _ _ => change_decl_type) (Γ,,, fix_context mfix) (Γ,,, fix_context mfix').
  Proof.
    intros len.
    apply context_relation_app_inv.
    - now rewrite !fix_context_length.
    - apply context_relation_refl.
      intros.
      destruct x.
      destruct decl_body; constructor.
    - unfold fix_context, mapi.
      generalize 0 at 2 4.
      induction mfix in mfix', len |- *; intros n.
      + destruct mfix'; [|cbn in *; discriminate len].
        constructor.
      + destruct mfix'; cbn in *; [discriminate len|].
        apply context_relation_app_inv.
        * now rewrite !List.rev_length, !mapi_rec_length.
        * constructor; [constructor|].
          constructor.
        * apply IHmfix; lia.
  Qed.
  
  Lemma red_tFix_inv Γ mfix idx t :
    red Σ Γ (tFix mfix idx) t ->
    ∑ mfix',
     t = tFix mfix' idx ×
     All2 (fun d d' => dname d = dname d' × rarg d = rarg d' ×
                       red Σ Γ (dtype d) (dtype d') ×
                       red Σ (Γ,,, fix_context mfix) (dbody d) (dbody d'))
          mfix mfix'.
  Proof.
    intros r.
    remember (tFix mfix idx) eqn:fromeq.
    revert mfix fromeq.
    induction r using red_rect_n1; intros mfix ->.
    - eexists _; split; [reflexivity|].
      apply All2_same.
      eauto.
    - specialize (IHr _ eq_refl) as (?&->&all).
      depelim X.
      + exfalso.
        destruct args using List.rev_ind; [|rewrite <- mkApps_nested in H; discriminate H].
        unfold is_constructor in e0.
        rewrite nth_error_nil in e0; congruence.
      + match type of all with
        | All2 ?P _ _ => eapply OnOne2_All2 with (Q := P) in o
        end; eauto.
        2: intros ? ? (?&[= -> -> ->]); eauto.
        eexists _; split; [reflexivity|].
        eapply All2_trans; eauto.
        intros ? ? ? (?&?&?&?) (?&?&?&?); eauto.
        do 2 (split; [easy|]).
        split; [etransitivity; eauto|].
        etransitivity; eauto.
      + match type of all with
        | All2 ?P _ _ => eapply OnOne2_All2 with (Q := P) in o
        end; eauto.
        2: { intros ? ? (?&[= -> -> ->]); eauto.
             do 2 (split; [easy|]).
             split; [etransitivity; eauto|].
             eapply context_change_decl_types_red; eauto.
             apply fix_context_change_decl_types.
             apply All2_length in all.
             easy. }
        eexists _; split; [reflexivity|].
        eapply All2_trans; eauto.
        intros ? ? ? (?&?&?&?) (?&?&?&?); eauto.
        do 2 (split; [easy|]).
        split; [etransitivity; eauto|].
        etransitivity; eauto.
  Qed.
  
  Lemma conv_cum_tFix_inv leq Γ mfix idx mfix' idx' :
    conv_cum leq Σ Γ (tFix mfix idx) (tFix mfix' idx') ->
    ∥idx = idx' ×
     All2 (fun d d' => rarg d = rarg d' ×
                       Σ;;; Γ |- dtype d = dtype d' ×
                       Σ;;; Γ,,, fix_context mfix |- dbody d = dbody d')
          mfix mfix'∥.
  Proof.
    intros conv.
    apply conv_cum_alt in conv as [(?&?&(r1&r2)&?)].
    apply red_tFix_inv in r1 as (?&->&?).
    apply red_tFix_inv in r2 as (?&->&?).
    depelim e.
    constructor.
    split; [easy|].
    clear -a a0 a1.
    cut (#|mfix| = #|mfix'|);
      [|now apply All2_length in a; apply All2_length in a0; apply All2_length in a1].
    revert a a0 a1.
    generalize mfix at 1 3 4.
    generalize mfix' at 1 3.
    intros ctx_fix ctx_fix'.
    intros all1 all2 all len_eq.
    induction all in mfix, mfix', x1, x, all1, all2, all |- *;
      depelim all1; depelim all2; [constructor|].
    constructor; [|now auto].
    destruct p as (?&?&?&?), p0 as (?&?&?&?), r as ((?&?)&?).
    split; [congruence|].
    split; [now apply conv_alt_red; exists (dtype x), (dtype y)|].
    apply conv_alt_red.
    exists (dbody x), (dbody y).
    split; [|easy].
    split; [easy|].
    eapply context_change_decl_types_red; eauto.
    eapply fix_context_change_decl_types; eauto.
  Qed.
  
  (* TODO: Move to a place that actually should be depending on typing *)
  Lemma conv_cum_red_inv leq Γ t1 t2 t1' t2' :
    conv_cum leq Σ Γ t1 t2 ->
    red Σ Γ t1 t1' ->
    red Σ Γ t2 t2' ->
    conv_cum leq Σ Γ t1' t2'.
  Proof.
    destruct wf.
    intros cc r1 r2.
    destruct leq; cbn in *.
    - destruct cc.
      constructor.
      eapply PCUICConversion.conv_red_l_inv; [eauto| |eauto].
      apply conv_sym.
      eapply PCUICConversion.conv_red_l_inv; [eauto| |eauto].
      apply conv_sym.
      auto.
    - destruct cc.
      constructor.
      eapply PCUICConversion.cumul_red_l_inv; [eauto| |eauto].
      eapply PCUICConversion.cumul_red_r_inv; [eauto| |eauto].
      auto.
  Qed.

End fixed.
