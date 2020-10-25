From Equations Require Import Equations.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.PCUIC Require Import PCUICAstUtils.
From MetaCoq.PCUIC Require Import PCUICContextConversion.
From MetaCoq.PCUIC Require Import PCUICConversion.
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
  
  Definition conv_cum_napp leq Γ napp t t' :=
    match t with
    | tInd _ _
    | tConstruct _ _ _ => ∥eq_termp_napp leq napp t t'∥
    | _ => conv_cum leq Σ Γ t t'
    end.

  Lemma conv_cum_mkApps_inv leq Γ hd args hd' args' :
    conv_cum leq Σ Γ (mkApps hd args) (mkApps hd' args') ->
    isApp hd = false ->
    isApp hd' = false ->
    whnf RedFlags.default Σ Γ (mkApps hd args) ->
    whnf RedFlags.default Σ Γ (mkApps hd' args') ->
    ∥conv_cum_napp leq Γ #|args| hd hd' × conv_terms Σ Γ args args'∥.
  Proof.
    intros conv notapp notapp' wh wh'.
    apply conv_cum_alt in conv as [(?&?&(r1&r2)&e)].
    apply whnf_red_mkApps_l in r1 as [(?&?&->&?&?)]; auto.
    apply whnf_red_mkApps_l in r2 as [(?&?&->&?&?)]; auto.
    assert (isApp x1 = false).
    { erewrite whnf_red_isApp.
      3: eauto.
      1: assumption.
      apply whnf_mkApps_inv in wh; auto.
      now rewrite notapp. }
    assert (isApp x = false).
    { erewrite whnf_red_isApp.
      3: eauto.
      1: assumption.
      apply whnf_mkApps_inv in wh'; auto.
      now rewrite notapp'. }
    apply eq_termp_mkApps_inv in e as (?&?); auto.
    constructor.
    split.
    - assert (isIndConstructApp x1 = isIndConstructApp hd).
      { eapply whnf_red_isIndConstructApp; eauto.
        apply whnf_mkApps_inv in wh; auto.
        now rewrite notapp. }
      destruct hd.
      all: cbn.
      1-9, 12-15: apply conv_cum_alt.
      1-13: constructor.
      1-13: exists x1, x.
      1-13: split; [split|]; eauto with pcuic.
      1-13: (eapply eq_term_upto_univ_napp_nonind; [exact e|try exact H1]).
      1: discriminate notapp.
      all: apply whnf_mkApps_inv in wh; auto.
      all: eapply whnf_red_inv in r; auto.
      all: depelim r.
      all: apply whnf_mkApps_inv in wh'; auto; [|now rewrite notapp'].
      all: eapply whnf_red_inv in r0; auto.
      all: depelim e.
      all: depelim r0.
      all: apply All2_length in a.
      all: constructor; constructor; rewrite a; auto.
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
    eapply whnf_red_inv in r1; eauto.
    eapply whnf_red_inv in r2; eauto.
    depelim r1.
    depelim r2.
    depelim e.
    constructor.
    split; [easy|].
    split; [apply conv_alt_red; now exists motive'0, motive'1|].
    split; [apply conv_alt_red; now exists discr'0, discr'1|].
    clear -a X1 X4.
    induction a in brs, brs', brs'0, brs'1, X1, X4, a |- *;
      depelim X1; depelim X4; [now constructor|].
    constructor.
    + destruct p, p0, r.
      split; [congruence|].
      apply conv_alt_red; now exists x.2, y.2.
    + now apply IHa.
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
    assert (forall defs i, whnf RedFlags.default Σ Γ (tFix defs i)).
    { intros defs i.
      apply whnf_fixapp with (v := []).
      destruct unfold_fix as [(?&?)|]; [|easy].
      now rewrite nth_error_nil. }
    eapply whnf_red_inv in r1; eauto.
    eapply whnf_red_inv in r2; eauto.
    depelim r1.
    depelim r2.
    depelim e.
    constructor.
    split; [easy|].
    clear -a X X0.
    cut (#|mfix| = #|mfix'|);
      [|now apply All2_length in a; apply All2_length in X; apply All2_length in X0].
    revert a X X0.
    generalize mfix at 1 3 4.
    generalize mfix' at 1 3.
    intros ctx_fix ctx_fix'.
    intros all1 all2 all len_eq.
    induction all in mfix, mfix', mfix'0, mfix'1, all1, all2, all |- *;
      depelim all1; depelim all2; [constructor|].
    constructor; [|now auto].
    destruct p as ((?&?)&?), p0 as (?&?&?&?), r as (?&?&?&?).
    split; [congruence|].
    split; [now apply conv_alt_red; exists (dtype x), (dtype y)|].
    apply conv_alt_red.
    exists (dbody x), (dbody y).
    split; [|easy].
    split; [easy|].
    eapply context_change_decl_types_red; eauto.
    eapply fix_context_change_decl_types; eauto.
  Qed.

  Lemma conv_cum_tProj_inv leq Γ p c p' c' :
    conv_cum leq Σ Γ (tProj p c) (tProj p' c') ->
    whnf RedFlags.default Σ Γ (tProj p c) ->
    whnf RedFlags.default Σ Γ (tProj p' c') ->
    ∥ p = p' × Σ;;; Γ |- c = c' ∥.
  Proof.
    intros conv whl whr.
    apply conv_cum_alt in conv as [(?&?&(r1&r2)&?)].
    eapply whnf_red_inv in r1; eauto.
    eapply whnf_red_inv in r2; eauto.
    depelim r1.
    depelim r2.
    depelim e.
    constructor.
    split; [easy|].
    now apply conv_alt_red; exists c'0, c'1.
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
  
  Lemma conv_cum_red_inv' leq Γ Γ' t1 t2 t1' t2' :
    conv_context Σ Γ Γ' ->
    conv_cum leq Σ Γ t1 t2 ->
    red Σ Γ t1 t1' ->
    red Σ Γ' t2 t2' ->
    conv_cum leq Σ Γ t1' t2'.
  Proof.
    intros cc r1 r2 conv_ctx.
    destruct wf.
    eapply conv_cum_red_inv; [|now eauto|reflexivity].
    eapply conv_cum_conv_ctx; eauto.
    2: apply conv_context_sym; eauto.
    eapply conv_cum_red_inv; [|reflexivity|now eauto].
    eapply conv_cum_conv_ctx; eauto.
  Qed.
End fixed.
