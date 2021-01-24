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
  
  Lemma whnf_red_isIndConstructApp Γ t t' :
    whnf_red Σ Γ t t' ->
    isIndConstructApp t' = isIndConstructApp t.
  Proof.
    intros r.
    induction r; auto.
    rewrite (isIndConstructApp_mkApps _ [arg']), (isIndConstructApp_mkApps _ [arg]).
    apply IHr.
  Qed.
  
  Lemma eq_termp_mkApps_inv leq v args v' args' :
    isApp v = false ->
    isApp v' = false ->
    eq_termp leq Σ (mkApps v args) (mkApps v' args') ->
    eq_termp_napp leq Σ #|args| v v' × All2 (fun x y => eq_term Σ Σ x y) args args'.
  Proof.
    intros noapp1 noapp2 eq.
    now apply eq_term_upto_univ_mkApps_inv in eq as (?&?).
  Qed.
  
  Definition conv_cum_napp leq Γ napp t t' :=
    match t with
    | tInd _ _
    | tConstruct _ _ _ => ∥eq_termp_napp leq Σ napp t t'∥
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
    apply whnf_red_inv, whnf_red_mkApps_l_inv in r1 as (?&?&->&?&?); auto.
    apply whnf_red_inv, whnf_red_mkApps_l_inv in r2 as (?&?&->&?&?); auto.
    apply whnf_red_isApp in w as ?.
    apply whnf_red_isApp in w0 as ?.
    apply eq_termp_mkApps_inv in e as (?&?); try congruence.
    constructor.
    split.
    - apply whnf_red_isIndConstructApp in w as ?.
      destruct hd.
      all: cbn.
      1-9, 12-15: apply conv_cum_alt.
      1-13: constructor.
      1-13: exists x1, x.
      1-13: split; [split|]; eauto with pcuic.
      1-13: (eapply eq_term_upto_univ_napp_nonind; [exact e|try exact H1]).
      1-13: cbn in *; congruence.
      all: depelim w.
      all: depelim e.
      all: depelim w0.
      all: apply All2_length in a.
      all: try (constructor; constructor; rewrite a; auto).
      all: destruct leq; cbn; repeat constructor.
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
      conv_predicate Σ Γ motive motive' ×
      Σ;;; Γ |- discr = discr' ×
      conv_brs Σ Γ brs brs'∥.
  Proof.
    intros conv whl whr.
    depelim whl; solve_discr.
    depelim w; solve_discr; try discriminate.
    depelim whr; solve_discr.
    depelim w0; solve_discr; try discriminate.
    apply conv_cum_alt in conv as [(?&?&(r1&r2)&eq)].
    eapply whnf_red_inv in r1; eauto.
    eapply whnf_red_inv in r2; eauto.
    depelim r1.
    depelim r2.
    depelim eq.
    constructor.
    split; [easy|].
    split; [todo "case"|].
     (* apply conv_alt_red; now exists motive'0, motive'1|]. *)
    split; [apply conv_alt_red; now exists discr'0, discr'1|].
    clear -a0 a2 a3.
    induction a0 in brs', brs'1, a2, a3 |- *;
      depelim a2; depelim a3; [constructor|].
    destruct p, p0, r.
    constructor; eauto.
    + todo "case".
    + todo "case".
      (*apply conv_alt_red. exists (bbody y), (bbody y0).
      splits; eauto. todo "case".*)

  Qed.
  
  Lemma conv_cum_tFix_inv leq Γ mfix idx mfix' idx' :
    conv_cum leq Σ Γ (tFix mfix idx) (tFix mfix' idx') ->
    ∥idx = idx' ×
     All2 (fun d d' => rarg d = rarg d' × eq_binder_annot d.(dname) d'.(dname) ×
                       Σ;;; Γ |- dtype d = dtype d' ×
                       Σ;;; Γ,,, fix_context mfix |- dbody d = dbody d')
          mfix mfix'∥.
  Proof.
    intros conv.
    apply conv_cum_alt in conv as [(?&?&(r1&r2)&eq)].
    assert (forall defs i, whnf RedFlags.default Σ Γ (tFix defs i)).
    { intros defs i.
      apply whnf_fixapp with (v := []).
      destruct unfold_fix as [(?&?)|]; [|easy].
      now rewrite nth_error_nil. }
    eapply whnf_red_inv in r1; eauto.
    eapply whnf_red_inv in r2; eauto.
    depelim r1.
    depelim r2.
    depelim eq.
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
    induction all in mfix, mfix', mfix'0, mfix'1, all1, all2, all |- *;
      depelim all1; depelim all2; [constructor|].
    constructor; [|now auto].
    destruct r as ((?&?)&?), p as (?&?&?&?), p0 as (?&?&?&?).
    split; [congruence|]. split; auto; try congruence.
    split; [now apply conv_alt_red; exists (dtype x), (dtype y)|].
    apply conv_alt_red.
    exists (dbody x), (dbody y).
    split; [|easy].
    split; [easy|].
    eapply PCUICRedTypeIrrelevance.context_pres_let_bodies_red; eauto.
    eapply PCUICRedTypeIrrelevance.fix_context_pres_let_bodies; eauto.
  Qed.
  
  Lemma conv_cum_tCoFix_inv leq Γ mfix idx mfix' idx' :
    conv_cum leq Σ Γ (tCoFix mfix idx) (tCoFix mfix' idx') ->
    ∥idx = idx' ×
     All2 (fun d d' => rarg d = rarg d' × eq_binder_annot d.(dname) d'.(dname) ×
                       Σ;;; Γ |- dtype d = dtype d' ×
                       Σ;;; Γ,,, fix_context mfix |- dbody d = dbody d')
          mfix mfix'∥.
  Proof.
    intros conv.
    apply conv_cum_alt in conv as [(?&?&(r1&r2)&eq)].
    assert (forall defs i, whnf RedFlags.default Σ Γ (tCoFix defs i))
      by (intros; apply whnf_cofixapp with (v := [])).
    eapply whnf_red_inv in r1; eauto.
    eapply whnf_red_inv in r2; eauto.
    depelim r1.
    depelim r2.
    depelim eq.
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
    induction all in mfix, mfix', mfix'0, mfix'1, all1, all2, all |- *;
      depelim all1; depelim all2; [constructor|].
    constructor; [|now auto].
    destruct r as ((?&?)&?), p as (?&?&?&?), p0 as (?&?&?&?).
    split; [congruence|]. split; [congruence|].
    split; [now apply conv_alt_red; exists (dtype x), (dtype y)|].
    apply conv_alt_red.
    exists (dbody x), (dbody y).
    split; [|easy].
    split; [easy|].
    eapply PCUICRedTypeIrrelevance.context_pres_let_bodies_red; eauto.
    eapply PCUICRedTypeIrrelevance.fix_context_pres_let_bodies; eauto.
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
    apply conv_alt_red; eauto.
  Qed.
End fixed.
