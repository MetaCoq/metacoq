From Coq Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICContextConversion PCUICContextReduction
  PCUICCumulativity PCUICConversion PCUICEquality PCUICLiftSubst PCUICNormal PCUICReduction PCUICTyping
  PCUICGlobalEnv PCUICConfluence PCUICSubstitution PCUICClosed PCUICClosedTyp
  PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
  PCUICWellScopedCumulativity PCUICOnFreeVars PCUICSR.

From MetaCoq.Template Require Import config.
From MetaCoq.Template Require Import utils.

Local Set Keyed Unification.

Set Default Goal Selector "!".

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Definition conv_cum {cf:checker_flags} pb Σ Γ u v :=
  ∥ Σ ;;; Γ ⊢ u ≤[pb] v ∥.

Lemma eq_term_eq_termp {cf:checker_flags} leq (Σ : global_env_ext) x y :
  eq_term Σ Σ x y ->
  eq_termp leq Σ x y.
Proof.
  destruct leq; [easy|].
  cbn.
  apply eq_term_upto_univ_leq; cbn; auto.
Qed.

Lemma alt_into_ws_cumul_pb_terms {cf Σ} {wfΣ : wf Σ} {Γ l l'} :
  All2 (convAlgo Σ Γ) l l' ->
  is_closed_context Γ ->
  forallb (is_open_term Γ) l ->
  forallb (is_open_term Γ) l' ->
  ws_cumul_pb_terms Σ Γ l l'.
Proof.
  solve_all. eapply into_ws_cumul_pb; tea.
Qed.

(** Might be better suited with [red_context] hyps ensuring closedness directly *)
Lemma red_ctx_rel_par_conv {cf Σ Γ Γ0 Γ0' Γ1 Γ1'} {wfΣ : wf Σ} :
  is_closed_context (Γ ,,, Γ0) ->
  is_closed_context (Γ ,,, Γ1) ->
  red_ctx_rel Σ Γ Γ0 Γ0' ->
  red_ctx_rel Σ Γ Γ1 Γ1' ->
  eq_context_upto Σ (eq_universe Σ) (eq_universe Σ) Γ0' Γ1' ->
  ws_cumul_ctx_pb_rel Conv Σ Γ Γ0 Γ1.
Proof.
  intros clΓ0 clΓ1 r0 r1 eq.
  apply red_ctx_rel_red_context_rel, red_context_app_same_left in r0; auto.
  2:{ now eapply on_free_vars_ctx_on_ctx_free_vars_closedP_impl. }
  apply red_ctx_rel_red_context_rel, red_context_app_same_left in r1; auto.
  2:{ now eapply on_free_vars_ctx_on_ctx_free_vars_closedP_impl. }
  eapply red_ctx_red_context in r0; eapply red_ctx_red_context in r1.
  eapply into_closed_red_ctx in r0 => //.
  eapply into_closed_red_ctx in r1 => //.
  eapply (red_ctx_ws_cumul_ctx_pb (l:=Conv)) in r0.
  eapply (red_ctx_ws_cumul_ctx_pb (l:=Conv)) in r1.
  apply ws_cumul_ctx_pb_rel_app. etransitivity; tea.
  symmetry. etransitivity; tea.
  eapply (eq_context_upto_cat _ _ _ Γ _ Γ) in eq. 2:reflexivity.
  eapply (eq_context_upto_ws_cumul_ctx_pb (pb:=Conv)) in eq. 2-3:fvs.
  now symmetry.
Qed.

Lemma into_red_terms {Σ Γ ts ts'} :
  All2 (red Σ Γ) ts ts' ->
  is_closed_context Γ ->
  forallb (is_open_term Γ) ts ->
  red_terms Σ Γ ts ts'.
Proof.
  induction 1; [constructor|].
  move=> /= clΓ /andP[clx cll]. constructor; eauto using into_closed_red.
Qed.

Lemma alpha_eq_context_gen Γ Δ :
  eq_context_upto_names Γ Δ ->
  eq_context_gen eq eq Γ Δ.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma untyped_subslet_ass {Γ s Δ} :
  assumption_context Δ ->
  #|s| = context_assumptions Δ ->
  untyped_subslet Γ s Δ.
Proof.
  induction Δ as [|[na [b|] ty] Δ] in s |- *; destruct s; simpl; try discriminate.
  - constructor.
  - intros h; elimtype False; inv h.
  - intros h; elimtype False; inv h.
  - intros h [=]. constructor. apply IHΔ => //.
    now inv h.
Qed.

Lemma shiftnP_up n m : n <= m -> forall i, shiftnP n xpred0 i -> shiftnP m xpred0 i.
Proof.
  intros lt i; rewrite /shiftnP !orb_false_r.
  move/Nat.ltb_lt => H; apply Nat.ltb_lt. lia.
Qed.

Lemma inst_case_ws_cumul_ctx_pb {cf Σ} {wfΣ : wf Σ} {ind mdecl idecl Γ pars pars' puinst puinst' ctx ctx'} :
  declared_inductive Σ ind mdecl idecl ->
  #|pars| = ind_npars mdecl ->
  #|pars'| = ind_npars mdecl ->
  on_free_vars_ctx (closedP #|pars| xpredT) ctx ->
  on_free_vars_ctx (closedP #|pars'| xpredT) ctx' ->
  is_closed_context Γ ->
  ws_cumul_pb_terms Σ Γ pars pars' ->
  R_universe_instance (eq_universe Σ) puinst puinst' ->
  eq_context_gen eq eq ctx ctx' ->
  Σ ⊢ Γ,,, inst_case_context pars puinst ctx = Γ,,, inst_case_context pars' puinst' ctx'.
Proof.
  intros decli wfp wfp' onp onp' clΓ eqpars eqinst eqctx.
  rewrite /inst_case_context.
  eapply ws_cumul_ctx_pb_rel_app.
  have clpars : is_closed_context (Γ,,, smash_context [] (ind_params mdecl)).
  { rewrite on_free_vars_ctx_app clΓ /=.
    apply on_free_vars_ctx_smash => //.
    generalize (declared_inductive_closed_params decli).
    now move/(closed_ctx_on_free_vars (shiftnP #|Γ| xpred0)). }
  have lenpars : #|pars| = context_assumptions (ind_params mdecl).
  { rewrite -(declared_minductive_ind_npars decli).
    now rewrite wfp. }
  have asspars : assumption_context (smash_context [] (ind_params mdecl)).
  { eapply PCUICContexts.smash_context_assumption_context => //. constructor. }
  have lenpars' : #|pars| = context_assumptions (smash_context [] (ind_params mdecl)).
  { rewrite context_assumptions_smash_context /= //. }
  eapply (substitution_ws_cumul_ctx_pb_subst_conv (Γ'':=[])
    (Γ' := smash_context [] mdecl.(ind_params))
    (Γ'0 := smash_context [] mdecl.(ind_params))) => //.
  * eapply (PCUICSpine.ws_cumul_ctx_pb_rel_trans (Δ' := ctx'@[puinst])).
    - eapply ws_cumul_ctx_pb_rel_app.
      eapply eq_context_upto_ws_cumul_ctx_pb.
      { rewrite on_free_vars_ctx_app clpars /=. len.
        rewrite on_free_vars_ctx_subst_instance -lenpars.
        eapply on_free_vars_ctx_impl; tea. apply shiftnP_up. lia. }
      { rewrite on_free_vars_ctx_app clpars /=. len.
        rewrite on_free_vars_ctx_subst_instance -lenpars.
        eapply on_free_vars_ctx_impl; tea. apply shiftnP_up. lia. }
      eapply eq_context_upto_cat; [reflexivity|].
      eapply eq_context_upto_univ_subst_instance'; tc. 1:reflexivity.
      assumption.
    - cbn.
      eapply subst_instance_ws_cumul_ctx_pb_rel => //.
      rewrite !on_free_vars_ctx_app clΓ /=. len.
      apply /andP; split.
      { apply on_free_vars_ctx_smash => //.
        generalize (declared_inductive_closed_params decli).
        now move/(closed_ctx_on_free_vars (shiftnP #|Γ| xpred0)). }
      rewrite -(declared_minductive_ind_npars decli) -wfp'.
      eapply on_free_vars_ctx_impl; tea.
      intros i. rewrite closedP_shiftnP.
      eapply shiftnP_up. lia.
  * now eapply All2_rev.
  * apply (untyped_subslet_ass asspars). now len.
  * apply (untyped_subslet_ass asspars). now len.
Qed.

#[global] Hint Resolve sq : core.

Lemma conv_cum_alt {cf:checker_flags} {leq} {Σ : global_env_ext} {Γ t t'} (wfΣ : ∥ wf Σ ∥) :
  conv_cum leq Σ Γ t t' <->
  ∥∑ v v', [× Σ ;;; Γ ⊢ t ⇝ v, Σ ;;; Γ ⊢ t' ⇝ v' & eq_termp leq Σ v v']∥.
Proof.
  destruct wfΣ.
  assert (forall P Q, (P <~> Q) -> (∥P∥ <-> ∥Q∥)) by
      (intros P Q H; split; intros [p]; constructor; apply H in p; auto).
  destruct leq; cbn; apply H.
  * eapply (ws_cumul_pb_alt_closed (pb:=Conv)).
  * eapply (ws_cumul_pb_alt_closed (pb:=Cumul)).
Qed.

Lemma conv_conv_cum_l {cf:checker_flags} :
  forall (Σ : global_env_ext) leq Γ u v,
      Σ ;;; Γ ⊢ u = v ->
      conv_cum leq Σ Γ u v.
Proof.
  intros Σ [] Γ u v h.
  - cbn. constructor. assumption.
  - cbn. constructor. now apply ws_cumul_pb_eq_le.
Qed.

Lemma conv_conv_cum_r {cf:checker_flags} :
  forall (Σ : global_env_ext) leq Γ u v,
      Σ ;;; Γ ⊢ u = v ->
      conv_cum leq Σ Γ v u.
Proof.
  intros Σ [] Γ u v h.
  - cbn. constructor. now symmetry.
  - cbn. constructor. apply ws_cumul_pb_eq_le.
    now symmetry.
Qed.

Definition closed_red_red {Σ Γ T U} : Σ ;;; Γ ⊢ T ⇝ U -> red Σ Γ T U := clrel_rel.
Coercion closed_red_red : closed_red >-> red.

Section fixed.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (wfΣ : ∥ wf Σ ∥).

  Definition isIndConstructApp (t : term) : bool :=
    match (decompose_app t).1 with
    | tInd _ _
    | tConstruct _ _ _ => true
    | _ => false
    end.

  Lemma isIndConstructApp_mkApps hd args :
    isIndConstructApp (mkApps hd args) = isIndConstructApp hd.
  Proof using Type.
    unfold isIndConstructApp.
    destruct (mkApps_elim hd args).
    rewrite !decompose_app_mkApps; by easy.
  Qed.

  Lemma eq_term_upto_univ_napp_nonind Re Rle napp t t' :
    eq_term_upto_univ_napp Σ Re Rle napp t t' ->
    isIndConstructApp t = false ->
    eq_term_upto_univ Σ Re Rle t t'.
  Proof using Type.
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
  Proof using Type.
    intros r.
    induction r; auto.
    rewrite (isIndConstructApp_mkApps _ [arg']) (isIndConstructApp_mkApps _ [arg]).
    apply IHr.
  Qed.

  Lemma eq_termp_mkApps_inv leq v args v' args' :
    isApp v = false ->
    isApp v' = false ->
    eq_termp leq Σ (mkApps v args) (mkApps v' args') ->
    eq_termp_napp leq Σ #|args| v v' × All2 (fun x y => eq_term Σ Σ x y) args args'.
  Proof using Type.
    intros noapp1 noapp2 eq.
    apply eq_term_upto_univ_mkApps_inv in eq as (?&?) => //.
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
    ∥conv_cum_napp leq Γ #|args| hd hd' × ws_cumul_pb_terms Σ Γ args args'∥.
  Proof using wfΣ.
    intros conv notapp notapp' wh wh'.
    eapply conv_cum_alt in conv as [(?&?&[r1 r2 e])]; auto.
    sq.
    pose proof (whnf_red_inv _ _ _ _ wh r1) as w1.
    apply whnf_red_mkApps_l_inv in w1 as (?&?&->&?&?); auto.
    pose proof (whnf_red_inv _ _ _ _ wh' r2) as w2.
    apply whnf_red_mkApps_l_inv in w2 as (?&?&->&?&?); auto.
    apply whnf_red_isApp in w as ?.
    apply whnf_red_isApp in w0 as ?.
    apply eq_termp_mkApps_inv in e as (?&?); try congruence.
    have clΓ : is_closed_context Γ by fvs.
    have [clhd clargs] : is_open_term Γ hd /\ forallb (is_open_term Γ) args.
    { move/clrel_src: r1. now rewrite on_free_vars_mkApps => /andP. }
    have [clhd' clargs'] : is_open_term Γ hd' /\ forallb (is_open_term Γ) args'.
    { move/clrel_src: r2. now rewrite on_free_vars_mkApps => /andP. }
    split.
    - apply whnf_red_isIndConstructApp in w as ?.
      destruct hd.
      all: cbn.
      1-9, 12-15: apply conv_cum_alt; eauto.
      1-13: constructor.
      1-13: exists x1, x.
      1-13: split; eauto with pcuic.
      1-13: (eapply eq_term_upto_univ_napp_nonind; [exact e|try exact H1]).
      1-13: cbn in *; congruence.
      all: depelim w; subst.
      all: depelim e.
      all: depelim w0; subst.
      all: apply All2_length in a.
      all: try (constructor; constructor; rewrite a; auto).
      all: destruct leq; cbn; repeat constructor => //.
    - eapply alt_into_ws_cumul_pb_terms => //.
      clear -a1 a a0.
      induction a1 in args, args', x2, a, x3, a0, a1 |- *; depelim a; depelim a0; [now constructor|].
      constructor.
      + apply conv_alt_red.
        now exists x, y.
      + now apply IHa1.
  Qed.

  Lemma conv_cum_tCase_inv leq Γ ci p discr brs ci' p' discr' brs' mdecl idecl mdecl' idecl' :
    conv_cum leq Σ Γ (tCase ci p discr brs) (tCase ci' p' discr' brs') ->
    declared_inductive Σ ci mdecl idecl ->
    declared_inductive Σ ci' mdecl' idecl' ->
    wf_predicate mdecl idecl p ->
    wf_predicate mdecl' idecl' p' ->
    whnf RedFlags.default Σ Γ (tCase ci p discr brs) ->
    whnf RedFlags.default Σ Γ (tCase ci' p' discr' brs') ->
    ∥ [× ci = ci',
      ws_cumul_pb_predicate Σ Γ p p',
      Σ;;; Γ ⊢ discr = discr' &
      ws_cumul_pb_brs Σ Γ p brs brs']∥.
  Proof using wfΣ.
    intros conv decli decli' wfp wfp' whl whr.
    depelim whl; solve_discr.
    depelim w; solve_discr; try discriminate.
    depelim whr; solve_discr.
    depelim w0; solve_discr; try discriminate.
    apply conv_cum_alt in conv as [(?&?&[r1 r2 eq])]; auto.
    have clΓ : is_closed_context Γ by fvs.
    set(l := tCase ci _ _ _) in *.
    set(r := tCase ci' _ _ _) in *.
    have cll : is_open_term Γ l.
    { now move/clrel_src: r1. }
    have clr : is_open_term Γ r.
    { now move/clrel_src: r2. }
    sq.
    subst l r; eapply whnf_red_inv in r1; eauto.
    eapply whnf_red_inv in r2; eauto.
    depelim r1.
    depelim r2.
    depelim eq.
    set (pl := {| pparams := motivepars |}) in *.
    set (pr := {| pparams := motivepars0 |}) in *.
    specialize e as (?&?&?&?).
    destruct (declared_inductive_inj decli decli') as [-> ->].
    repeat inv_on_free_vars.
    have clred : red_terms Σ Γ (pparams p) motivepars.
    { eapply into_red_terms; tea. }
    have clred' : red_terms Σ Γ (pparams p') motivepars0.
    { eapply into_red_terms; tea. }
    have eqpars : ws_cumul_pb_terms Σ Γ (pparams p) (pparams p').
    { etransitivity => //.
      { eapply red_terms_ws_cumul_pb_terms; tea. }
      transitivity motivepars0.
      { eapply eq_terms_ws_cumul_pb_terms; fvs.
        * eapply closed_red_terms_open_right in clred; solve_all.
        * eapply closed_red_terms_open_right in clred'; solve_all. }
      symmetry. eapply red_terms_ws_cumul_pb_terms. eapply into_red_terms; tea. }
    have eq_instctx : Σ ⊢ Γ,,, inst_case_predicate_context p = Γ,,, inst_case_predicate_context p'.
    { eapply (inst_case_ws_cumul_ctx_pb decli); tea.
      { apply (wf_predicate_length_pars wfp). }
      { apply (wf_predicate_length_pars wfp'). } }
    repeat split; eauto.
    - transitivity motiveret0.
      { eapply ws_cumul_pb_alt_closed. exists motiveret, motiveret0.
        split; auto.
        * split; auto.
          + rewrite on_free_vars_ctx_app. apply /andP. split; auto.
            eapply on_free_vars_ctx_inst_case_context; tea => //.
            rewrite test_context_k_closed_on_free_vars_ctx //.
          + len. now setoid_rewrite shiftnP_add in p6.
        * eapply closed_red_refl.
          + rewrite on_free_vars_ctx_app. apply /andP. split; auto.
            eapply on_free_vars_ctx_inst_case_context; tea => //.
            now rewrite test_context_k_closed_on_free_vars_ctx.
          + eapply red_on_free_vars in r1; tea.
            { len. rewrite (All2_fold_length a5).
              now setoid_rewrite shiftnP_add in p1. }
            len. rewrite -shiftnP_add (All2_fold_length a5).
            eapply on_ctx_free_vars_inst_case_context; auto.
            1:now rewrite test_context_k_closed_on_free_vars_ctx.
            now erewrite -> on_free_vars_ctx_on_ctx_free_vars. }
      eapply (ws_cumul_pb_ws_cumul_ctx (Γ := Γ ,,, inst_case_predicate_context p') (pb':=Conv)) => //.
      symmetry. eapply red_ws_cumul_pb.
      eapply into_closed_red; eauto. 1:fvs.
      len. now setoid_rewrite shiftnP_add in p1.
    - apply ws_cumul_pb_alt_closed; eauto.
      exists discr'0, discr'1. split; eauto.
      all:eapply into_closed_red; eauto.
    - rename a0 into brsa1.
      rename a2 into brsa2.
      rename a3 into brseq.
      clear -wfΣ decli brsa1 brsa2 brseq clΓ wfp wfp' a a1 p0 p5 p4 p9 r3 eqpars.
      induction brseq in brs, brs', brsa1, brsa2, p4, p9 |- *;
        depelim brsa1; depelim brsa2; [constructor|].
      destruct p0, p1, r.
      cbn in p4, p9. move/andP: p4 => [fv p4].
      move/andP: p9 => [fv' p9].
      constructor.
      2: { apply IHbrseq; auto. }
      have eqctx : Σ ⊢ Γ ,,, inst_case_branch_context p x0 = Γ ,,, inst_case_branch_context p' x1.
      { rewrite /inst_case_branch_context.
        eapply (inst_case_ws_cumul_ctx_pb decli); tea.
        { apply (wf_predicate_length_pars wfp). }
        { apply (wf_predicate_length_pars wfp'). }
        { rewrite -test_context_k_closed_on_free_vars_ctx //.
          now move/andP: fv'. }
        { rewrite -test_context_k_closed_on_free_vars_ctx; now move/andP: fv. }
        now rewrite e e0. }
      rewrite e e0; split => //.
      transitivity (bbody x); tea.
      { eapply red_ws_cumul_pb. rewrite /inst_case_branch_context. split; auto.
        1:now eapply ws_cumul_ctx_pb_closed_left in eqctx.
        move/andP: fv' => []. now len; rewrite shiftnP_add. }
      transitivity (bbody y); tea.
      { constructor; auto. 1:now eapply ws_cumul_ctx_pb_closed_left.
        { eapply closed_red_open_right. eapply into_closed_red; tea.
          { now eapply ws_cumul_ctx_pb_closed_left. }
          move/andP: fv' => []. len. now setoid_rewrite shiftnP_add. }
        move/andP: fv => [] fv fvx1. len.
        eapply red_on_free_vars in fvx1; tea.
        { rewrite e (All2_fold_length a0) -e0. now setoid_rewrite shiftnP_add in fvx1. }
        rewrite shiftnP_add. relativize (#|bcontext x1| + _).
        1:rewrite -> on_free_vars_ctx_on_ctx_free_vars. 2:now len.
        now eapply ws_cumul_ctx_pb_closed_right in eqctx. }
      symmetry.
      eapply ws_cumul_pb_ws_cumul_ctx; tea.
      eapply red_ws_cumul_pb. rewrite /inst_case_branch_context. split; auto.
      1:now eapply ws_cumul_ctx_pb_closed_right in eqctx.
      move/andP: fv => []. len. now rewrite shiftnP_add.
  Qed.

  Lemma conv_cum_tFix_inv leq Γ mfix idx mfix' idx' :
    conv_cum leq Σ Γ (tFix mfix idx) (tFix mfix' idx') ->
    ∥idx = idx' ×
     All2 (fun d d' =>
      [× rarg d = rarg d',
         eq_binder_annot d.(dname) d'.(dname),
         Σ;;; Γ ⊢ dtype d = dtype d' &
         Σ;;; Γ,,, fix_context mfix ⊢ dbody d = dbody d'])
          mfix mfix'∥.
  Proof using wfΣ.
    intros conv.
    apply conv_cum_alt in conv as [(?&?&[r1 r2 eq])]; auto.
    sq.
    assert (forall defs i, whnf RedFlags.default Σ Γ (tFix defs i)).
    { intros defs i.
      apply whnf_fixapp with (v := []).
      destruct unfold_fix as [(?&?)|]; [|easy].
      now rewrite nth_error_nil. }
    have clΓ := clrel_ctx r1.
    have cll := clrel_src r1.
    have clr := clrel_src r2.
    assert (clx := closed_red_open_right r1).
    assert (cly := closed_red_open_right r2).
    eapply whnf_red_inv in r1; eauto.
    eapply whnf_red_inv in r2; eauto.
    depelim r1.
    depelim r2.
    depelim eq.
    split; [easy|].
    cbn in cll, clr, clx, cly.
    have clmfixctx : is_closed_context (Γ ,,, fix_context mfix).
    { rewrite on_free_vars_ctx_app clΓ /=. apply on_free_vars_fix_context; solve_all. }
    have clmfixctx' : is_closed_context (Γ ,,, fix_context mfix').
    { rewrite on_free_vars_ctx_app clΓ /=. apply on_free_vars_fix_context; solve_all. }
    solve_all.
    move: clmfixctx clmfixctx'.
    clear -wfΣ a a0 a1 clΓ.
    cut (#|mfix| = #|mfix'|);
      [|now apply All2_length in a; apply All2_length in a0; apply All2_length in a1].
    revert a a0 a1.
    generalize mfix at 1 2 4 5 6.
    generalize mfix' at 1 2 4 5.
    intros ctx_fix ctx_fix'.
    intros all1 all2 all len_eq.
    induction all in mfix, mfix', all1, all2, all |- *;
      depelim all1; depelim all2; subst; [constructor|].
    constructor; [|now auto].
    destruct r as ((?&(((? & ?) & ?)&?))&?), p as (?&?&?&?&?), p0 as (?&?&?&?&?).
    split; auto; try congruence.
    - eapply ws_cumul_pb_alt_closed; exists (dtype x), (dtype y). split; eauto.
      all:eapply into_closed_red; eauto.
      { now move/andP: i1. }
      { now move/andP: i2. }
    - eapply ws_cumul_pb_alt_closed.
      exists (dbody x), (dbody y).
      split; [| |easy].
      all:eapply into_closed_red; auto.
      * move/andP: i1 => []. now len; rewrite shiftnP_add.
      * eapply PCUICRedTypeIrrelevance.context_pres_let_bodies_red; eauto.
        eapply PCUICRedTypeIrrelevance.fix_context_pres_let_bodies; eauto.
      * move/andP: i2 => []. len. now rewrite len_eq shiftnP_add.
  Qed.

  Lemma conv_cum_tCoFix_inv leq Γ mfix idx mfix' idx' :
    conv_cum leq Σ Γ (tCoFix mfix idx) (tCoFix mfix' idx') ->
    ∥idx = idx' ×
    All2 (fun d d' =>
      [× rarg d = rarg d',
        eq_binder_annot d.(dname) d'.(dname),
        Σ;;; Γ ⊢ dtype d = dtype d' &
        Σ;;; Γ,,, fix_context mfix ⊢ dbody d = dbody d'])
          mfix mfix'∥.
  Proof using wfΣ.
    intros conv.
    apply conv_cum_alt in conv as [(?&?&[r1 r2 eq])]; auto. sq.
    assert (forall defs i, whnf RedFlags.default Σ Γ (tCoFix defs i)).
    { intros defs i.
      apply whnf_cofixapp with (v := []). }
    have clΓ := clrel_ctx r1.
    have cll := clrel_src r1.
    have clr := clrel_src r2.
    assert (clx := closed_red_open_right r1).
    assert (cly := closed_red_open_right r2).
    eapply whnf_red_inv in r1; eauto.
    eapply whnf_red_inv in r2; eauto.
    depelim r1.
    depelim r2.
    depelim eq.
    split; [easy|].
    cbn in cll, clr, clx, cly.
    have clmfixctx : is_closed_context (Γ ,,, fix_context mfix).
    { rewrite on_free_vars_ctx_app clΓ /=. apply on_free_vars_fix_context; solve_all. }
    have clmfixctx' : is_closed_context (Γ ,,, fix_context mfix').
    { rewrite on_free_vars_ctx_app clΓ /=. apply on_free_vars_fix_context; solve_all. }
    solve_all.
    move: clmfixctx clmfixctx'.
    clear -wfΣ a a0 a1 clΓ.
    cut (#|mfix| = #|mfix'|);
      [|now apply All2_length in a; apply All2_length in a0; apply All2_length in a1].
    revert a a0 a1.
    generalize mfix at 1 2 4 5 6.
    generalize mfix' at 1 2 4 5.
    intros ctx_fix ctx_fix'.
    intros all1 all2 all len_eq.
    induction all in mfix, mfix', all1, all2, all |- *;
      depelim all1; depelim all2; subst; [constructor|].
    constructor; [|now auto].
    destruct r as ((?&(((? & ?) & ?)&?))&?), p as (?&?&?&?&?), p0 as (?&?&?&?&?).
    split; auto; try congruence.
    - eapply ws_cumul_pb_alt_closed; exists (dtype x), (dtype y). split; eauto.
      all:eapply into_closed_red; eauto.
      { now move/andP: i1. }
      { now move/andP: i2. }
    - eapply ws_cumul_pb_alt_closed.
      exists (dbody x), (dbody y).
      split; [| |easy].
      all:eapply into_closed_red; auto.
      * move/andP: i1 => []. now len; rewrite shiftnP_add.
      * eapply PCUICRedTypeIrrelevance.context_pres_let_bodies_red; eauto.
        eapply PCUICRedTypeIrrelevance.fix_context_pres_let_bodies; eauto.
      * move/andP: i2 => []. len. now rewrite len_eq shiftnP_add.
  Qed.

  Lemma conv_cum_tProj_inv leq Γ p c p' c' :
    conv_cum leq Σ Γ (tProj p c) (tProj p' c') ->
    whnf RedFlags.default Σ Γ (tProj p c) ->
    whnf RedFlags.default Σ Γ (tProj p' c') ->
    ∥ p = p' × Σ;;; Γ ⊢ c = c' ∥.
  Proof using wfΣ.
    intros conv whl whr.
    apply conv_cum_alt in conv as [(?&?&[r1 r2 ?])]; auto. sq.
    have clΓ := clrel_ctx r1.
    have cll := clrel_src r1.
    have clr := clrel_src r2.
    eapply whnf_red_inv in r1; eauto.
    eapply whnf_red_inv in r2; eauto.
    depelim r1.
    depelim r2.
    depelim c0.
    split; [easy|].
    apply ws_cumul_pb_alt_closed; eauto.
    exists c'0, c'1; split; eauto.
    all:eapply into_closed_red; eauto.
  Qed.

End fixed.
