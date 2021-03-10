(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICTyping PCUICWeakening PCUICCases
     PCUICCumulativity PCUICReduction
     PCUICParallelReduction PCUICEquality PCUICUnivSubstitution
     PCUICParallelReductionConfluence PCUICConfluence
     PCUICContextReduction PCUICOnFreeVars.

From MetaCoq.PCUIC Require Export PCUICContextRelation.

From Coq Require Import CRelationClasses ssreflect.
From Equations Require Import Equations.

Arguments red_ctx : clear implicits.

Ltac my_rename_hyp h th :=
  match th with
    | (typing _ _ ?t _) => fresh "type" t
    | (All_local_env (@typing _) _ ?G) => fresh "wf" G
    | (All_local_env (@typing _) _ _) => fresh "wf"
    | (All_local_env _ _ ?G) => fresh "H" G
    | context [typing _ _ (_ ?t) _] => fresh "IH" t
  end.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Hint Resolve conv_refl' : pcuic.
Arguments skipn : simpl never.

Ltac inv_on_free_vars :=
  repeat match goal with
  | [ H : is_true (on_free_vars_decl _ _) |- _ ] => progress cbn in H
  | [ H : is_true (_ && _) |- _ ] => 
    move/andP: H => []; intros
  | [ H : is_true (on_free_vars ?P ?t) |- _ ] => 
    progress (cbn in H || rewrite on_free_vars_mkApps in H);
    (move/and5P: H => [] || move/and4P: H => [] || move/and3P: H => [] || move/andP: H => [] || 
      eapply forallb_All in H); intros
  | [ H : is_true (test_def (on_free_vars ?P) ?Q ?x) |- _ ] =>
    move/andP: H => []; rewrite ?shiftnP_xpredT; intros
  | [ H : is_true (test_context_k _ _ _ ) |- _ ] =>
    rewrite -> test_context_k_closed_on_free_vars_ctx in H
  end.

Notation byfvs := (ltac:(cbn; eauto with fvs)) (only parsing).

(* TODO move *)
(* Lemma weakening_cumul0 {cf:checker_flags} Σ Γ Γ'' M N n :
  wf Σ.1 -> n = #|Γ''| ->
  Σ ;;; Γ |- M <= N ->
  Σ ;;; Γ ,,, Γ'' |- lift0 n M <= lift0 n N.
Proof. intros; subst. apply (weakening_cumul (Γ':= [])); tea. Qed. *)

Hint Constructors red1 : pcuic.
Hint Resolve refl_red : pcuic.

Section ContextReduction.
  Context {cf : checker_flags}.
  Context (Σ : global_env).
  Context (wfΣ : wf Σ).

  Local Definition red1_red_ctxP Γ Γ' :=
    (forall n b b',
        option_map decl_body (nth_error Γ n) = Some (Some b) ->
        option_map decl_body (nth_error Γ' n) = Some (Some b') ->
        @red_ctx Σ (skipn (S n) Γ) (skipn (S n) Γ') ->
        ∑ t, red Σ (skipn (S n) Γ') b t * red Σ (skipn (S n) Γ') b' t).

  Lemma red_ctx_skip i Γ Γ' :
    red1_red_ctxP Γ Γ' ->
    red1_red_ctxP (skipn i Γ) (skipn i Γ').
  Proof.
    rewrite /red1_red_ctxP => H n b b'.
    rewrite !nth_error_skipn => H0 H1.
    specialize (H (i + n)).
    rewrite !skipn_skipn. rewrite - !Nat.add_succ_comm.
    move=> H'.
    eapply H; auto.
  Qed.

  Lemma All2_fold_over_red_refl {Γ Δ} :
    All2_fold (on_decls (fun (Δ _ : context) (t u : term) => red Σ (Γ ,,, Δ) t u)) Δ Δ.
  Proof. induction Δ as [|[na [b|] ty]]; econstructor; try red; auto. 
    constructor; reflexivity. constructor; reflexivity.
  Qed.

  Lemma All2_fold_red_refl {Δ} :
    All2_fold (on_decls (fun (Δ _ : context) (t u : term) => red Σ Δ t u)) Δ Δ.
  Proof. 
    induction Δ as [|[na [b|] ty]]; econstructor; try red; auto;
    constructor; reflexivity.
  Qed.

  Derive Signature for assumption_context.

  Lemma red1_red_ctxP_app {Γ Γ' Δ} : 
    red1_red_ctxP Γ Γ' ->
    red1_red_ctxP (Γ ,,, Δ) (Γ' ,,, Δ).
  Proof.
    induction Δ as [|[na [b|] ty] Δ]; intros; auto.
    - case.
      * move=> bod bod' => /= [=] -> [=] ->. rewrite !skipn_S !skipn_0. exists bod'.
        split; reflexivity.
      * move=> /= n bod b' hn hn' r.
        specialize (IHΔ X n bod b' hn hn' r) as [t [redl redr]].
        exists t. rewrite !skipn_S in r |- *. split; auto.
    - case; move => n b b' //. eapply IHΔ. apply X.
  Qed.

  Ltac t := split; [eapply red1_red; try econstructor; eauto|try constructor]; eauto with pcuic.
  Ltac u := intuition eauto with pcuic.

  Lemma red_ctx_app Γ Γ' Δ : 
    red_ctx Σ Γ Γ' -> red_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ).
  Proof.
    intros h; eapply All2_fold_app => //.
    eapply All2_fold_refl. reflexivity.
  Qed.
  Hint Resolve red_ctx_app : pcuic.
  Import ssrbool.

  Lemma red_ctx_on_free_vars P Γ Γ' :
    red_ctx Σ Γ Γ' ->
    on_free_vars_ctx P Γ ->
    on_free_vars_ctx P Γ'.
  Proof.
    move=> /red_ctx_red_context r onΓ.
    pose proof (All2_fold_length r).
    move: r => /red_context_on_ctx_free_vars.
    move: onΓ. now rewrite - !on_free_vars_ctx_on_ctx_free_vars -H.
  Qed.

  Lemma red1_red_ctx_aux {Γ Γ' T U} :
    red1 Σ Γ T U ->
    on_free_vars xpredT T ->
    on_free_vars_ctx xpredT Γ ->
    @red_ctx Σ Γ Γ' ->
    red1_red_ctxP Γ Γ' ->
    ∑ t, red Σ Γ' T t * red Σ Γ' U t.
  Proof.
    intros r onT onΓ H. revert onT onΓ Γ' H.
    simpl in *. induction r using red1_ind_all; intros; auto with pcuic; 
    repeat inv_on_free_vars_xpredT.
    all:try solve [eexists; t].
    all:try specialize (IHr ltac:(tea) ltac:(eauto with fvs)).
    all:try destruct (IHr _ ltac:(tea) ltac:(tea)) as [? [? ?]]; auto.

    - pose proof H.
      eapply nth_error_pred1_ctx_l in H as [body' [? ?]]; eauto.
      rewrite -(firstn_skipn (S i) Γ').
      assert (i < #|Γ'|). destruct (nth_error Γ' i) eqn:Heq; noconf e. eapply nth_error_Some_length in Heq. lia.
      move: (All2_fold_length H0) => Hlen.
      specialize (X _ _ _ H1 e). forward X. eapply All2_fold_app_inv.
      instantiate (1 := firstn (S i) Γ').
      instantiate (1 := firstn (S i) Γ).
      rewrite !firstn_length. lia.
      rewrite [_ ,,, _](firstn_skipn (S i) _).
      now rewrite [_ ,,, _](firstn_skipn (S i) _).
      destruct X as [x' [bt b't]]. exists (lift0 (S i) x').
      split; eauto with pcuic.
      * etransitivity. eapply red1_red. constructor.
        rewrite firstn_skipn. eauto. cbn in *.
        eapply red_ctx_on_free_vars in onΓ. 2:tea.
        eapply weakening_red_0; eauto.
        rewrite firstn_length_le //.
        erewrite on_free_vars_ctx_on_ctx_free_vars.
        rewrite -(firstn_skipn (S i) Γ') on_free_vars_ctx_app in onΓ.
        now move/andP: onΓ => [].
        destruct (nth_error Γ' i) eqn:hnth => //.
        epose proof (nth_error_on_free_vars_ctx xpredT 0 Γ' i c).
        forward H2. rewrite addnP0. eauto with fvs.
        forward H2 by auto.
        specialize (H2 hnth). noconf e.
        move/andP: H3 => [] /=. rewrite H /=.
        rewrite PCUICInst.addnP_xpredT shiftnP_xpredT //.
      * epose proof (red_ctx_on_free_vars _ _ _ H0 onΓ).
        eapply weakening_red_0; eauto.
        rewrite firstn_length_le //.
        erewrite on_free_vars_ctx_on_ctx_free_vars.
        rewrite -(firstn_skipn (S i) Γ') on_free_vars_ctx_app in H2.
        now move/andP: H2 => [].
        destruct (nth_error Γ i) eqn:hnth => //.
        epose proof (nth_error_on_free_vars_ctx xpredT 0 Γ i c).
        forward H3. rewrite addnP0. eauto with fvs.
        forward H3 by auto.
        specialize (H3 hnth). noconf H1.
        move/andP: H3 => [] /=. rewrite H /=.
        eauto with fvs.

    - exists (tLambda na x N). split; apply red_abs; auto.

    - destruct (IHr (Γ' ,, vass na N)). constructor; pcuic. constructor; pcuic.
      case => ? ? /= //. apply X.
      exists (tLambda na N x). split; apply red_abs; u.

    - exists (tLetIn na x t b'). split; eapply red_letin; auto.
    - specialize (IHr (Γ' ,, vdef na b t)).
      forward IHr. constructor; eauto. constructor; auto.
      destruct IHr as [? [? ?]].
      case. move=> b0 b1 [] <- [] <- H'. exists b; auto.
      apply X.
      exists (tLetIn na b t x). split; eapply red_letin; auto.
    - solve_all. eapply OnOne2_All_mix_left in X; tea.
      eapply (OnOne2_exist _ (red Σ Γ')) in X as [pars' [ol or]].
      exists (tCase ci (set_pparams p pars') c brs). u.
      apply red_case_pars. eapply OnOne2_All2; tea => /= //.
      change (set_pparams p pars') with (set_pparams (set_pparams p params') pars').
      apply red_case_pars => /=. eapply OnOne2_All2; tea => /= //.
      intros; u.
    (* - eapply (OnOne2_local_env_exist' _ (fun Δ => red Σ (Γ' ,,, Δ)) (fun Δ => red Σ (Γ' ,,, Δ))) in X as [pars' [ol or]].
      exists (tCase ci (set_pcontext p pars') c brs). u.
      apply red_case_pcontext => //.
      change (set_pcontext p pars') with (set_pcontext (set_pcontext p pcontext') pars').
      apply red_case_pcontext => /= //.
      move=> /= Δ x y IH. apply (IH (Γ' ,,, Δ)).
      { eapply All2_fold_app => //. eapply All2_fold_refl; reflexivity. }
      { now apply red1_red_ctxP_app. } *)
    - destruct (IHr (Γ' ,,, inst_case_predicate_context p)).
      now eapply red_ctx_app => //.
      now eapply red1_red_ctxP_app.
      destruct p5.
      eexists. split. eapply red_case_p; tea.
      change (set_preturn p x) with (set_preturn (set_preturn p preturn') x).
      eapply red_case_p; tea.
    - exists (tCase ind p x brs). u; now apply red_case_c.
    - solve_all. eapply OnOne2_All_mix_left in X; tea.
      eapply (OnOne2_exist _ 
        (fun br br' => on_Trel_eq (red Σ (Γ' ,,, inst_case_branch_context p br)) bbody bcontext br br')) in X.
        destruct X as [brs'' [? ?]].
        eexists. split; eapply red_case_one_brs; eauto;
        solve_all.
        intros. intuition eauto.
        inv_on_free_vars_xpredT.
        specialize (b1 ltac:(eauto with fvs)).
        forward b1. eapply on_free_vars_ctx_inst_case_context_xpredT; eauto with fvs. solve_all.
        now rewrite test_context_k_closed_on_free_vars_ctx in a0.
        specialize (b1 (Γ' ,,, inst_case_branch_context p y)) as [body' [rl rr]].
        + rewrite /inst_case_branch_context -b0. now eapply red_ctx_app => //.
        + rewrite /inst_case_branch_context -b0. now eapply red1_red_ctxP_app.
        + exists {| bcontext := bcontext x; bbody := body' |}; cbn; split; rewrite -?b;
          intuition eauto.
          rewrite /inst_case_branch_context b0 //.
    - exists (tProj p x). u; now eapply red_proj_c.
    - exists (tApp x M2). u; now eapply red_app.
    - exists (tApp M1 x). u; now eapply red_app.
    - exists (tProd na x M2). u; now eapply red_prod.
    - specialize (IHr (Γ' ,, vass na M1)) as [? [? ?]].
      constructor; pcuic. constructor; auto. case => //.
      exists (tProd na M1 x). u; now eapply red_prod.
    - eapply OnOne2_All_mix_left in X; tea.
      eapply (OnOne2_exist _ (red Σ Γ')) in X.
      destruct X as [rl [l0 l1]].
      eexists; split; eapply red_evar; eauto.
      eapply OnOne2_All2; eauto.
      eapply OnOne2_All2; eauto.
      simpl; intros.
      intuition eauto.
    - eapply OnOne2_All_mix_left in X; tea.
       eapply (OnOne2_exist _ (on_Trel_eq (red Σ Γ') dtype (fun x => (dname x, dbody x, rarg x)))) in X.
      destruct X as [mfix' [l r]].
      exists (tFix mfix' idx); split; eapply red_fix_ty.
      eapply OnOne2_All2; intuition eauto; intuition.
      eapply OnOne2_All2; intuition eauto; intuition.
      intuition auto. inv_on_free_vars_xpredT.
      specialize (b1 a0 onΓ).
      destruct (b1 _ H X0) as [d' [r0 r1]].
      refine (existT _ {| dtype := d' |} _); simpl; eauto.
    - assert (fix_context mfix0 = fix_context mfix1).
      { rewrite /fix_context /mapi. generalize 0 at 2 4.
        induction X. destruct p. simpl. intuition congruence.
        intros. specialize (IHX (S n)). simpl. congruence. }
      eapply OnOne2_All_mix_left in X; tea.
      eapply (OnOne2_exist _ (on_Trel_eq (red Σ (Γ' ,,, fix_context mfix0)) dbody (fun x => (dname x, dtype x, rarg x)))) in X.
      destruct X as [mfix' [l r]].
      exists (tFix mfix' idx); split; eapply red_fix_body.
      eapply OnOne2_All2; intuition eauto; intuition.
      eapply OnOne2_All2; intuition eauto; intuition. congruence.
      intros.
      intuition auto. inv_on_free_vars_xpredT.
      specialize (b1 ltac:(eauto with fvs) ltac:(eauto with fvs) (Γ' ,,, fix_context mfix0)). forward b1.
      eapply All2_fold_app => //. apply All2_fold_over_red_refl.
      forward b1. now eapply red1_red_ctxP_app.
      destruct b1 as [t [? ?]].
      refine (existT _ {| dbody := t |} _); simpl; eauto.
    - eapply OnOne2_All_mix_left in X; tea.
      eapply (OnOne2_exist _ (on_Trel_eq (red Σ Γ') dtype (fun x => (dname x, dbody x, rarg x)))) in X.
      destruct X as [mfix' [l r]].
      exists (tCoFix mfix' idx); split; eapply red_cofix_ty.
      eapply OnOne2_All2; intuition eauto; intuition.
      eapply OnOne2_All2; intuition eauto; intuition.
      intuition auto. inv_on_free_vars_xpredT.
      destruct (b1 byfvs byfvs _ H X0) as [d' [r0 r1]].
      refine (existT _ {| dtype := d' |} _); simpl; eauto.
    - assert (fix_context mfix0 = fix_context mfix1).
      { rewrite /fix_context /mapi. generalize 0 at 2 4.
        induction X. destruct p. simpl. intuition congruence.
        intros. specialize (IHX (S n)). simpl. congruence. }
      eapply OnOne2_All_mix_left in X; tea.
      eapply (OnOne2_exist _ (on_Trel_eq (red Σ (Γ' ,,, fix_context mfix0)) dbody (fun x => (dname x, dtype x, rarg x)))) in X.
      destruct X as [mfix' [l r]].
      exists (tCoFix mfix' idx); split; eapply red_cofix_body.
      eapply OnOne2_All2; intuition eauto; intuition.
      eapply OnOne2_All2; intuition eauto; intuition. congruence.
      intros. intuition auto. inv_on_free_vars_xpredT.
      specialize (b1 byfvs byfvs (Γ' ,,, fix_context mfix0)). forward b1.
      eapply All2_fold_app => //. apply All2_fold_over_red_refl.
      forward b1. eapply red1_red_ctxP_app => //.
      destruct b1 as [t [? ?]].
      refine (existT _ {| dbody := t |} _); simpl; eauto.
  Qed.

  Hint Resolve red_ctx_on_free_vars : fvs.

  Lemma red_red_ctx' {Γ : closed_context} Γ' {T : open_term Γ} {U} :
    red Σ Γ T U ->
    @red_ctx Σ Γ Γ' ->
    red1_red_ctxP Γ Γ' ->
    ∑ t, red Σ Γ' T t * red Σ Γ' U t.
  Proof.
    intros r rc rP. destruct T as [T hT]; cbn in *; induction r.
    - eapply red1_red_ctx_aux; eauto with fvs.
    - exists x; split; auto.
    - destruct IHr1 as [xl [redl redr]]; eauto with fvs.
      destruct IHr2 as [xr [redl' redr']]; eauto with fvs.
      assert (on_free_vars_ctx xpred0 Γ'). eapply red_ctx_on_free_vars; tea. eauto with fvs.
      pose proof (All2_fold_length rc).
      unshelve epose proof (red_confluence (Γ := exist Γ' _) (t := exist y _) redr redl'); cbn; eauto with fvs.
      rewrite -H0; eauto with fvs.
      destruct X as [v' [redxl redxr]].
      exists v'. split; [transitivity xl|transitivity xr]; auto.
  Qed.

  Lemma red_red_ctx_aux' {Γ : closed_context} {Γ'} :
    @red_ctx Σ Γ Γ' -> red1_red_ctxP Γ Γ'.
  Proof.
    destruct Γ as [Γ onΓ].
    intros X. cbn in *.
    induction Γ in Γ', X, onΓ |- *.
    - depelim X.
      intros n t t'. rewrite nth_error_nil //.
    - depelim X.
      move: onΓ; rewrite on_free_vars_ctx_snoc => /andP /= [onΓ ond].
      depelim a0.
      + specialize (IHΓ byfvs _ X).
        case => n b b' /= //.
        simpl. apply IHΓ.
      + specialize (IHΓ byfvs _ X).
        case.
        * move=> b0 b1 [] <- [] <- H.
          rewrite skipn_S /skipn /= in H.
          move/andP: ond => /= [] onb ont.
          eapply (@red_red_ctx' (exist Γ onΓ) _ (exist b onb)) in H; eauto.
        * simpl. eapply IHΓ.
  Qed.

  Lemma red_red_ctx {Γ : closed_context} {Γ'} {T : open_term Γ} {U} :
    red Σ Γ T U ->
    @red_ctx Σ Γ Γ' ->
    ∑ t, red Σ Γ' T t * red Σ Γ' U t.
  Proof.
    intros. eapply red_red_ctx', red_red_ctx_aux'; eauto.
  Qed.

End ContextReduction.


Import ssrbool.

Definition inj_closed (Γ : context) (o : on_free_vars_ctx xpred0 Γ) : closed_context :=
  exist Γ o.
Arguments inj_closed Γ & o.

Notation "⇑ Γ" := (inj_closed Γ byfvs) (at level 20).

Definition inj_open {Γ : closed_context} (t : term) (o : on_free_vars (shiftnP #|Γ| xpred0) t) : open_term Γ :=
  exist t o.
Arguments inj_open {Γ} & t o.
Notation "⤊ t" := (inj_open t byfvs) (at level 20).

Hint Resolve red_ctx_on_free_vars : fvs.

Lemma red_ctx_on_free_vars_term {Σ P Γ Γ' t} :
  red_ctx Σ Γ Γ' -> 
  on_free_vars (shiftnP #|Γ| P) t ->
  on_free_vars (shiftnP #|Γ'| P) t.
Proof.
  intros r. now rewrite (All2_fold_length r).
Qed.
Hint Resolve red_ctx_on_free_vars_term : fvs.

Section ContextConversion.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context {wfΣ : wf Σ}.

  Notation conv_context := (All2_fold (conv_decls Σ)).
  Notation cumul_context := (All2_fold (cumul_decls Σ)).

  Hint Resolve conv_ctx_refl' cumul_ctx_refl' : pcuic.

  Lemma fill_le {Γ : closed_context} {t u : open_term Γ} {t' u'} :
    leq_term Σ.1 Σ t u -> red Σ Γ t t' -> red Σ Γ u u' ->
    ∑ t'' u'', red Σ Γ t' t'' * red Σ Γ u' u'' * leq_term Σ Σ t'' u''.
  Proof.
    intros tu tt' uu'.
    eapply red_eq_term_upto_univ_l in tu; try exact tt'. all:try tc.
    destruct tu as [u'' [uu'' t'u'']].
    destruct (red_confluence uu' uu'') as [unf [ul ur]].
    eapply red_eq_term_upto_univ_r in t'u''; try exact ur; try tc.
    destruct t'u'' as [t'' [t't'' t''unf]].
    exists t'', unf. intuition auto.
  Qed.

  Lemma fill_eq {Γ : closed_context} {t u : open_term Γ} {t' u'} :
    eq_term Σ.1 Σ t u -> red Σ Γ t t' -> red Σ Γ u u' ->
    ∑ t'' u'', red Σ Γ t' t'' * red Σ Γ u' u'' * eq_term Σ.1 Σ t'' u''.
  Proof.
    intros tu tt' uu'.
    pose proof tu as tu2.
    eapply red_eq_term_upto_univ_l in tu; try exact tt'; try tc.
    destruct tu as [u'' [uu'' t'u'']].
    destruct (red_confluence uu' uu'') as [unf [ul ur]].
    eapply red_eq_term_upto_univ_r in t'u''; try exact ur; try tc.
    destruct t'u'' as [t'' [t't'' t''unf]].
    exists t'', unf. intuition auto.
  Qed.
  
  Lemma red_ctx_conv_context Γ Γ' :
    red_ctx Σ Γ Γ' ->
    conv_context Γ Γ'.
  Proof.
    intros r.
    induction r; constructor; auto.
    depelim p; constructor; auto.
    all: apply red_conv; auto.
  Qed.
  
  Lemma red_ctx_cumul_context Γ Γ' :
    red_ctx Σ Γ Γ' ->
    cumul_context Γ Γ'.
  Proof.
    intros r.
    induction r; constructor; auto.
    depelim p; constructor; auto.
    all: try apply red_cumul; try apply red_conv; auto.
  Qed.

  Lemma cumul_red_ctx {Γ : closed_context} Γ' {T U : open_term Γ} :
    Σ ;;; Γ |- T <= U ->
    red_ctx Σ Γ Γ' ->
    Σ ;;; Γ' |- T <= U.
  Proof.
    intros H Hctx.
    apply cumul_alt in H as [v [v' [[redl redr] leq]]].
    destruct (red_red_ctx Σ wfΣ redl Hctx) as [lnf [redl0 redr0]].
    apply cumul_alt.
    eapply red_eq_term_upto_univ_l in leq; tea; try tc.
    destruct leq as [? [? ?]].
    destruct (red_red_ctx _ wfΣ redr Hctx) as [rnf [redl1 redr1]].
    unshelve epose proof (red_confluence (Γ := inj_closed Γ' byfvs) (t := inj_open v' byfvs) r redr1) as [nf [redl' redr']].
    edestruct (red_eq_term_upto_univ_r Σ (eq_universe_leq_universe _) e redl') as [lnf' [? ?]].
    exists lnf', nf. intuition auto. now transitivity lnf.
    now transitivity rnf.
  Qed.

  Lemma red_red_ctx_inv {Γ Δ : closed_context} {t : open_term Γ} {u} :
    red Σ Γ t u -> red_ctx Σ Δ Γ -> red Σ Δ t u.
  Proof.
    intros r rc.
    eapply red_ctx_red_context in rc.
    eapply PCUICContextReduction.red_red_ctx; tea; eauto with fvs.
  Qed.

  Lemma cumul_red_ctx_inv {Γ Γ' : closed_context} {T U : open_term Γ} :
    Σ ;;; Γ |- T <= U ->
    @red_ctx Σ Γ' Γ ->
    Σ ;;; Γ' |- T <= U.
  Proof.
    intros H Hctx.
    apply cumul_alt in H as [v [v' [[redl redr] leq]]].
    epose proof (red_red_ctx_inv redl Hctx).
    epose proof (red_red_ctx_inv redr Hctx).
    apply cumul_alt.
    exists v, v'.
    split. pcuic. auto.
  Qed.

(* 
  Lemma conv_red_ctx {Γ Γ' T U} :
    Σ ;;; Γ |- T = U ->
    @red_ctx Σ Γ Γ' ->
    Σ ;;; Γ' |- T = U.
  Proof.
    intros H Hctx. apply cumul2_conv.
    split; eapply cumul_red_ctx; eauto; eapply conv_cumul2 in H; eapply H.
  Qed.

  Lemma conv_red_ctx_inv {Γ Γ' T U} :
    Σ ;;; Γ |- T = U ->
    @red_ctx Σ Γ' Γ ->
    Σ ;;; Γ' |- T = U.
  Proof.
    intros H Hctx. apply cumul2_conv.
    split; eapply cumul_red_ctx_inv; eauto; eapply conv_cumul2 in H; eapply H.
  Qed. *)

  Arguments red_ctx : clear implicits.

  Lemma red_eq_context_upto_l {R Re} {Γ Δ} {u} {v}
        `{RelationClasses.Reflexive _ R} `{RelationClasses.Transitive _ R} `{SubstUnivPreserving R}
        `{RelationClasses.Reflexive _ Re} `{RelationClasses.Transitive _ Re} `{SubstUnivPreserving Re}
        `{RelationClasses.subrelation _ Re R} :
    red Σ Γ u v ->
    eq_context_upto Σ Re R Γ Δ ->
    ∑ v',
    red Σ Δ u v' *
    eq_term_upto_univ Σ Re Re v v'.
  Proof.
    intros r HΓ.
    induction r.
    - eapply (red1_eq_context_upto_l _ (Rle:=R)) in r; eauto.
      destruct r as [v [? ?]]. exists v. intuition pcuic.
    - exists x. split; auto. reflexivity.
    - destruct IHr1 as [v' [? ?]]; eauto with fvs.
      destruct IHr2 as [v'' [? ?]]; eauto with fvs.
      eapply (red_eq_term_upto_univ_l _ _ (u:=y) (v:=v'') (u':=v')) in e; try tc. all:pcuic.
      destruct e as [? [? ?]].
      exists x0; split; eauto.
      now transitivity v'.
      eapply eq_term_upto_univ_trans with v''; auto.
  Qed.

  Lemma red_eq_context_upto_r {R Re Γ Δ} {u} {v}
        `{RelationClasses.Equivalence _ Re} `{SubstUnivPreserving Re}
        `{RelationClasses.PreOrder _ R} `{SubstUnivPreserving R}
        `{RelationClasses.subrelation _ Re R} :
    red Σ Δ u v ->
    eq_context_upto Σ Re R Γ Δ ->
    ∑ v',
    red Σ Γ u v' *
    eq_term_upto_univ Σ Re Re v v'.
  Proof.
    intros r HΓ.
    induction r.
    - eapply (red1_eq_context_upto_r _ Re R) in r; eauto.
      destruct r as [v [? ?]]. exists v. intuition pcuic.
      now symmetry.
    - exists x. split; auto. reflexivity.
    - destruct IHr1 as [v' [? ?]].
      destruct IHr2 as [v'' [? ?]].
      unshelve eapply (red_eq_term_upto_univ_l Σ _ (Γ := Γ) (u:=y) (v:=v'') (u':=v')) in e. all:pcuic.
      destruct e as [? [? ?]].
      exists x0; split; eauto.
      transitivity v'; auto.
      eapply eq_term_upto_univ_trans with v''; auto; tc.
  Qed.

  Lemma cumul_trans_red_leqterm {Γ : closed_context} {t u v : open_term Γ} :
    Σ ;;; Γ |- t <= u -> Σ ;;; Γ |- u <= v ->
    ∑ l o r, red Σ Γ t l *
             red Σ Γ u o *
             red Σ Γ v r *
             leq_term Σ.1 Σ l o * leq_term Σ.1 Σ o r.
  Proof.
    intros X X0.
    intros.
    eapply cumul_alt in X as [t0 [u0 [[redl redr] eq]]].
    eapply cumul_alt in X0 as [u1 [v0 [[redl' redr'] eq']]].
    destruct (red_confluence redr redl') as [unf [nfl nfr]].
    eapply red_eq_term_upto_univ_r in eq; try tc. 2:tea.
    destruct eq as [t1 [red'0 eq2]].
    eapply red_eq_term_upto_univ_l in eq'; try tc; tea.
    destruct eq' as [v1 [red'1 eq1]].
    exists t1, unf, v1.
    repeat split.
    transitivity t0; auto.
    transitivity u0; auto.
    transitivity v0; auto. eapply eq2. eapply eq1.
  Qed.

  Lemma conv_eq_context_upto {Γ} {Δ} {T U} :
    eq_context_upto Σ (eq_universe Σ) (eq_universe Σ) Γ Δ ->
    Σ ;;; Γ |- T = U ->
    Σ ;;; Δ |- T = U.
  Proof.
    intros eqctx cum.
    eapply conv_alt_red in cum as [nf [nf' [[redl redr] ?]]].
    eapply (red_eq_context_upto_l (R:=eq_universe _) (Re:=eq_universe _)) in redl; tea; tc.
    eapply (red_eq_context_upto_l (R:=eq_universe _) (Re:=eq_universe _)) in redr; tea; tc.
    destruct redl as [v' [redv' eqv']].
    destruct redr as [v'' [redv'' eqv'']].
    eapply conv_alt_red. exists v', v''; intuition auto.
    transitivity nf.
    now symmetry. now transitivity nf'.
  Qed.
  
  Lemma conv_leq_context_upto {Γ Δ T U} :
    eq_context_upto Σ (eq_universe Σ) (leq_universe Σ) Γ Δ ->
    Σ ;;; Δ |- T = U ->
    Σ ;;; Γ |- T = U.
  Proof.
    intros eqctx cum.
    eapply conv_alt_red in cum as [nf [nf' [[redl redr] ?]]].
    eapply (red_eq_context_upto_r (Re:=eq_universe _)) in redl; tea.
    eapply (red_eq_context_upto_r (Re:=eq_universe _)) in redr; tea.
    destruct redl as [v' [redv' eqv']].
    destruct redr as [v'' [redv'' eqv'']].
    eapply conv_alt_red. exists v', v''; intuition auto.
    transitivity nf.
    now symmetry. now transitivity nf'.
  Qed.

  (* Conversion is untyped so this currently holds as context equality 
     just allows cumulativity on types, which do not participate in reduction. 
     However the useful lemma is the one above that shows we can lift a 
     conversion from a large context to a smaller one (contravariance).    
     *)
  Local Remark conv_eq_context_upto_leq_inv {Γ Δ T U} :
    eq_context_upto Σ (eq_universe Σ) (leq_universe Σ) Γ Δ ->
    Σ ;;; Γ |- T = U ->
    Σ ;;; Δ |- T = U.
  Proof.
    intros eqctx cum.
    eapply conv_alt_red in cum as [nf [nf' [[redl redr] ?]]].
    eapply (red_eq_context_upto_l (Re:=eq_universe _)) in redl; tea.
    eapply (red_eq_context_upto_l (Re:=eq_universe _)) in redr; tea.
    destruct redl as [v' [redv' eqv']].
    destruct redr as [v'' [redv'' eqv'']].
    eapply conv_alt_red. exists v', v''; intuition auto.
    transitivity nf.
    now symmetry. now transitivity nf'.
  Qed.

  Lemma cumul_leq_context_upto {Γ Δ T U} :
    eq_context_upto Σ (eq_universe Σ) (leq_universe Σ) Δ Γ ->
    Σ ;;; Γ |- T <= U ->
    Σ ;;; Δ |- T <= U.
  Proof.
    intros eqctx cum.
    eapply cumul_alt in cum as [nf [nf' [[redl redr] ?]]].
    eapply (red_eq_context_upto_r (Re:=eq_universe Σ)) in redl; tea.
    eapply (red_eq_context_upto_r (Re:=eq_universe Σ)) in redr; tea.
    destruct redl as [v' [redv' eqv']].
    destruct redr as [v'' [redv'' eqv'']].
    eapply cumul_alt. exists v', v''; intuition auto.
    transitivity nf.
    apply eq_term_leq_term. now symmetry.
    transitivity nf'; auto.
    now apply eq_term_leq_term.
  Qed.

  Local Remark cumul_leq_context_upto_inv {Γ Δ T U} :
    eq_context_upto Σ (eq_universe Σ) (leq_universe Σ) Γ Δ ->
    Σ ;;; Γ |- T <= U ->
    Σ ;;; Δ |- T <= U.
  Proof.
    intros eqctx cum.
    eapply cumul_alt in cum as [nf [nf' [[redl redr] ?]]].
    eapply (red_eq_context_upto_l (Re:=eq_universe Σ) (Δ:=Δ)) in redl; tas.
    eapply (red_eq_context_upto_l (Re:=eq_universe Σ) (Δ:=Δ)) in redr; tas.
    destruct redl as [v' [redv' eqv']].
    destruct redr as [v'' [redv'' eqv'']].
    eapply cumul_alt. exists v', v''; intuition auto.
    eapply leq_term_trans with nf.
    apply eq_term_leq_term. now apply eq_term_sym.
    eapply leq_term_trans with nf'; auto.
    now apply eq_term_leq_term.
  Qed.

  Lemma eq_context_upto_impl {Re Rle} {Re' Rle'} {Γ Δ}
    `{RelationClasses.subrelation _ Re Re'}
    `{RelationClasses.subrelation _ Rle Rle'}
    `{RelationClasses.subrelation _ Re' Rle'} :
    eq_context_upto Σ Re Rle Γ Δ -> 
    eq_context_upto Σ Re' Rle' Γ Δ.
  Proof.
     induction 1; constructor; auto.
     eapply compare_decls_impl; eauto.
     intros x y h.
     eapply eq_term_upto_univ_impl. 5:eauto. all:try tc || auto.
     intros x y h.
     eapply eq_term_upto_univ_impl. 5:eauto. all:try tc || auto.
     transitivity Re'; auto.
  Qed.

  Lemma eq_leq_context_upto Γ Δ : 
    eq_context_upto Σ (eq_universe Σ) (eq_universe Σ) Γ Δ ->
    eq_context_upto Σ (eq_universe Σ) (leq_universe Σ) Γ Δ.
  Proof. apply eq_context_upto_impl. Qed.

  Lemma cumul_eq_context_upto {Γ Δ T U} :
    eq_context_upto Σ (eq_universe Σ) (eq_universe Σ) Γ Δ ->
    Σ ;;; Γ |- T <= U ->
    Σ ;;; Δ |- T <= U.
  Proof.
    intros eqctx cum. symmetry in eqctx.
    apply eq_leq_context_upto in eqctx.
    eapply cumul_leq_context_upto; eauto.
  Qed.

  Lemma conv_alt_red_ctx {Γ : closed_context} {Γ'} {T U : open_term Γ} :
    Σ ;;; Γ |- T = U ->
    @red_ctx Σ Γ Γ' ->
    Σ ;;; Γ' |- T = U.
  Proof.
    intros H Hctx.
    eapply conv_alt_red in H. apply conv_alt_red.
    destruct H as [T' [U' [[redv redv'] leqvv']]].
    destruct (red_red_ctx _ _ redv Hctx) as [Tj [redTj redT'j]].
    destruct (red_red_ctx _ _ redv' Hctx) as [Uj [redUUj redU'j]].
    destruct (fill_eq (Γ := inj_closed Γ' byfvs) (t := inj_open T' byfvs) (u := inj_open U' byfvs) leqvv' redT'j redU'j) as [Tnf [Unf [[redTnf redUnf] eqnf]]].
    exists Tnf, Unf; intuition eauto.
    now transitivity Tj.
    now transitivity Uj.
  Qed.

  Lemma conv_alt_red_ctx_inv {Γ Γ' : closed_context} {T U : open_term Γ} :
    Σ ;;; Γ |- T = U ->
    red_ctx Σ Γ' Γ ->
    Σ ;;; Γ' |- T = U.
  Proof.
    intros H Hctx.
    apply conv_alt_red in H as [v [v' [[redl redr] leq]]].
    pose proof (red_red_ctx_inv redl Hctx).
    pose proof (red_red_ctx_inv redr Hctx).
    apply conv_alt_red.
    exists v, v'.
    split. pcuic. auto.
  Qed.
  
  Lemma cumul_alt_red_ctx {Γ : closed_context} {Γ'} {T U : open_term Γ} :
    Σ ;;; Γ |- T <= U ->
    @red_ctx Σ Γ Γ' ->
    Σ ;;; Γ' |- T <= U.
  Proof.
    intros H Hctx.
    eapply cumul_alt in H. apply cumul_alt.
    destruct H as [T' [U' [[redv redv'] leqvv']]].
    destruct (red_red_ctx _ _ redv Hctx) as [Tj [redTj redT'j]].
    destruct (red_red_ctx _ _ redv' Hctx) as [Uj [redUUj redU'j]].
    destruct (fill_le (Γ := inj_closed Γ' byfvs) (t := inj_open T' byfvs) (u := inj_open U' byfvs) leqvv' redT'j redU'j) as [Tnf [Unf [[redTnf redUnf] eqnf]]].
    exists Tnf, Unf; intuition eauto.
    now transitivity Tj.
    now transitivity Uj.
  Qed.

  Lemma cumul_alt_red_ctx_inv {Γ Γ' : closed_context} {T U : open_term Γ} :
    Σ ;;; Γ |- T <= U ->
    red_ctx Σ Γ' Γ ->
    Σ ;;; Γ' |- T <= U.
  Proof.
    intros H Hctx.
    apply cumul_alt in H as [v [v' [[redl redr] leq]]].
    pose proof (red_red_ctx_inv redl Hctx).
    pose proof (red_red_ctx_inv redr Hctx).
    apply cumul_alt.
    exists v, v'.
    split. pcuic. auto.
  Qed.

  Lemma cumul_context_red_context {Γ Γ' : closed_context} :
    cumul_context Γ Γ' ->
    ∑ Δ Δ', red_ctx Σ Γ Δ * red_ctx Σ Γ' Δ' * eq_context_upto Σ (eq_universe Σ) (leq_universe Σ) Δ Δ'.
  Proof.
    intros Hctx.
    destruct Γ as [Γ onΓ], Γ' as [Γ' onΓ']. cbn in *.
    induction Hctx.
    - exists [], []; intuition pcuic.
    - move: onΓ onΓ'; rewrite !on_free_vars_ctx_snoc => /andP[] onΓ ond /andP[] onΓ' ond'.
      destruct IHHctx as [Δ [Δ' [[? ?] ?]]]; eauto with fvs.
      depelim p; inv_on_free_vars.
      { set (Γcl := ⇑ Γ). change Γ with (proj1_sig Γcl) in r.
        set (Γ'cl := ⇑ Γ'). change Γ' with (proj1_sig Γ'cl) in r0.
        set (Δcl := ⇑ Δ). set (Δ'cl := ⇑ Δ').
        set (Tcl := ⤊ T : open_term Γcl).
        assert (on_free_vars (shiftnP #|Γ| xpred0) T').
        now rewrite (All2_fold_length Hctx).
        unshelve epose proof (cumul_alt_red_ctx (Γ := Γcl) (T:=Tcl) (U:= ⤊ T') c r).
        eapply cumul_alt in X.
        destruct X as [T'' [U' [[? ?] ?]]].
        pose proof (red_red_ctx_inv (Δ := Γcl) (Γ := ⇑ Δ) (t := ⤊ T) r1 r).
        unshelve epose proof (red_red_ctx_inv (Δ := Γcl) (Γ := ⇑ Δ) (t := ⤊ T') r2 r).
        destruct (red_eq_context_upto_l r1 a). destruct p.
        destruct (red_eq_context_upto_l r2 a). destruct p.
        exists (Δ ,, vass na T''), (Δ' ,, vass na' x0).
        split; [split|]; constructor; try constructor; auto.
        + unshelve eapply (red_red_ctx_inv (Γ := Δ'cl) (Δ := Γ'cl) (t := inj_open T' _)); eauto.
          cbn. rewrite -(All2_fold_length r0) /=; eauto.
        + eapply eq_term_upto_univ_trans with U'; eauto; try tc.
          now apply eq_term_leq_term. }
      { set (Γcl := ⇑ Γ). change Γ with (proj1_sig Γcl) in r.
        set (Γ'cl := ⇑ Γ'). change Γ' with (proj1_sig Γ'cl) in r0.
        set (Δcl := ⇑ Δ). set (Δ'cl := ⇑ Δ').
        move: ond ond' => /andP[] /= onb onT /andP[] /= onb' onT'.
        set (Tcl := ⤊ T : open_term Γcl). 
        assert (on_free_vars (shiftnP #|Γ| xpred0) T').
        now rewrite (All2_fold_length Hctx).
        unshelve epose proof (conv_alt_red_ctx (Γ := Γcl) (T := ⤊ b) (U := ⤊ b') c r).
        now rewrite (All2_fold_length Hctx).
        eapply conv_alt_red in X.
        destruct X as [t' [u' [[? ?] ?]]].
        pose proof (red_red_ctx_inv (Δ := Γcl) (Γ := ⇑ Δ) (t := ⤊ b) r1 r).
        unshelve epose proof (red_red_ctx_inv (Δ := Γcl) (Γ := ⇑ Δ) (t := ⤊ b') r2 r).
        rewrite -(All2_fold_length r) (All2_fold_length Hctx); cbn; eauto with fvs.
        destruct (red_eq_context_upto_l r1 a) as [t'' [? ?]].
        destruct (red_eq_context_upto_l r2 a) as [u'' [? ?]].
        pose proof (cumul_alt_red_ctx  (Γ := Γcl) (T := ⤊ T) (U := ⤊ T') c0 r) as hTU.
        eapply cumul_alt in hTU.
        destruct hTU as [T'' [U' [[rT rU] eTU']]].
        pose proof (red_red_ctx_inv (Δ := Γcl) (Γ := ⇑ Δ) (t := ⤊ T) rT r).
        pose proof (red_red_ctx_inv  (Δ:= Γcl) (Γ := ⇑ Δ) (t := ⤊ T') rU r).
        destruct (red_eq_context_upto_l rT a) as [T''' [? ?]].
        destruct (red_eq_context_upto_l rU a) as [U''' [? ?]].
        exists (Δ ,, vdef na t' T''), (Δ' ,, vdef na' u'' U''').
        split; [split|]. all: constructor ; auto.
        * constructor; auto. 
        * constructor.
          -- apply (red_red_ctx_inv (Γ := Δ'cl) (Δ := Γ'cl) (t := inj_open b' byfvs)); eauto.
          -- apply (red_red_ctx_inv (Γ := Δ'cl) (Δ := Γ'cl) (t := inj_open T' byfvs)); eauto.
        * constructor; auto.
          eapply eq_term_upto_univ_trans with u'; eauto; tc.
          eapply eq_term_upto_univ_trans with U'; eauto; try tc.
          now eapply eq_term_leq_term. }
  Qed.

  Lemma conv_context_red_context {Γ Γ' : closed_context} :
    conv_context Γ Γ' ->
    ∑ Δ Δ', red_ctx Σ Γ Δ * red_ctx Σ Γ' Δ' * eq_context_upto Σ (eq_universe Σ) (eq_universe Σ) Δ Δ'.
  Proof.
    intros Hctx.
    destruct Γ as [Γ onΓ], Γ' as [Γ' onΓ']. cbn in *.
    induction Hctx.
    - exists [], []; intuition pcuic.
    - move: onΓ onΓ'; rewrite !on_free_vars_ctx_snoc => /andP[] onΓ ond /andP[] onΓ' ond'.
      destruct IHHctx as [Δ [Δ' [[? ?] ?]]]; eauto with fvs.
      depelim p; inv_on_free_vars.
      { set (Γcl := ⇑ Γ). change Γ with (proj1_sig Γcl) in r.
        set (Γ'cl := ⇑ Γ'). change Γ' with (proj1_sig Γ'cl) in r0.
        set (Δcl := ⇑ Δ). set (Δ'cl := ⇑ Δ').
        set (Tcl := ⤊ T : open_term Γcl).
        assert (on_free_vars (shiftnP #|Γ| xpred0) T').
        now rewrite (All2_fold_length Hctx).
        unshelve epose proof (conv_alt_red_ctx (Γ := Γcl) (T:=Tcl) (U:= ⤊ T') c r).
        eapply conv_alt_red in X.
        destruct X as [T'' [U' [[? ?] ?]]].
        pose proof (red_red_ctx_inv (Δ := Γcl) (Γ := ⇑ Δ) (t := ⤊ T) r1 r).
        unshelve epose proof (red_red_ctx_inv (Δ := Γcl) (Γ := ⇑ Δ) (t := ⤊ T') r2 r).
        destruct (red_eq_context_upto_l r1 a). destruct p.
        destruct (red_eq_context_upto_l r2 a). destruct p.
        exists (Δ ,, vass na T''), (Δ' ,, vass na' x0).
        split; [split|]; constructor; try constructor; auto.
        + unshelve eapply (red_red_ctx_inv (Γ := Δ'cl) (Δ := Γ'cl) (t := inj_open T' _)); eauto.
          cbn. rewrite -(All2_fold_length r0) /=; eauto.
        + eapply eq_term_upto_univ_trans with U'; eauto; try tc. }
      { set (Γcl := ⇑ Γ). change Γ with (proj1_sig Γcl) in r.
        set (Γ'cl := ⇑ Γ'). change Γ' with (proj1_sig Γ'cl) in r0.
        set (Δcl := ⇑ Δ). set (Δ'cl := ⇑ Δ').
        move: ond ond' => /andP[] /= onb onT /andP[] /= onb' onT'.
        set (Tcl := ⤊ T : open_term Γcl). 
        assert (on_free_vars (shiftnP #|Γ| xpred0) T').
        now rewrite (All2_fold_length Hctx).
        unshelve epose proof (conv_alt_red_ctx (Γ := Γcl) (T := ⤊ b) (U := ⤊ b') c r).
        now rewrite (All2_fold_length Hctx).
        eapply conv_alt_red in X.
        destruct X as [t' [u' [[? ?] ?]]].
        pose proof (red_red_ctx_inv (Δ := Γcl) (Γ := ⇑ Δ) (t := ⤊ b) r1 r).
        unshelve epose proof (red_red_ctx_inv (Δ := Γcl) (Γ := ⇑ Δ) (t := ⤊ b') r2 r).
        rewrite -(All2_fold_length r) (All2_fold_length Hctx); cbn; eauto with fvs.
        destruct (red_eq_context_upto_l r1 a) as [t'' [? ?]].
        destruct (red_eq_context_upto_l r2 a) as [u'' [? ?]].
        pose proof (conv_alt_red_ctx  (Γ := Γcl) (T := ⤊ T) (U := ⤊ T') c0 r) as hTU.
        eapply conv_alt_red in hTU.
        destruct hTU as [T'' [U' [[rT rU] eTU']]].
        pose proof (red_red_ctx_inv (Δ := Γcl) (Γ := ⇑ Δ) (t := ⤊ T) rT r).
        pose proof (red_red_ctx_inv  (Δ:= Γcl) (Γ := ⇑ Δ) (t := ⤊ T') rU r).
        destruct (red_eq_context_upto_l rT a) as [T''' [? ?]].
        destruct (red_eq_context_upto_l rU a) as [U''' [? ?]].
        exists (Δ ,, vdef na t' T''), (Δ' ,, vdef na' u'' U''').
        split; [split|]. all: constructor ; auto.
        * constructor; auto. 
        * constructor.
          -- apply (red_red_ctx_inv (Γ := Δ'cl) (Δ := Γ'cl) (t := inj_open b' byfvs)); eauto.
          -- apply (red_red_ctx_inv (Γ := Δ'cl) (Δ := Γ'cl) (t := inj_open T' byfvs)); eauto.
        * constructor; auto.
          eapply eq_term_upto_univ_trans with u'; eauto; tc.
          eapply eq_term_upto_univ_trans with U'; eauto; try tc. }
  Qed.

  Lemma conv_cumul_ctx {Γ Γ' : closed_context} {T U : open_term Γ} :
    Σ ;;; Γ |- T = U ->
    cumul_context Γ' Γ ->
    Σ ;;; Γ' |- T = U.
  Proof.
    intros H Hctx.
    destruct T as [T hT], U as [U hU].
    apply cumul_context_red_context in Hctx => //.
    destruct Hctx as [Δ [Δ' [[l r] elr]]].
    have r' := conv_alt_red_ctx H r.
    have r'' := conv_leq_context_upto elr r'. cbn in *.
    unshelve epose proof (conv_alt_red_ctx_inv (Γ := inj_closed Δ byfvs) (T:=inj_open T byfvs) (U:=inj_open U byfvs) r'' l);
    eauto with fvs.
    all:rewrite (All2_fold_length elr) -(All2_fold_length r); eauto with fvs.
  Qed.
  
  Lemma conv_conv_ctx {Γ Γ' : closed_context} {T U : open_term Γ} :
    Σ ;;; Γ |- T = U ->
    conv_context Γ Γ' ->
    Σ ;;; Γ' |- T = U.
  Proof.
    intros H Hctx.
    apply conv_context_red_context in Hctx => //.
    destruct Hctx as [Δ [Δ' [[l r] elr]]].
    have r' := conv_alt_red_ctx H l.
    have r'' := conv_eq_context_upto elr r'. cbn in *.
    unshelve epose proof 
      (conv_alt_red_ctx_inv (Γ := inj_closed Δ' byfvs) (T:=inj_open T byfvs) (U:=inj_open U byfvs) r'' r);
      eauto with fvs.
    all:rewrite -(All2_fold_length elr) -(All2_fold_length l); eauto with fvs.
  Qed.

  Lemma cumul_conv_ctx {Γ Γ' : closed_context} {T U : open_term Γ} :
    Σ ;;; Γ |- T <= U ->
    conv_context Γ Γ' ->
    Σ ;;; Γ' |- T <= U.
  Proof.
    intros H Hctx.
    apply conv_context_red_context in Hctx => //.
    destruct Hctx as [Δ [Δ' [[l r] elr]]].
    have r' := cumul_alt_red_ctx H l.
    have r'' := cumul_eq_context_upto elr r'. cbn in *.
    unshelve epose proof 
      (cumul_alt_red_ctx_inv (Γ := inj_closed Δ' byfvs) (T:=inj_open T byfvs) (U:=inj_open U byfvs) r'' r);
      eauto with fvs.
    all:rewrite -(All2_fold_length elr) -(All2_fold_length l); eauto with fvs.
  Qed.

  Lemma conv_cumul_context {Γ Δ} : 
    conv_context Γ Δ -> cumul_context Γ Δ.
  Proof.
    induction 1; constructor; auto;
    depelim p; constructor; auto; now apply conv_cumul.
  Qed.
  Hint Resolve conv_cumul_context : pcuic.

  Lemma cumul_cumul_ctx {Γ Γ' : closed_context} {T U : open_term Γ} :
    Σ ;;; Γ |- T <= U ->
    cumul_context Γ' Γ ->
    Σ ;;; Γ' |- T <= U.
  Proof.
    intros H Hctx.
    apply cumul_context_red_context in Hctx => //.
    destruct Hctx as [Δ [Δ' [[l r] elr]]].
    have r' := cumul_alt_red_ctx H r.
    have r'' := cumul_leq_context_upto elr r'. cbn in *.
    unshelve epose proof 
      (cumul_alt_red_ctx_inv (Γ := inj_closed Δ byfvs) (T:=inj_open T byfvs) (U:=inj_open U byfvs) r'' l);
      eauto with fvs.
    all:rewrite (All2_fold_length elr) -(All2_fold_length r); eauto with fvs.
  Qed.

  (** Again, this is only the case because conversion is untyped. We require
      nothing on Γ or Γ'. *)
  Local Remark cumul_cumul_ctx_inv {Γ Γ' : closed_context} {T U : open_term Γ} :
    Σ ;;; Γ |- T <= U ->
    cumul_context Γ Γ' ->
    Σ ;;; Γ' |- T <= U.
  Proof.
    intros H Hctx. 
    apply cumul_context_red_context in Hctx => //.
    destruct Hctx as [Δ [Δ' [[l r] elr]]].
    have r' := cumul_alt_red_ctx H l.
    have r'' := cumul_leq_context_upto_inv elr r'. cbn in *.
    unshelve epose proof 
      (cumul_alt_red_ctx_inv (Γ := inj_closed Δ' byfvs) (T:=inj_open T byfvs) (U:=inj_open U byfvs) r'' r);
      eauto with fvs.
    all:rewrite -(All2_fold_length elr) -(All2_fold_length l); eauto with fvs.
  Qed.

End ContextConversion.

Hint Resolve isType_open wf_local_closed_context : fvs.

Definition conv_cum {cf:checker_flags} le Σ Γ T T' :=
  if le then Σ ;;; Γ |- T <= T' else Σ ;;; Γ |- T = T'.

Notation ws_decl Γ d := (on_free_vars_decl (shiftnP #|Γ| xpred0) d).
  
Definition equality_decls {cf : checker_flags} (le : bool) (Σ : global_env_ext) (Γ Γ' : context) d d' :=
  (if le then cumul_decls else conv_decls) Σ Γ Γ' d d'.

Definition open_decl (Γ : context) := { d : context_decl | ws_decl Γ d }.
Definition open_decl_proj {Γ : context} (d : open_decl Γ) := proj1_sig d.
Coercion open_decl_proj : open_decl >-> context_decl.

Definition vass_open_decl {Γ : closed_context} (na : binder_annot name) (t : open_term Γ) : open_decl Γ :=
  exist (vass na t) (proj2_sig t).

Definition vdef_open_decl {Γ : closed_context} (na : binder_annot name) (b t : open_term Γ) : open_decl Γ :=
  exist (vdef na b t) (introT andP (conj (proj2_sig b) (proj2_sig t))).
  
Inductive All_open_decls_alpha {Γ : closed_context} le (P : bool -> open_term Γ -> open_term Γ -> Type) :
  open_decl Γ -> open_decl Γ -> Type :=
| on_open_vass_alpha {na na' : binder_annot name} {t : open_term Γ} {t' : open_term Γ} :
  eq_binder_annot na na' -> P le t t' -> 
  All_open_decls_alpha le P (vass_open_decl na t) (vass_open_decl na' t')

| on_open_vdef_alpha {na na' : binder_annot name} {b t : open_term Γ} {b' t' : open_term Γ} :
  eq_binder_annot na na' ->
  P false b b' ->
  P le t t' ->
  All_open_decls_alpha le P (vdef_open_decl na b t) (vdef_open_decl na' b' t').
Derive Signature NoConfusion for All_open_decls_alpha.

Lemma All_open_decls_alpha_irrel {Γ : closed_context} le (P : bool -> open_term Γ -> open_term Γ -> Type) 
  {d d0 d' d'0 : open_decl Γ} :
  All_open_decls_alpha le P d0 d'0 ->
  d = d0 :> context_decl ->
  d' = d'0 :> context_decl ->
  All_open_decls_alpha le P d d'.
Proof.
  case => [na na' t t' eqna eqt|na na' b t b' t' eqna eqb eqt] /=.
  - destruct d, d'; simpl in *; intros -> ->.
    rewrite (uip i (proj2_sig t)).
    rewrite (uip i0 (proj2_sig t')).
    constructor; auto.
  - destruct d, d'; simpl in *; intros -> ->.
    rewrite (uip i (introT andP (conj (proj2_sig b) (proj2_sig t)))).
    rewrite (uip i0 (introT andP (conj (proj2_sig b') (proj2_sig t')))).
    constructor; auto.
Qed.

(* Arguments All_open_decls_alpha {Γ Γ'} _%function_scope.
Arguments on_open_vass_alpha {Γ Γ'} _%function_scope.
Arguments on_open_vdef_alpha {Γ Γ'} _%function_scope. *)
  
Definition equality_open_decls {cf : checker_flags} (le : bool) (Σ : global_env_ext)
  (Γ : closed_context) (d : open_decl Γ) (d' : open_decl Γ) :=
  All_open_decls_alpha le (fun le => @ws_equality cf le Σ Γ) d d'.

Definition ws_equality_decls {cf : checker_flags} (le : bool) (Σ : global_env_ext) (Γ Γ' : context) : context_decl -> context_decl -> Type :=
  fun d d' => 
    #|Γ| = #|Γ'| × equality_decls le Σ Γ Γ' d d' ×
    [&& on_free_vars_ctx xpred0 Γ, on_free_vars_ctx xpred0 Γ', ws_decl Γ d & ws_decl Γ' d'].

(* Definition equality_open_decls {cf : checker_flags} (le : bool) (Σ : global_env_ext) 
  (Γ : closed_context) (d : open_decl Γ) (d' : open_decl Γ) :=
  ∑ eq : #|Γ| = #|Γ'|, equality_open_decls le Σ Γ d (move_ws_term d'. *)
    
Notation is_open_term Γ t := (on_free_vars (shiftnP #|Γ| xpred0) t).
Notation is_open_decl Γ t := (on_free_vars_decl (shiftnP #|Γ| xpred0) t).
Notation is_closed_context Γ := (on_free_vars_ctx xpred0 Γ).

Lemma into_equality_open_decls {cf : checker_flags} {le : bool} {Σ : global_env_ext} {wfΣ : wf Σ}(Γ Γ' : context) d d' :
  equality_decls le Σ Γ Γ' d d' -> 
  forall (onΓ : on_free_vars_ctx xpred0 Γ)
        (isd: is_open_decl Γ d)
        (isd': is_open_decl Γ d'),
  equality_open_decls le Σ (exist Γ onΓ) (exist d isd) (exist d' isd').
Proof.
  case: le; move=> [].
  - intros; eapply All_open_decls_alpha_irrel.
    econstructor 1. tea.
    exact (into_ws_equality (le:=true) c isd isd' onΓ).
    all:trea.
  - intros; eapply All_open_decls_alpha_irrel.
    econstructor 2. tea.
    unshelve apply (into_ws_equality (le:=false) c); cbn.
    now move/andP: isd. now move/andP: isd'.
    unshelve apply (into_ws_equality (le:=true) c0); cbn.
    now move/andP: isd. now move/andP: isd'.
    all:trea.
  - intros; eapply All_open_decls_alpha_irrel.
    econstructor 1. tea.
    unshelve apply (into_ws_equality (le:=false) c); cbn; tea.
    all:trea.
  - intros; eapply All_open_decls_alpha_irrel.
    econstructor 2. tea.
    unshelve apply (into_ws_equality (le:=false) c); cbn.
    now move/andP: isd. now move/andP: isd'.
    unshelve apply (into_ws_equality (le:=false) c0); cbn.
    now move/andP: isd. now move/andP: isd'.
    all:trea.
Qed.

Lemma into_ws_equality_open_decls {cf : checker_flags} (le : bool) {Σ : global_env_ext} {wfΣ : wf Σ} 
  {Γ Γ' : context} {d d'} :
  ws_equality_decls le Σ Γ Γ' d d' -> 
  ∑ (onΓ : on_free_vars_ctx xpred0 Γ)
        (isd: is_open_decl Γ d)
        (isd': is_open_decl Γ d'),
  equality_open_decls le Σ (exist Γ onΓ) (exist d isd) (exist d' isd').
Proof.
  rewrite /ws_equality_decls=> [] [] eqctx [] eqd /and4P [] onΓ onΓ' isd isd'.
  exists onΓ, isd.
  unshelve eexists. now rewrite eqctx. cbn.
  eapply into_equality_open_decls; tea.
Qed.

Lemma equality_open_decls_forget {cf : checker_flags} {le : bool} {Σ : global_env_ext} {wfΣ : wf Σ} 
  {Γ : closed_context} {Γ' : closed_context} {d d' : open_decl Γ} :
  #|Γ| = #|Γ'| ->
  equality_open_decls le Σ Γ d d' ->
  ws_equality_decls le Σ Γ Γ' d d'. 
Proof.
  move=> hlen. rewrite /equality_open_decls /ws_equality_decls => a; split => //.
  rewrite -hlen.
  split.
  2:{ apply/and4P; split; intuition eauto with fvs.
      all:destruct a; cbn; eauto with fvs. }
  destruct a. simpl. red.
  eapply ws_equality_forget in w.
  destruct le; constructor; auto.
  eapply ws_equality_forget in w.
  eapply ws_equality_forget in w0.
  destruct le; constructor; auto.
Qed.
  
Instance equality_open_decls_trans {cf : checker_flags} (le : bool) {Σ : global_env_ext} {wfΣ : wf Σ} {Γ : closed_context} :
  Transitive (equality_open_decls le Σ Γ).
Proof.
  intros d d' d''.
  rewrite /equality_open_decls.
  intros ond ond'; destruct ond; depelim ond'.
  destruct t', t0. noconf e1. simpl in H. subst i; auto.
  econstructor; now etransitivity.
  destruct b', b0. noconf H.
  destruct t', t0; noconf e1.
  simpl in H0.
  econstructor; etransitivity; tea.
  now rewrite (uip i i0).
  now rewrite (uip i1 i2).
Qed.

Instance ws_equality_decls_trans {cf : checker_flags} (le : bool) (Σ : global_env_ext) {wfΣ : wf Σ}
  {Γ Γ'} : Transitive (ws_equality_decls le Σ Γ Γ').
Proof.
  intros Δ Δ' Δ''.
  move=> a; move: a.1 => HΓ. move: a.2.2 => /and4P[] _ onΓ' _ _. move: a.
  move/into_ws_equality_open_decls => [onΓ [isd [isde' eq]]].
  move/into_ws_equality_open_decls => [onΓ'' [isd' [isde'' eq']]].
  rewrite -(uip onΓ onΓ'') in eq'.
  rewrite -(uip isde' isd') in eq'.
  now generalize (transitivity eq eq') => /(equality_open_decls_forget (Γ := exist Γ onΓ) (Γ' := exist Γ' onΓ') HΓ).
Qed.

Lemma into_ws_equality_decls {cf : checker_flags} {le : bool} {Σ : global_env_ext}
  {Γ Γ'} {d d' : context_decl} (c : equality_decls le Σ Γ Γ' d d') :
  #|Γ| = #|Γ'| ->
  on_free_vars_ctx xpred0 Γ ->
  on_free_vars_ctx xpred0 Γ' ->
  is_open_decl Γ d ->
  is_open_decl Γ' d' ->
  ws_equality_decls le Σ Γ Γ' d d'.
Proof.
  rewrite /ws_equality_decls => len onΓ onΓ' ond ond'. 
  repeat split => //.
  now rewrite onΓ onΓ' ond ond'.
Qed.

Lemma equality_decls_trans {cf : checker_flags} {le : bool} {Σ : global_env_ext} {wfΣ : wf Σ}
  {Γ Γ'} (d d' d'' : context_decl) (c : equality_decls le Σ Γ Γ' d d')
  (c' : equality_decls le Σ Γ Γ' d' d'') : 
  #|Γ| = #|Γ'| ->
  on_free_vars_ctx xpred0 Γ ->
  on_free_vars_ctx xpred0 Γ' ->
  is_open_decl Γ d ->
  is_open_decl Γ' d' ->
  is_open_decl Γ' d'' ->
  equality_decls le Σ Γ Γ' d d''.
Proof.
  move=> len onΓ onΓ' ond ond' ond''.
  move: (into_ws_equality_decls c len onΓ onΓ' ond ond') => l.
  rewrite -len in ond'.
  move: (into_ws_equality_decls c' len onΓ onΓ' ond' ond'') => r.
  apply (transitivity l r).
Qed.

Inductive wt_equality_decls {cf : checker_flags} (le : bool) (Σ : global_env_ext) (Γ Γ' : context) : context_decl -> context_decl -> Type :=
| wt_equality_vass {na na' : binder_annot name} {T T' : term} :
    isType Σ Γ T -> isType Σ Γ' T' ->
    conv_cum le Σ Γ T T' ->
    eq_binder_annot na na' ->
    wt_equality_decls le Σ Γ Γ' (vass na T) (vass na' T')
| wt_equality_vdef {na na' : binder_annot name} {b b' T T'} :
    eq_binder_annot na na' ->
    isType Σ Γ T -> isType Σ Γ' T' ->
    Σ ;;; Γ |- b : T -> Σ ;;; Γ' |- b' : T' ->
    Σ ;;; Γ |- b = b' ->
    conv_cum le Σ Γ T T' ->
    wt_equality_decls le Σ Γ Γ' (vdef na b T) (vdef na' b' T').
Derive Signature for wt_equality_decls.

Definition ws_context_equality {cf:checker_flags} (le : bool) (Σ : global_env_ext) :=
  All2_fold (ws_equality_decls le Σ).

Notation ws_cumul_context Σ := (ws_context_equality true Σ).
Notation ws_conv_context Σ := (ws_context_equality false Σ).
    
(* Slightly more convenient formulation on context equality that brings all the 
  hypotheses using Σ and subset-types instead of boolean equality reasoning. *)
Definition closed_context_equality {cf:checker_flags} (le : bool) (Σ : global_env_ext) (Γ Γ' : context) :=
  All2_fold (fun Γ Γ' d d' => 
    ∑ (clΓ : is_closed_context Γ) (clΓ' : is_closed_context Γ') 
      (cld : is_open_decl Γ d) (cld' : is_open_decl Γ d'),
      equality_open_decls le Σ (exist Γ clΓ) (exist d cld) (exist d' cld')) Γ Γ'.

Notation closed_cumul_context Σ := (closed_context_equality true Σ).
Notation closed_conv_context Σ := (closed_context_equality false Σ).

Lemma ws_context_equality_closed_right {cf:checker_flags} {le : bool} {Σ : global_env_ext} {Γ Γ'}:
  ws_context_equality le Σ Γ Γ' -> is_closed_context Γ'.
Proof.
  intros X. red in X.
  induction X; auto.
  destruct p as [? []].
  rewrite on_free_vars_ctx_snoc IHX /=.
  now move/and4P: i => [].
Qed.

Lemma ws_context_equality_closed_left {cf:checker_flags} {le : bool} {Σ : global_env_ext} {Γ Γ'}:
  ws_context_equality le Σ Γ Γ' -> is_closed_context Γ.
Proof.
  intros X. red in X.
  induction X; auto.
  destruct p as [? []].
  rewrite on_free_vars_ctx_snoc IHX /=.
  now move/and4P: i => [].
Qed.

Lemma into_closed_context_equality {cf:checker_flags} {le : bool} {Σ : global_env_ext} {wfΣ : wf Σ} 
  {Γ Γ' : context} :
  ws_context_equality le Σ Γ Γ' ->
  closed_context_equality le Σ Γ Γ'.
Proof.
  rewrite /ws_context_equality /closed_context_equality.
  intros a; eapply All2_fold_impl_ind; tea.
  clear -wfΣ; intros Γ Δ d d' wseq IH hd.
  destruct (into_ws_equality_open_decls le hd) as [clΓ [isd [isd' eq]]].
  exists clΓ. exists (ws_context_equality_closed_right wseq).
  now exists isd, isd'.
Qed.

Lemma from_closed_context_equality {cf:checker_flags} {le : bool} {Σ : global_env_ext} {wfΣ : wf Σ} 
  {Γ Γ' : context} :
  closed_context_equality le Σ Γ Γ' ->
  ws_context_equality le Σ Γ Γ'.
Proof.
  rewrite /ws_context_equality /closed_context_equality.
  intros a; eapply All2_fold_impl_ind; tea.
  clear -wfΣ; intros Γ Δ d d' wseq IH hd. cbn in hd.
  destruct hd as [clΓ [clΔ [isd [isd' eq]]]].
  rewrite /ws_equality_decls. split => //.
  apply (All2_fold_length IH). split.
  rewrite /equality_decls.
  depelim eq. destruct le; constructor; auto; now apply ws_equality_forget in w.
  apply ws_equality_forget in w. apply ws_equality_forget in w0.
  destruct le; constructor; auto.
  now rewrite clΓ clΔ isd /= -(All2_fold_length IH) isd'.
Qed.



Definition wt_context_equality {cf:checker_flags} (le : bool) (Σ : global_env_ext) :=
  All2_fold (wt_equality_decls le Σ).

Notation wt_cumul_context Σ := (wt_context_equality true Σ).
Notation wt_conv_context Σ := (wt_context_equality false Σ).

Section WtContextConversion.
  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ}.

  Definition wt_decl Γ d := 
    match d with
    | {| decl_body := None; decl_type := ty |} => isType Σ Γ ty
    | {| decl_body := Some b; decl_type := ty |} => isType Σ Γ ty × Σ ;;; Γ |- b : ty
    end.

  Lemma wf_local_All_fold Γ : 
    wf_local Σ Γ <~>
    All_fold wt_decl Γ.
  Proof.
    split.
    - induction 1; constructor; auto.
      red in t0, t1. cbn. split; auto.
    - induction 1; [constructor|].
      destruct d as [na [b|] ty]; cbn in p; constructor; intuition auto.
  Qed.

  Lemma All2_fold_All_fold_mix {P Q l l'} : 
    All2_fold P l l' ->
    All_fold Q l ->
    All_fold Q l' ->
    All2_fold (fun Γ Γ' x y => Q Γ x × Q Γ' y × P Γ Γ' x y) l l'.
  Proof.
    induction 1; [constructor|] => l r; depelim l; depelim r; constructor; auto.
  Qed.

  Lemma All2_fold_All_fold_mix_inv {P Q l l'} : 
    All2_fold (fun Γ Γ' x y => Q Γ x × Q Γ' y × P Γ Γ' x y) l l' ->
    All2_fold P l l' × All_fold Q l × All_fold Q l'.
  Proof.
    induction 1; intuition (try constructor; auto).
  Qed.

  Lemma wt_context_equality_forget {le} {Γ Γ' : context} :
    wt_context_equality le Σ Γ Γ' ->
    wf_local Σ Γ × wf_local Σ Γ' ×
    if le then cumul_context Σ Γ Γ' else conv_context Σ Γ Γ'.
  Proof.
    move=> wteq.
    apply (PCUICEnvironment.All2_fold_impl (Q:=fun Γ Γ' d d' => wt_decl Γ d × wt_decl Γ' d' × 
      (if le then cumul_decls Σ Γ Γ' d d' else conv_decls Σ Γ Γ' d d'))) in wteq.
    2:{ intros ???? []; intuition (cbn; try constructor; auto).
        all:cbn in *; destruct le; constructor; auto. }
    eapply All2_fold_All_fold_mix_inv in wteq as [wteq [wfΓ wfΓ']].
    eapply wf_local_All_fold in wfΓ. eapply wf_local_All_fold in wfΓ'.
    intuition auto.
    destruct le; auto.
  Qed.

  Lemma into_wt_context_equality {le} {Γ Γ' : context} {T U : term} :
    wf_local Σ Γ -> wf_local Σ Γ' ->
    (if le then cumul_context Σ Γ Γ' else conv_context Σ Γ Γ') ->
    wt_context_equality le Σ Γ Γ'.
  Proof.
    move=> /wf_local_All_fold wfΓ /wf_local_All_fold wfΓ'.
    destruct le=> eq.
    eapply All2_fold_All_fold_mix in eq; tea.
    eapply PCUICEnvironment.All2_fold_impl; tea; clear => Γ Γ' d d' [wtd [wtd' cum]] /=.
    destruct cum; cbn in wtd, wtd'; constructor; intuition auto.
    eapply All2_fold_All_fold_mix in eq; tea.
    eapply PCUICEnvironment.All2_fold_impl; tea; clear => Γ Γ' d d' [wtd [wtd' cum]] /=.
    destruct cum; cbn in wtd, wtd'; constructor; intuition auto.
  Qed.

  Lemma wt_ws_context_equality {le} {Γ Γ' : context} {T U : term} :
    wt_context_equality le Σ Γ Γ' ->
    ws_context_equality le Σ Γ Γ'.
  Proof.
    intros a; eapply All2_fold_impl_ind; tea.
    intros ???? wt ws []; 
    pose proof (All2_fold_length wt);
    constructor; auto. all:constructor; auto.
    2,4:rtoProp; intuition eauto using PCUICSubstitution.isType_wf_local with fvs.
    1,4:destruct le; constructor; auto.
    rewrite /on_free_vars_decl /test_decl /=. rtoProp; intuition eauto with fvs.
    eapply PCUICClosed.subject_closed in t.
    now eapply closedn_on_free_vars.
    rewrite /on_free_vars_decl /test_decl /=. rtoProp; intuition eauto with fvs.
    eapply PCUICClosed.subject_closed in t0.
    now eapply closedn_on_free_vars.
  Qed.

  Lemma ws_context_equality_split {le} {Γ Γ' : context} :
    ws_context_equality le Σ Γ Γ' ->
    on_free_vars_ctx xpred0 Γ × on_free_vars_ctx xpred0 Γ' ×
    if le then cumul_context Σ Γ Γ' else conv_context Σ Γ Γ'.
  Proof.
    move=> wteq.
    apply (PCUICEnvironment.All2_fold_impl (Q:=fun Γ Γ' d d' => ws_decl Γ d × ws_decl Γ' d' × 
      (if le then cumul_decls Σ Γ Γ' d d' else conv_decls Σ Γ Γ' d d'))) in wteq.
    2:{ intros ???? [? []].
        move/and4P: i => [].
        intuition (cbn; try constructor; auto).
        cbn in *; destruct le; auto. }
    eapply All2_fold_All_fold_mix_inv in wteq as [wteq [wfΓ wfΓ']].
    apply on_free_vars_ctx_All_fold in wfΓ; apply on_free_vars_ctx_All_fold in wfΓ'.
    intuition auto.
    destruct le; auto.
  Qed.

  Lemma ws_context_equality_red_context {le} {Γ Γ'} :
    ws_context_equality le Σ Γ Γ' ->
    ∑ Δ Δ', red_ctx Σ Γ Δ * red_ctx Σ Γ' Δ' * eq_context_upto Σ (eq_universe Σ) (if le then leq_universe Σ else eq_universe Σ) Δ Δ'.
  Proof.
    move=> /ws_context_equality_split [wfΓ [wfΓ' Hctx]].
    destruct le.
    apply (cumul_context_red_context Σ (Γ := inj_closed Γ byfvs) (Γ' := inj_closed Γ' byfvs)) in Hctx.
    now cbn in Hctx.
    apply (conv_context_red_context Σ (Γ := inj_closed Γ byfvs) (Γ' := inj_closed Γ' byfvs)) in Hctx.
    now cbn in Hctx.
  Qed.

  #[global]
  Instance ws_equality_decls_sym Γ Γ' : Symmetric (ws_equality_decls false Σ Γ Γ').
  Proof.
    move=> x y [Hlen [[na na' T T' eqan cv|na na' b b' T T' eqna eqb eqT]]] /and4P[]; 
      rewrite /ws_equality_decls => -> -> /= onx ony; intuition auto.
    1,3:constructor; auto; now symmetry.
    1,2:apply/andP; split; [rewrite ?Hlen //|rewrite -?Hlen //].
  Qed.

  Instance ws_equality_sym {Γ} : Symmetric (ws_equality false Σ Γ).
  Proof.
    move=> t u d.
    induction d.
    - constructor. cbn. now symmetry.
    - econstructor 3; tea.
    - econstructor 2; tea.
  Qed.

  #[global]
  Instance equality_open_decls_sym Γ : Symmetric (equality_open_decls false Σ Γ).
  Proof.
    move=> x y [na na' T T' eqan cv|na na' b b' T T' eqna eqb eqT];
    constructor; now symmetry.
  Qed.

  Notation " p # t " := (transport _ p t).
  Notation " p #[ P ] t " := (transport P p t) (at level 30).

  Definition move_open_decl {Γ Γ' : closed_context} (d : open_decl Γ) (p : #|Γ| = #|Γ'|) : open_decl Γ' :=
    exist (proj1_sig d) (p #[fun n => on_free_vars_decl (shiftnP n xpred0) d] proj2_sig d).

  Lemma closed_conv_conv_ctx {le} {Γ Γ' : closed_context} {d d' : open_decl Γ} :
    forall cv : conv_context Σ Γ Γ',
    equality_open_decls le Σ Γ d d' ->
    equality_open_decls le Σ Γ' (move_open_decl d (All2_fold_length cv))
                                (move_open_decl d' (All2_fold_length cv)).
  Proof.
    intros cv eq.
    destruct Γ' as [Γ' onΓ'].
    eapply (into_equality_open_decls _ Γ').
    induction eq; cbn.
    - eapply ws_equality_forget in p.
      destruct le; cbn in *; constructor => //.
      apply (cumul_conv_ctx (Γ' := exist Γ' onΓ') Σ p cv).
      apply (conv_conv_ctx (Γ' := exist Γ' onΓ') Σ p cv).
    - eapply ws_equality_forget in p.
      destruct le; cbn in *; 
      eapply ws_equality_forget in p0.
      constructor => //.
      apply (conv_conv_ctx (Γ' := exist Γ' onΓ') Σ p cv).
      apply (cumul_conv_ctx (Γ' := exist Γ' onΓ') Σ p0 cv).
      constructor => //.
      apply (conv_conv_ctx (Γ' := exist Γ' onΓ') Σ p cv).
      apply (conv_conv_ctx (Γ' := exist Γ' onΓ') Σ p0 cv).
  Qed.

  Lemma closed_cumul_conv_ctx {le} {Γ Γ' : closed_context} {d d' : open_decl Γ} :
    forall cv : cumul_context Σ Γ' Γ,
    equality_open_decls le Σ Γ d d' ->
    equality_open_decls le Σ Γ' (move_open_decl d (symmetry (All2_fold_length cv)))
                                (move_open_decl d' (symmetry (All2_fold_length cv))).
  Proof.
    intros cv eq.
    destruct Γ' as [Γ' onΓ'].
    eapply (into_equality_open_decls _ Γ').
    induction eq; cbn.
    - eapply ws_equality_forget in p.
      destruct le; cbn in *; constructor => //.
      apply (cumul_cumul_ctx (Γ' := exist Γ' onΓ') Σ p cv).
      apply (conv_cumul_ctx (Γ' := exist Γ' onΓ') Σ p cv).
    - eapply ws_equality_forget in p.
      destruct le; cbn in *; 
      eapply ws_equality_forget in p0.
      constructor => //.
      apply (conv_cumul_ctx (Γ' := exist Γ' onΓ') Σ p cv).
      apply (cumul_cumul_ctx (Γ' := exist Γ' onΓ') Σ p0 cv).
      constructor => //.
      apply (conv_cumul_ctx (Γ' := exist Γ' onΓ') Σ p cv).
      apply (conv_cumul_ctx (Γ' := exist Γ' onΓ') Σ p0 cv).
  Qed.

  Lemma closed_context_equality_forget {le Γ Γ'} : 
    closed_context_equality le Σ Γ Γ' ->
    if le then cumul_context Σ Γ Γ' else conv_context Σ Γ Γ'.
  Proof.
    induction 1. destruct le; constructor.
    destruct le. constructor; auto.
    destruct p as [cl [cl' [cld [cld' eq]]]].
    depelim eq; constructor; auto; try now eapply ws_equality_forget in w.
    now eapply ws_equality_forget in w0.
    destruct p as [cl [cl' [cld [cld' eq]]]].
    depelim eq; constructor; auto; try now eapply ws_equality_forget in w.
    constructor; auto; now apply ws_equality_forget in w.
    constructor; auto; now apply ws_equality_forget in w; apply ws_equality_forget in w0.
  Qed.
    
  Lemma All_fold_All2_fold {P Q Γ} : 
    All_fold P Γ ->
    (forall Γ d, All_fold P Γ -> All2_fold Q Γ Γ -> P Γ d -> Q Γ Γ d d) ->
    All2_fold Q Γ Γ.
  Proof.
    intros a H; induction a; constructor; auto.
  Qed.

  Lemma closed_context_equality_refl le (Γ : closed_context) : closed_context_equality le Σ Γ Γ.
  Proof.
    destruct Γ as [Γ onΓ]. cbn.
    move/on_free_vars_ctx_All_fold: onΓ => a.
    eapply (All_fold_All2_fold a). clear -wfΣ.
    move=> Γ d a IH ond.
    move/on_free_vars_ctx_All_fold: a => clΓ.
    exists clΓ, clΓ, ond, ond.
    eapply (into_equality_open_decls _ Γ).
    rewrite /equality_decls.
    destruct le. reflexivity. reflexivity.
  Qed.

  Lemma ws_context_equality_refl le (Γ : closed_context) : ws_context_equality le Σ Γ Γ.
  Proof.
    apply from_closed_context_equality, closed_context_equality_refl.
  Qed.

  #[global]
  Instance conv_context_sym : Symmetric (fun Γ Γ' => closed_conv_context Σ Γ Γ').
  Proof.
    intros Γ Γ' conv.
    eapply All2_fold_sym; tea.
    clear Γ Γ' conv. intros Γ Γ' d d' H IH [clΓ [clΓ' [opd [opd' eq]]]].
    exists clΓ', clΓ.
    unshelve eexists. rewrite -(All2_fold_length H); exact opd'.
    unshelve eexists. rewrite -(All2_fold_length H); exact opd.
    symmetry in eq. pose proof (closed_context_equality_forget H).
    eapply (closed_conv_conv_ctx X (Γ := exist Γ clΓ) (Γ' := exist Γ' clΓ')) in eq.
    eapply All_open_decls_alpha_irrel; tea. all:reflexivity.
  Qed.

  #[global]
  Instance context_equality_trans le : Transitive (fun Γ Γ' => closed_context_equality le Σ Γ Γ').
  Proof.
    eapply All2_fold_trans.
    intros.
    destruct X2 as (clΓ & clΓ' & cld & cld' & eq).
    destruct X3 as (clΓ'2 & clΓ'' & cld'2 & cld'' & eq').
    exists clΓ, clΓ'', cld.
    unshelve eexists.
    rewrite (All2_fold_length X); exact cld''.
    eapply equality_open_decls_trans; tea.
    destruct le.
    - move: (closed_context_equality_forget X) => /= cv.
      eapply (closed_cumul_conv_ctx (Γ := exist Γ' clΓ'2) (Γ' := exist Γ clΓ) cv) in eq'.
      eapply All_open_decls_alpha_irrel; tea. all:trea.
    - pose proof (conv_context_sym _ _ X). cbn in X2.
      move: (closed_context_equality_forget X2) => cv.
      eapply (closed_conv_conv_ctx (Γ := exist Γ' clΓ'2) (Γ' := exist Γ clΓ) cv) in eq'.
      eapply All_open_decls_alpha_irrel; tea. all:trea.
  Qed.

  #[global]
  Instance conv_context_trans : Transitive (closed_conv_context Σ).
  Proof. apply context_equality_trans. Qed.

  #[global]
  Instance cumul_context_trans : Transitive (closed_cumul_context Σ).
  Proof. apply context_equality_trans. Qed.

  #[global]
  Instance ws_context_equality_trans le : Transitive (ws_context_equality le Σ).
  Proof.
    intros x y z H H'.
    apply into_closed_context_equality in H.
    apply into_closed_context_equality in H'.
    apply from_closed_context_equality.
    transitivity y; tea.
  Qed.

  #[global]
  Instance ws_context_equality_sym: Symmetric (ws_conv_context Σ).
  Proof.
    move=> x y /into_closed_context_equality H.
    apply from_closed_context_equality.
    now symmetry.
  Qed.

End WtContextConversion.

Hint Resolve conv_ctx_refl' cumul_ctx_refl' : pcuic.
Hint Constructors conv_decls cumul_decls : pcuic.

Lemma eq_context_upto_conv_context {cf:checker_flags} (Σ : global_env_ext) Re :
  RelationClasses.subrelation Re (eq_universe Σ) ->
  subrelation (eq_context_upto Σ Re Re) (fun Γ Γ' => conv_context Σ Γ Γ').
Proof.
  intros HRe Γ Δ h. induction h.
  - constructor.
  - constructor; tas.
    depelim p; constructor; auto; constructor; tas;
    eapply eq_term_upto_univ_impl; tea; auto.
Qed.

Lemma eq_context_upto_cumul_context {cf:checker_flags} (Σ : global_env_ext) Re Rle :
  RelationClasses.subrelation Re (eq_universe Σ) ->
  RelationClasses.subrelation Rle (leq_universe Σ) ->
  RelationClasses.subrelation Re Rle ->
  subrelation (eq_context_upto Σ Re Rle) (fun Γ Γ' => cumul_context Σ Γ Γ').
Proof.
  intros HRe HRle hR Γ Δ h. induction h.
  - constructor.
  - constructor; tas.
    depelim p; constructor; auto; constructor; tas.
    eapply eq_term_upto_univ_impl. 5:eauto. all:tea. 
    now transitivity Rle. auto.
    eapply eq_term_upto_univ_impl; eauto.
    eapply eq_term_upto_univ_impl. 5:eauto. all:tea. 
    now transitivity Rle. auto.
Qed.

Instance eq_subrel_eq_univ {cf:checker_flags} Σ : RelationClasses.subrelation eq (eq_universe Σ).
Proof. intros x y []. reflexivity. Qed.

Lemma eq_context_upto_empty_conv_context {cf:checker_flags} (Σ : global_env_ext) :
  subrelation (eq_context_upto [] eq eq) (fun Γ Γ' => conv_context Σ Γ Γ').
Proof.
  intros Γ Δ h. induction h.
  - constructor.
  - constructor; tas.
    depelim p; constructor; auto; constructor.
    all:eapply eq_term_upto_univ_empty_impl; tea; try typeclasses eauto.
Qed.

Lemma eq_context_upto_univ_conv_context {cf:checker_flags} {Σ : global_env_ext} Γ Δ :
    eq_context_upto Σ.1 (eq_universe Σ) (eq_universe Σ) Γ Δ ->
    conv_context Σ Γ Δ.
Proof.
  intros h. eapply eq_context_upto_conv_context; tea.
  reflexivity.
Qed.

Lemma eq_context_upto_univ_cumul_context {cf:checker_flags} {Σ : global_env_ext} Γ Δ :
    eq_context_upto Σ.1 (eq_universe Σ) (leq_universe Σ) Γ Δ ->
    cumul_context Σ Γ Δ.
Proof.
  intros h. eapply eq_context_upto_cumul_context; tea.
  reflexivity. tc. tc.
Qed.

Lemma conv_context_app_same {cf:checker_flags} Σ Γ Γ' Δ :
  conv_context Σ Γ Γ' ->
  conv_context Σ (Γ ,,, Δ) (Γ' ,,, Δ).
Proof.
  intros HΔ.
  induction Δ; auto.
  destruct a as [na [b|] ty]; constructor; auto;
    constructor; reflexivity.
Qed.

Lemma cumul_context_app_same {cf:checker_flags} Σ Γ Γ' Δ :
  cumul_context Σ Γ Γ' ->
  cumul_context Σ (Γ ,,, Δ) (Γ' ,,, Δ).
Proof.
  intros HΔ.
  induction Δ; auto.
  destruct a as [na [b|] ty]; constructor; auto;
    constructor; reflexivity.
Qed.

Hint Extern 4 (eq_term_upto_univ _ _ _ _ _) => reflexivity : pcuic.

Axiom fix_guard_context_cumulativity : forall {cf:checker_flags} Σ Γ Γ' mfix,
  cumul_context Σ Γ' Γ ->
  fix_guard Σ Γ mfix ->
  fix_guard Σ Γ' mfix.

Axiom cofix_guard_context_cumulativity : forall {cf:checker_flags} Σ Γ Γ' mfix,
  cumul_context Σ Γ' Γ ->
  cofix_guard Σ Γ mfix ->
  cofix_guard Σ Γ' mfix.

(* Definition on_decl (P : context -> term -> term -> Type)
             (Γ : context) (t : term) (t' : option term) :=
    match t' with
    | Some (b, b') => (P Γ b b' * P Γ Γ' t t')%type
    | None => P Γ Γ' t t'
    end. *)
Definition on_local_decl (P : context -> term -> option term -> Type) (Γ : context) (d : context_decl) :=
  match decl_body d with
  | Some b => P Γ b (Some (decl_type d)) * P Γ (decl_type d) None
  | None => P Γ (decl_type d) None
  end.

Lemma nth_error_All_local_env {P Γ n} (isdecl : n < #|Γ|) :
  All_local_env P Γ ->
  on_some (on_local_decl P (skipn (S n) Γ)) (nth_error Γ n).
Proof.
  induction 1 in n, isdecl |- *. red; simpl.
  - destruct n; simpl; inv isdecl.
  - destruct n. red; simpl. red. simpl. apply t0.
    simpl. apply IHX. simpl in isdecl. lia.
  - destruct n; simpl in *.
    * rewrite skipn_S skipn_0. red; cbn.
      split; auto.
    * rewrite !skipn_S. apply IHX. lia.
Qed.

Lemma context_cumulativity_wf_app {cf:checker_flags} Σ Γ Γ' Δ : 
  cumul_context Σ Γ' Γ ->
  wf_local Σ Γ' ->
    All_local_env
       (lift_typing
          (fun (Σ : global_env_ext) (Γ : context) (t T : term) =>
           forall Γ' : context,
           cumul_context Σ Γ' Γ -> wf_local Σ Γ' -> Σ;;; Γ' |- t : T) Σ)
       (Γ,,, Δ) ->
  wf_local Σ (Γ' ,,, Δ).
Proof.
  intros.
  eapply wf_local_app => //.
  eapply All_local_env_app_inv in X1 as [].
  eapply All_local_env_impl_ind; tea => /=.
  rewrite /lift_typing => Γ'' t' [t wf IH|wf [s IH]]; try exists s; eauto; red.
  eapply IH. eapply All2_fold_app => //.
  eapply All2_fold_refl. intros. eapply cumul_decls_refl.
  eapply All_local_env_app; split; auto.
  eapply IH. 
  eapply All2_fold_app => //.
  eapply All2_fold_refl. intros. eapply cumul_decls_refl.
  eapply All_local_env_app; split; auto.
Qed.

Lemma closed_cumul_context_closed_left {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ'} {le} : 
  closed_context_equality le Σ Γ' Γ -> is_closed_context Γ'.
Proof.
  move/from_closed_context_equality; apply ws_context_equality_closed_left.
Qed.

Lemma closed_cumul_context_closed_right {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ'} {le} : 
  closed_context_equality le Σ Γ' Γ -> is_closed_context Γ.
Proof.
  move/from_closed_context_equality; apply ws_context_equality_closed_right.
Qed.

Lemma is_closed_context_cumul_app Γ Δ Γ' : 
  is_closed_context (Γ ,,, Δ) ->
  is_closed_context Γ' ->
  #|Γ| = #|Γ'| ->
  is_closed_context (Γ' ,,, Δ).
Proof.
  rewrite !on_free_vars_ctx_app => /andP[] onΓ onΔ onΓ' <-.
  now rewrite onΓ' onΔ.
Qed.

Lemma on_free_vars_decl_eq n m d :
  on_free_vars_decl (shiftnP n xpred0) d ->
  n = m ->
  on_free_vars_decl (shiftnP m xpred0) d.
Proof.
  now intros o ->.
Qed.

Hint Extern 4 (is_true (on_free_vars_decl (shiftnP _ xpred0) _)) =>
  eapply on_free_vars_decl_eq; [eassumption|len; lia] : fvs.

Lemma closed_conv_context_forget {cf} {Σ} {wfΣ : wf Σ} {Γ Γ'} : 
  closed_conv_context Σ Γ Γ' -> conv_context Σ Γ Γ'.
Proof.
  apply: closed_context_equality_forget.
Qed.

Lemma closed_cumul_context_forget {cf} {Σ} {wfΣ : wf Σ} {Γ Γ'} : 
  closed_cumul_context Σ Γ Γ' -> cumul_context Σ Γ Γ'.
Proof.
  apply: closed_context_equality_forget.
Qed.

Lemma ws_conv_cumul_ctx {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ' : closed_context} 
  {T U : open_term Γ} :
  Σ;;; Γ |-ws T = U -> closed_cumul_context Σ Γ' Γ -> Σ;;; Γ' |- T = U.
Proof.
  move/ws_equality_forget => conv convctx.
  eapply conv_cumul_ctx in conv; tea.
  now apply closed_cumul_context_forget.
Qed.

Ltac exass H := 
  match goal with
  |- ∑ x : ?A, _ => 
    assert (H : A); [idtac|exists H]
  end.


Lemma into_ws_context_equality {cf:checker_flags} {le : bool} {Σ : global_env_ext} {wfΣ : wf Σ} 
  {Γ Γ' : context} :
  is_closed_context Γ ->
  is_closed_context Γ' ->
  (if le then cumul_context Σ Γ Γ' else conv_context Σ Γ Γ') ->
  ws_context_equality le Σ Γ Γ'.
Proof.
  rewrite /ws_context_equality.
  move/on_free_vars_ctx_All_fold => onΓ.
  move/on_free_vars_ctx_All_fold => onΓ'.
  destruct le.
  { intros cum.
    eapply All2_fold_All_fold_mix in cum; tea.
    eapply All2_fold_impl_ind; tea. clear.
    cbn; intros. red. rewrite (All2_fold_length X); split=> //.
    eapply All2_fold_All_fold_mix_inv in X as [cum [onΓ onΔ]].
    move/on_free_vars_ctx_All_fold: onΓ => ->.
    move/on_free_vars_ctx_All_fold: onΔ => ->.
    rewrite -(All2_fold_length X0); intuition rtoProp; intuition auto.
    rewrite (All2_fold_length X0) //. }
  { intros cum.
    eapply All2_fold_All_fold_mix in cum; tea.
    eapply All2_fold_impl_ind; tea. clear.
    cbn; intros. red. rewrite (All2_fold_length X); split=> //.
    eapply All2_fold_All_fold_mix_inv in X as [cum [onΓ onΔ]].
    move/on_free_vars_ctx_All_fold: onΓ => ->.
    move/on_free_vars_ctx_All_fold: onΔ => ->.
    rewrite -(All2_fold_length X0); intuition rtoProp; intuition auto.
    rewrite (All2_fold_length X0) //. }
Qed.

Lemma closed_cumul_context_app_same {cf} {Σ} {wfΣ : wf Σ} {Γ Γ' Δ : context} :
  is_closed_context (Γ ,,, Δ) ->
  closed_cumul_context Σ Γ Γ' -> closed_cumul_context Σ (Γ,,, Δ) (Γ',,, Δ).
Proof.
  move=> iscl cum.
  eapply into_closed_context_equality, into_ws_context_equality => //.
  eapply is_closed_context_cumul_app; tea.
  now eapply closed_cumul_context_closed_right.
  now rewrite (All2_fold_length cum).
  apply cumul_context_app_same.
  now apply closed_cumul_context_forget.
Qed.

Lemma context_cumulativity_app {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Γ' Δ Δ'} : 
  closed_cumul_context Σ Γ' Γ ->
  closed_conv_context Σ (Γ ,,, Δ) (Γ ,,, Δ') ->
  closed_conv_context Σ (Γ' ,,, Δ) (Γ' ,,, Δ').
Proof.
  intros cum conv.
  pose proof (length_of conv). len in H.
  eapply All2_fold_app; eauto. lia. 
  eapply (closed_context_equality_refl _ (exist Γ' (closed_cumul_context_closed_left cum))).
  eapply All2_fold_app_inv in conv as []. 2:lia.
  eapply All2_fold_impl_ind; tea.
  intros. simpl in X1.
  pose proof (All2_fold_length cum).
  destruct X1 as (clΓ & clΓ' & cld & cld' & eq).
  exass clΓ'Γ0.
  { pose proof (closed_cumul_context_closed_left cum).
    eapply is_closed_context_cumul_app; tea; lia. }
  exass clΓ'Δ0.
  { pose proof (closed_cumul_context_closed_left cum).
    eapply is_closed_context_cumul_app; tea; abstract lia. }
  unshelve eexists; [abstract eauto with fvs|].
  unshelve eexists; [abstract eauto with fvs|].
  eapply (into_equality_open_decls _ (Γ' ,,, Δ0)).
  set (clΓΓ0 := exist (Γ ,,, Γ0) clΓ) in *.
  depelim eq; constructor; auto;
   unshelve eapply (ws_conv_cumul_ctx (Γ' := exist (Γ' ,,, Γ0) byfvs)) in w; cbn; tea;
    try eapply closed_cumul_context_app_same => //.
  unshelve eapply (ws_conv_cumul_ctx (Γ' := exist (Γ' ,,, Γ0) byfvs)) in w0; cbn; tea;
    try eapply closed_cumul_context_app_same => //.
Qed.

Notation open_context Γ := (ws_context (shiftnP #|Γ| xpred0)).

Lemma weakening_cumul0 {cf:checker_flags} {Σ} {wfΣ : wf Σ} {Γ : closed_context} {Γ'' : open_context Γ}
  {M N : open_term Γ} n :
  n = #|Γ''| ->
  Σ ;;; Γ |- M <= N ->
  Σ ;;; Γ ,,, Γ'' |- lift0 n M <= lift0 n N.
Proof. intros; subst. apply (weakening_cumul (Γ':= [])); tea; eauto with fvs. Qed.

Lemma split_closed_context {Γ : context} (n : nat) : 
  is_closed_context Γ ->
  n <= #|Γ| ->
  ∑ (Δ : closed_context) (Δ' : open_context Δ), 
    (Δ = skipn n Γ :> context) ×
    (Δ' = firstn n Γ :> context) ×
    (Γ = Δ ,,, Δ') ×
    n = #|Δ'|.
Proof.
  rewrite -{1}(firstn_skipn n Γ).
  rewrite on_free_vars_ctx_app => /andP[] sk fi.
  exists (exist (skipn n Γ) sk).
  exists (exist (firstn n Γ) fi). intuition auto.
  cbn. now rewrite firstn_skipn. cbn.
  rewrite List.firstn_length. lia.
Qed.

Lemma context_cumulativity_prop {cf:checker_flags} :
  env_prop
    (fun Σ Γ t T =>
       forall Γ', cumul_context Σ Γ' Γ -> wf_local Σ Γ' -> Σ ;;; Γ' |- t : T)
    (fun Σ Γ => 
    All_local_env
      (lift_typing (fun Σ (Γ : context) (t T : term) =>
        forall Γ' : context, cumul_context Σ Γ' Γ -> wf_local Σ Γ' -> Σ;;; Γ' |- t : T) Σ) Γ).
Proof.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; intros **; rename_all_hyps;
    try solve [econstructor; eauto].

  - induction X; constructor; auto.
    destruct tu as [s Hs]. exists s; eauto.
    destruct tu as [s Hs]. exists s; eauto.

  - pose proof heq_nth_error.
    eapply (All2_fold_nth_r X0) in H as [d' [Hnth [Hrel Hconv]]].
    unshelve eapply nth_error_All_local_env in X; tea. 2:eapply nth_error_Some_length in heq_nth_error; lia.
    rewrite heq_nth_error /= in X.
    destruct decl as [na [b|] ty] => /=.
    + red in X. cbn in X. destruct X as [Hb Hty].
      destruct Hty as [s Hty]. specialize (Hty _ Hrel).
      forward Hty by now eapply All_local_env_skipn.
      eapply type_Cumul with _ s.
      * econstructor. auto. eauto.
      * rewrite -(firstn_skipn (S n) Γ').
        change (tSort s) with (lift0 (S n) (tSort s)).
        eapply weakening_length. auto.
        rewrite firstn_length_le. eapply nth_error_Some_length in Hnth. lia. auto.
        now rewrite /app_context firstn_skipn.
        assumption.
      * depelim Hconv; simpl in *.
        destruct (split_closed_context (S n) (wf_local_closed_context X1)) as [Δ [Δ' [eqΔ [eqΔ' [-> hn]]]]].
        eapply nth_error_Some_length in Hnth. lia.
        rewrite -eqΔ in Hty, Hrel.
        rewrite -eqΔ in c0, c.
        assert (is_open_term Δ T).
        { rewrite nth_error_app_lt in Hnth. rewrite -hn. lia.
          destruct Δ' as [Δ' hΔ']. cbn in *.
          move: hΔ'.
          rewrite -on_free_vars_ctx_on_ctx_free_vars -[shiftnP _ _]addnP0 => hΔ'.
          eapply nth_error_on_free_vars_ctx in hΔ'; tea.
          2:{ rewrite shiftnP_add /shiftnP /= orb_false_r. apply Nat.ltb_lt. lia. }
          rewrite /test_decl /= in hΔ'. move/andP: hΔ' => [] _.
          now rewrite hn addnP_shiftnP. }
        eapply PCUICClosed.subject_closed in Hty.
        eapply (@closedn_on_free_vars xpred0) in Hty.
        eapply (weakening_cumul0 (Γ := Δ) (Γ'' := Δ') (M := exist T H) (N := exist ty Hty)); cbn. lia.
        exact c0.
    + cbn in X. destruct X as [s ondecl].
      specialize (ondecl _ Hrel).
      depelim Hconv.
      forward ondecl by now eapply All_local_env_skipn.
      eapply type_Cumul with _ s.
      * econstructor. auto. eauto.
      * rewrite -(firstn_skipn (S n) Γ').
        change (tSort s) with (lift0 (S n) (tSort s)).
        eapply weakening_length. auto.
        rewrite firstn_length_le. eapply nth_error_Some_length in Hnth. lia. auto.
        now rewrite /app_context firstn_skipn.
        assumption.
      * destruct (split_closed_context (S n) (wf_local_closed_context X1)) as [Δ [Δ' [eqΔ [eqΔ' [-> hn]]]]].
        eapply nth_error_Some_length in Hnth. lia.
        rewrite -eqΔ in ondecl, Hrel.
        rewrite -eqΔ in c.
        assert (is_open_term Δ T).
        { rewrite nth_error_app_lt in Hnth. rewrite -hn. lia.
          destruct Δ' as [Δ' hΔ']. cbn in *.
          move: hΔ'.
          rewrite -on_free_vars_ctx_on_ctx_free_vars -[shiftnP _ _]addnP0 => hΔ'.
          eapply nth_error_on_free_vars_ctx in hΔ'; tea.
          2:{ rewrite shiftnP_add /shiftnP /= orb_false_r. apply Nat.ltb_lt. lia. }
          rewrite /test_decl /= in hΔ'. move: hΔ'.
          now rewrite hn addnP_shiftnP. }
        eapply PCUICClosed.subject_closed in ondecl.
        eapply (@closedn_on_free_vars xpred0) in ondecl.
        eapply (weakening_cumul0 (Γ := Δ) (Γ'' := Δ') (M := exist T H) (N := exist ty ondecl)); cbn. lia.
        exact c.
  - constructor; pcuic.
    eapply forall_Γ'0. repeat (constructor; pcuic).
    constructor; auto. red. eexists; eapply forall_Γ'; auto.
  - econstructor; pcuic.
    eapply forall_Γ'0; repeat (constructor; pcuic).
  - econstructor; pcuic.
    eapply forall_Γ'1; repeat (constructor; pcuic).
  - econstructor; eauto.
    * eapply context_cumulativity_wf_app; tea.
    * eapply IHp0. rewrite /predctx.
      eapply All2_fold_app => //. eapply All2_fold_refl; reflexivity.
      eapply context_cumulativity_wf_app; tea.
    * revert X6.
      clear -Γ' X10 X11. induction 1; constructor; eauto.
    * eapply All2i_impl; tea => i cdecl br. cbv beta.
      set (brctxty := case_branch_type _ _ _ _ _ _ _ _). cbn.
      move=> [] hbctx [] ihbctxty [] hbody [] IHbody [] hbty IHbty.
      intuition eauto; solve_all.
      eapply context_cumulativity_wf_app; tea.
      eapply IHbody. eapply All2_fold_app => //. eapply All2_fold_refl; reflexivity.
      eauto using context_cumulativity_app, context_cumulativity_wf_app.
      eapply IHbty.
      eapply All2_fold_app => //. eapply All2_fold_refl; reflexivity.
      eapply context_cumulativity_wf_app; tea.
  - econstructor. eapply fix_guard_context_cumulativity; eauto.
    all:pcuic.
    eapply (All_impl X0).
    intros x [s [Hs IH]].
    exists s; eauto.
    eapply (All_impl X1).
    intros x [Hs IH].
    eapply IH.
    now apply cumul_context_app_same.
    eapply (All_mfix_wf); auto.
    apply (All_impl X0); simpl.
    intros x' [s [Hs' IH']]. exists s.
    eapply IH'; auto.
  - econstructor.
    eapply cofix_guard_context_cumulativity; eauto.
    all:pcuic.
    + eapply (All_impl X0).
      intros x [s [Hs IH]].
      exists s; eauto.
    + eapply (All_impl X1).
      intros x [Hs IH].
      eapply IH.
      now apply cumul_context_app_same.
      eapply (All_mfix_wf); auto.
      apply (All_impl X0); simpl.
      intros x' [s [Hs' IH']]. exists s.
      eapply IH'; auto.
    
  - econstructor; eauto.
    eapply PCUICClosed.type_closed in typet.
    eapply PCUICClosed.subject_closed in typeB.
    eapply (@closedn_on_free_vars xpred0) in typet.
    eapply (@closedn_on_free_vars xpred0) in typeB.
    eapply wf_local_closed_context in wfΓ. eapply wf_local_closed_context in X6.
    unshelve epose proof (cumul_cumul_ctx Σ (Γ := exist Γ byfvs) (Γ' := exist Γ' byfvs) 
      (T := exist A byfvs) (U := exist B byfvs)); eauto; cbn.
Qed.

Lemma context_cumulativity {cf:checker_flags} {Σ} {wfΣ : wf Σ.1} Γ {t T Γ'} :
    Σ ;;; Γ |- t : T ->
    wf_local Σ Γ' ->
    cumul_context Σ Γ' Γ ->
    Σ ;;; Γ' |- t : T.
Proof.
  intros h hΓ' e.
  eapply context_cumulativity_prop; eauto.
Qed.

Hint Resolve wf_local_closed_context : fvs.

Lemma wf_conv_context_closed {cf:checker_flags} {Σ} {wfΣ : wf Σ.1} {Γ Γ'} :
  conv_context Σ Γ Γ' -> 
  wf_local Σ Γ ->
  wf_local Σ Γ' ->
  closed_conv_context Σ Γ Γ'.
Proof.
  move=> a wf wf'.
  eapply into_closed_context_equality.
  eapply into_ws_context_equality; eauto with fvs.
Qed.

Lemma wf_cumul_context_closed {cf:checker_flags} {Σ} {wfΣ : wf Σ.1} {Γ Γ'} :
  cumul_context Σ Γ Γ' -> 
  wf_local Σ Γ ->
  wf_local Σ Γ' ->
  closed_cumul_context Σ Γ Γ'.
Proof.
  move=> a wf wf'.
  eapply into_closed_context_equality.
  eapply into_ws_context_equality; eauto with fvs.
Qed.

Lemma context_conversion {cf:checker_flags} {Σ} {wfΣ : wf Σ.1} Γ {t T Γ'} :
  Σ ;;; Γ |- t : T ->
  wf_local Σ Γ' ->
  conv_context Σ Γ Γ' ->
  Σ ;;; Γ' |- t : T.
Proof.
  intros h hΓ' e.
  eapply wf_conv_context_closed in e; eauto with fvs pcuic.
  apply conv_context_sym in e; auto.
  eapply closed_context_equality_forget in e.
  apply conv_cumul_context in e.
  eapply context_cumulativity; eauto.
Qed.
