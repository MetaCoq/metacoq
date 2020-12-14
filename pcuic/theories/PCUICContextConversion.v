(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst
     PCUICLiftSubst PCUICTyping PCUICWeakening
     PCUICCumulativity PCUICReduction
     PCUICParallelReduction PCUICEquality PCUICUnivSubstitution
     PCUICParallelReductionConfluence PCUICConfluence.

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

#[global]
Hint Resolve conv_refl' : pcuic.
Arguments skipn : simpl never.

(* TODO move *)
Lemma weakening_cumul0 `{CF:checker_flags} Σ Γ Γ'' M N n :
  wf Σ.1 -> n = #|Γ''| ->
  Σ ;;; Γ |- M <= N ->
  Σ ;;; Γ ,,, Γ'' |- lift0 n M <= lift0 n N.
Proof. intros; subst; now apply (weakening_cumul _ _ []). Qed.

#[global]
Hint Constructors red1 : pcuic.
#[global]
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

  Lemma All2_local_env_over_red_refl {Γ Δ} :
    All2_local_env (on_decl (fun (Δ _ : context) (t u : term) => red Σ (Γ ,,, Δ) t u)) Δ Δ.
  Proof. induction Δ as [|[na [b|] ty]]; econstructor; try red; auto. Qed.

  Lemma All2_local_env_red_refl {Δ} :
    All2_local_env (on_decl (fun (Δ _ : context) (t u : term) => red Σ Δ t u)) Δ Δ.
  Proof. induction Δ as [|[na [b|] ty]]; econstructor; try red; auto. Qed.

  Derive Signature for assumption_context.

  Lemma red1_red_ctxP_ass {Γ Γ' Δ} : assumption_context Δ ->
    red1_red_ctxP Γ Γ' ->
    red1_red_ctxP (Γ ,,, Δ) (Γ' ,,, Δ).
  Proof.
    induction Δ as [|[na [b|] ty] Δ]; intros; auto.
    - elimtype False. depelim H. 
    - case; move => n b b' //. eapply IHΔ. now depelim H. apply X.
  Qed.

  Ltac t := split; [eapply red1_red; try econstructor; eauto|try constructor]; eauto with pcuic.
  Ltac u := intuition eauto with pcuic.

  Lemma red1_red_ctx_aux {Γ Γ' T U} :
    red1 Σ Γ T U ->
    @red_ctx Σ Γ Γ' ->
    red1_red_ctxP Γ Γ' ->
    ∑ t, red Σ Γ' T t * red Σ Γ' U t.
  Proof.
    intros r H. revert Γ' H.
    simpl in *. induction r using red1_ind_all; intros; auto with pcuic;
     try solve [eexists; t]; try destruct (IHr _ H) as [? [? ?]]; auto.

    - pose proof H.
      eapply nth_error_pred1_ctx_l in H as [body' [? ?]]; eauto.
      rewrite -(firstn_skipn (S i) Γ').
      assert (i < #|Γ'|). destruct (nth_error Γ' i) eqn:Heq; noconf e. eapply nth_error_Some_length in Heq. lia.
      move: (All2_local_env_length H0) => Hlen.
      specialize (X _ _ _ H1 e). forward X. eapply All2_local_env_app.
      instantiate (1 := firstn (S i) Γ').
      instantiate (1 := firstn (S i) Γ).
      rewrite [_ ,,, _](firstn_skipn (S i) _).
      now rewrite [_ ,,, _](firstn_skipn (S i) _).
      rewrite !skipn_length; try lia.

      destruct X as [x' [bt b't]]. exists (lift0 (S i) x').
      split; eauto with pcuic.
      etransitivity. eapply red1_red. constructor.
      rewrite firstn_skipn. eauto.
      eapply weakening_red_0; eauto. rewrite firstn_length_le //.
      eapply weakening_red_0; eauto. rewrite firstn_length_le //.

    - exists (tLambda na x N). split; apply red_abs; auto.

    - destruct (IHr (Γ' ,, vass na N)). constructor; pcuic.
      case => n b b' /= //. apply X.
      exists (tLambda na N x). split; apply red_abs; u.

    - exists (tLetIn na x t b'). split; eapply red_letin; auto.
    - specialize (IHr (Γ' ,, vdef na b t)).
      forward IHr. constructor; eauto. red. eauto.
      destruct IHr as [? [? ?]].
      case. move=> b0 b1 [] <- [] <- H'. exists b; auto.
      apply X.
      exists (tLetIn na b t x). split; eapply red_letin; auto.
    - exists (tCase ind x c brs). u; now apply red_case_p.
    - exists (tCase ind p x brs). u; now apply red_case_c.
    - eapply (OnOne2_exist _ (on_Trel_eq (red Σ Γ') snd fst))  in X.
      destruct X as [brs'' [? ?]].
      eexists. split; eapply red_case_one_brs; eauto.
      intros. intuition eauto.
      destruct (b1 _ H X0) as [? [? ?]].
      eexists (x.1, x0); intuition eauto.
    - exists (tProj p x). u; now eapply red_proj_c.
    - exists (tApp x M2). u; now eapply red_app.
    - exists (tApp M1 x). u; now eapply red_app.
    - exists (tProd na x M2). u; now eapply red_prod.
    - specialize (IHr (Γ' ,, vass na M1)) as [? [? ?]].
      constructor; pcuic. case => //.
      exists (tProd na M1 x). u; now eapply red_prod.
    - eapply (OnOne2_exist _ (red Σ Γ')) in X.
      destruct X as [rl [l0 l1]].
      eexists; split; eapply red_evar; eauto.
      eapply OnOne2_All2; eauto.
      eapply OnOne2_All2; eauto.
      simpl; intros.
      intuition eauto.
    - eapply (OnOne2_exist _ (on_Trel_eq (red Σ Γ') dtype (fun x => (dname x, dbody x, rarg x)))) in X.
      destruct X as [mfix' [l r]].
      exists (tFix mfix' idx); split; eapply red_fix_ty.
      eapply OnOne2_All2; intuition eauto; intuition.
      eapply OnOne2_All2; intuition eauto; intuition.
      intuition auto.
      destruct (b0 _ H X0) as [d' [r0 r1]].
      refine (existT _ {| dtype := d' |} _); simpl; eauto.
    - assert (fix_context mfix0 = fix_context mfix1).
      { rewrite /fix_context /mapi. generalize 0 at 2 4.
        induction X. destruct p. simpl. intuition congruence.
        intros. specialize (IHX (S n)). simpl. congruence. }
      eapply (OnOne2_exist _ (on_Trel_eq (red Σ (Γ' ,,, fix_context mfix0)) dbody (fun x => (dname x, dtype x, rarg x)))) in X.
      destruct X as [mfix' [l r]].
      exists (tFix mfix' idx); split; eapply red_fix_body.
      eapply OnOne2_All2; intuition eauto; intuition.
      eapply OnOne2_All2; intuition eauto; intuition. congruence.
      intros.
      intuition auto.
      specialize (b0 (Γ' ,,, fix_context mfix0)). forward b0.
      eapply All2_local_env_app_inv. apply H. apply All2_local_env_over_red_refl.
      forward b0. eapply red1_red_ctxP_ass. apply fix_context_assumption_context. auto.
      destruct b0 as [t [? ?]].
      refine (existT _ {| dbody := t |} _); simpl; eauto.
    - eapply (OnOne2_exist _ (on_Trel_eq (red Σ Γ') dtype (fun x => (dname x, dbody x, rarg x)))) in X.
      destruct X as [mfix' [l r]].
      exists (tCoFix mfix' idx); split; eapply red_cofix_ty.
      eapply OnOne2_All2; intuition eauto; intuition.
      eapply OnOne2_All2; intuition eauto; intuition.
      intuition auto.
      destruct (b0 _ H X0) as [d' [r0 r1]].
      refine (existT _ {| dtype := d' |} _); simpl; eauto.
    - assert (fix_context mfix0 = fix_context mfix1).
      { rewrite /fix_context /mapi. generalize 0 at 2 4.
        induction X. destruct p. simpl. intuition congruence.
        intros. specialize (IHX (S n)). simpl. congruence. }
      eapply (OnOne2_exist _ (on_Trel_eq (red Σ (Γ' ,,, fix_context mfix0)) dbody (fun x => (dname x, dtype x, rarg x)))) in X.
      destruct X as [mfix' [l r]].
      exists (tCoFix mfix' idx); split; eapply red_cofix_body.
      eapply OnOne2_All2; intuition eauto; intuition.
      eapply OnOne2_All2; intuition eauto; intuition. congruence.
      intros.
      intuition auto.
      specialize (b0 (Γ' ,,, fix_context mfix0)). forward b0.
      eapply All2_local_env_app_inv. apply H. apply All2_local_env_over_red_refl.
      forward b0. eapply red1_red_ctxP_ass. apply fix_context_assumption_context. auto.
      destruct b0 as [t [? ?]].
      refine (existT _ {| dbody := t |} _); simpl; eauto.
  Qed.

  Lemma red_red_ctx' {Γ Γ' T U} :
    red Σ Γ T U ->
    @red_ctx Σ Γ Γ' ->
    red1_red_ctxP Γ Γ' ->
    ∑ t, red Σ Γ' T t * red Σ Γ' U t.
  Proof.
    intros r rc rP. induction r.
    - eapply red1_red_ctx_aux; eauto.
    - exists x; split; auto.
    - destruct IHr1 as [xl [redl redr]].
      destruct IHr2 as [xr [redl' redr']].
      destruct (red_confluence wfΣ redr redl').
      destruct p.
      exists x0. split; [transitivity xl|transitivity xr]; auto.
  Qed.

  Lemma red_red_ctx_aux' {Γ Γ'} :
    @red_ctx Σ Γ Γ' -> red1_red_ctxP Γ Γ'.
  Proof.
    intros X.
    induction Γ in Γ', X |- *.
    - depelim X.
      intros n t t'. rewrite nth_error_nil //.
    - depelim X; red in o.
      + specialize (IHΓ _ X).
        case => n b b' /= //.
        simpl. apply IHΓ.
      + specialize (IHΓ _ X).
        destruct o.
        case.
        * move=> b0 b1 [] <- [] <- H.
          rewrite skipn_S /skipn /= in H.
          eapply red_red_ctx' in H; eauto.
        * simpl. eapply IHΓ.
  Qed.

  Lemma red_red_ctx {Γ Γ' T U} :
    red Σ Γ T U ->
    @red_ctx Σ Γ Γ' ->
    ∑ t, red Σ Γ' T t * red Σ Γ' U t.
  Proof.
    intros. eapply red_red_ctx', red_red_ctx_aux'; eauto.
  Qed.

End ContextReduction.

Section ContextConversion.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context {wfΣ : wf Σ}.

  Notation conv_context Γ Γ' := (context_relation (conv_decls Σ) Γ Γ').
  Notation cumul_context Γ Γ' := (context_relation (cumul_decls Σ) Γ Γ').

  Global Instance conv_ctx_refl : Reflexive (context_relation (conv_decls Σ)).
  Proof.
    intro Γ; induction Γ; try econstructor.
    destruct a as [na [b|] ty]; econstructor; eauto;
      constructor; pcuic.
  Qed.

  Global Instance cumul_ctx_refl : Reflexive (context_relation (cumul_decls Σ)).
  Proof.
    intro Γ; induction Γ; try econstructor.
    destruct a as [na [b|] ty]; econstructor; eauto;
      constructor; pcuic; eapply cumul_refl'.
  Qed.

  Definition conv_ctx_refl' Γ : conv_context Γ Γ
  := conv_ctx_refl Γ.

  Definition cumul_ctx_refl' Γ : cumul_context Γ Γ
    := cumul_ctx_refl Γ.

  Hint Resolve conv_ctx_refl' cumul_ctx_refl' : pcuic.

  Lemma fill_le {Γ t t' u u'} :
    leq_term Σ.1 Σ t u -> red Σ Γ t t' -> red Σ Γ u u' ->
    ∑ t'' u'', red Σ Γ t' t'' * red Σ Γ u' u'' * leq_term Σ Σ t'' u''.
  Proof.
    intros tu tt' uu'.
    pose proof tu as tu2.
    eapply red_eq_term_upto_univ_l in tu; try exact tt'; tc.
    destruct tu as [u'' [uu'' t'u'']].
    destruct (red_confluence wfΣ uu' uu'') as [unf [ul ur]].
    eapply red_eq_term_upto_univ_r in t'u''; try exact ur; tc.
    destruct t'u'' as [t'' [t't'' t''unf]].
    exists t'', unf. intuition auto.
  Qed.

  Lemma fill_eq {Γ t t' u u'} :
    eq_term Σ.1 Σ t u -> red Σ Γ t t' -> red Σ Γ u u' ->
    ∑ t'' u'', red Σ Γ t' t'' * red Σ Γ u' u'' * eq_term Σ.1 Σ t'' u''.
  Proof.
    intros tu tt' uu'.
    pose proof tu as tu2.
    eapply red_eq_term_upto_univ_l in tu; try exact tt'; tc.
    destruct tu as [u'' [uu'' t'u'']].
    destruct (red_confluence wfΣ uu' uu'') as [unf [ul ur]].
    eapply red_eq_term_upto_univ_r in t'u''; try exact ur; tc.
    destruct t'u'' as [t'' [t't'' t''unf]].
    exists t'', unf. intuition auto.
  Qed.

  Lemma cumul_red_ctx Γ Γ' T U :
    Σ ;;; Γ |- T <= U ->
    red_ctx Σ Γ Γ' ->
    Σ ;;; Γ' |- T <= U.
  Proof.
    intros H Hctx.
    apply cumul_alt in H as [v [v' [[redl redr] leq]]].
    destruct (red_red_ctx Σ wfΣ redl Hctx) as [lnf [redl0 redr0]].
    apply cumul_alt.
    eapply red_eq_term_upto_univ_l in leq; tea; tc.
    destruct leq as [? [? ?]].
    destruct (red_red_ctx _ wfΣ redr Hctx) as [rnf [redl1 redr1]].
    destruct (red_confluence wfΣ r redr1). destruct p.
    edestruct (red_eq_term_upto_univ_r Σ (eq_universe_leq_universe _) e r0) as [lnf' [? ?]].
    exists lnf', x0. intuition auto. now transitivity lnf.
    now transitivity rnf.
  Qed.

  Lemma cumul_red_ctx_inv Γ Γ' T U :
    Σ ;;; Γ |- T <= U ->
    @red_ctx Σ Γ' Γ ->
    Σ ;;; Γ' |- T <= U.
  Proof.
    intros H Hctx.
    apply cumul_alt in H as [v [v' [[redl redr] leq]]].
    pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ redl Hctx).
    pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ redr Hctx).
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

  Lemma red_eq_context_upto_l {R Re Γ Δ u v}
        `{RelationClasses.Reflexive _ R} `{RelationClasses.Transitive _ R} `{SubstUnivPreserving R}
        `{RelationClasses.Reflexive _ Re} `{RelationClasses.Transitive _ Re} `{SubstUnivPreserving Re}
        `{RelationClasses.subrelation _ Re R} :
    red Σ Γ u v ->
    eq_context_upto Σ Re R Γ Δ ->
    ∑ v',
    red Σ Δ u v' *
    eq_term_upto_univ Σ Re Re v v'.
  Proof.
    intros r HΓ. induction r.
    - eapply (red1_eq_context_upto_l _ R) in r; eauto.
      destruct r as [v [? ?]]. exists v. intuition pcuic.
    - exists x. split; auto. reflexivity.
    - destruct IHr1 as [v' [? ?]].
      destruct IHr2 as [v'' [? ?]].
      unshelve eapply (red_eq_term_upto_univ_l Σ _ (u:=y) (v:=v'') (u':=v')) in e; tc. all:pcuic.
      destruct e as [? [? ?]].
      exists x0; split; eauto.
      now transitivity v'.
      eapply eq_term_upto_univ_trans with v''; auto.
  Qed.

  Lemma red_eq_context_upto_r {R Re Γ Δ u v}
        `{RelationClasses.Equivalence _ Re} `{SubstUnivPreserving Re}
        `{RelationClasses.PreOrder _ R} `{SubstUnivPreserving R}
        `{RelationClasses.subrelation _ Re R} :
    red Σ Δ u v ->
    eq_context_upto Σ Re R Γ Δ ->
    ∑ v',
    red Σ Γ u v' *
    eq_term_upto_univ Σ Re Re v v'.
  Proof.
    intros r HΓ. induction r.
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

  Lemma cumul_trans_red_leqterm {Γ t u v} :
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
    destruct (red_confluence wfΣ redr redl') as [unf [nfl nfr]].
    eapply red_eq_term_upto_univ_r in eq; tc;eauto with pcuic.
    destruct eq as [t1 [red'0 eq2]].
    eapply red_eq_term_upto_univ_l in eq'; tc;eauto with pcuic.
    destruct eq' as [v1 [red'1 eq1]].
    exists t1, unf, v1.
    repeat split.
    transitivity t0; auto.
    transitivity u0; auto.
    transitivity v0; auto. eapply eq2. eapply eq1.
  Qed.

  Lemma conv_eq_context_upto {Γ Δ T U} :
    eq_context_upto Σ (eq_universe Σ) (eq_universe Σ) Γ Δ ->
    Σ ;;; Γ |- T = U ->
    Σ ;;; Δ |- T = U.
  Proof.
    intros eqctx cum.
    eapply conv_alt_red in cum as [nf [nf' [[redl redr] ?]]].
    eapply (red_eq_context_upto_l (R:=eq_universe _) (Re:=eq_universe _)) in redl; tea.
    eapply (red_eq_context_upto_l (R:=eq_universe _) (Re:=eq_universe _)) in redr; tea.
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
     eapply eq_term_upto_univ_impl. 5:eauto. all:(tc || auto).
     transitivity Re'; auto.
     eapply eq_term_upto_univ_impl. 5:eauto. all:(tc || auto).
     eapply eq_term_upto_univ_impl. 5:eauto. all:(tc || auto).
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

  Lemma conv_alt_red_ctx {Γ Γ' T U} :
    Σ ;;; Γ |- T = U ->
    @red_ctx Σ Γ Γ' ->
    Σ ;;; Γ' |- T = U.
  Proof.
    intros H Hctx.
    eapply conv_alt_red in H. apply conv_alt_red.
    destruct H as [T' [U' [[redv redv'] leqvv']]].
    eapply red_red_ctx in redv; eauto.
    eapply red_red_ctx in redv'; eauto.
    destruct redv as [Tj [redTj redT'j]].
    destruct redv' as [Uj [redUUj redU'j]].
    destruct (fill_eq leqvv' redT'j redU'j) as [Tnf [Unf [[redTnf redUnf] eqnf]]].
    exists Tnf, Unf; intuition eauto.
    now transitivity Tj.
    now transitivity Uj.
  Qed.

  Lemma conv_alt_red_ctx_inv Γ Γ' T U :
    Σ ;;; Γ |- T = U ->
    red_ctx Σ Γ' Γ ->
    Σ ;;; Γ' |- T = U.
  Proof.
    intros H Hctx.
    apply conv_alt_red in H as [v [v' [[redl redr] leq]]].
    pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ redl Hctx).
    pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ redr Hctx).
    apply conv_alt_red.
    exists v, v'.
    split. pcuic. auto.
  Qed.
  
  Lemma cumul_alt_red_ctx {Γ Γ' T U} :
    Σ ;;; Γ |- T <= U ->
    @red_ctx Σ Γ Γ' ->
    Σ ;;; Γ' |- T <= U.
  Proof.
    intros H Hctx.
    eapply cumul_alt in H. apply cumul_alt.
    destruct H as [T' [U' [[redv redv'] leqvv']]].
    eapply red_red_ctx in redv; eauto.
    eapply red_red_ctx in redv'; eauto.
    destruct redv as [Tj [redTj redT'j]].
    destruct redv' as [Uj [redUUj redU'j]].
    destruct (fill_le leqvv' redT'j redU'j) as [Tnf [Unf [[redTnf redUnf] eqnf]]].
    exists Tnf, Unf; intuition eauto.
    now transitivity Tj.
    now transitivity Uj.
  Qed.

  Lemma cumul_alt_red_ctx_inv Γ Γ' T U :
    Σ ;;; Γ |- T <= U ->
    red_ctx Σ Γ' Γ ->
    Σ ;;; Γ' |- T <= U.
  Proof.
    intros H Hctx.
    apply cumul_alt in H as [v [v' [[redl redr] leq]]].
    pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ redl Hctx).
    pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ redr Hctx).
    apply cumul_alt.
    exists v, v'.
    split. pcuic. auto.
  Qed.

  Lemma cumul_context_red_context Γ Γ' :
    cumul_context Γ Γ' ->
    ∑ Δ Δ', red_ctx Σ Γ Δ * red_ctx Σ Γ' Δ' * eq_context_upto Σ (eq_universe Σ) (leq_universe Σ) Δ Δ'.
  Proof.
    intros Hctx.
    induction Hctx.
    - exists [], []; intuition pcuic. constructor.
    - destruct IHHctx as [Δ [Δ' [[? ?] ?]]].
      depelim p.
      pose proof (cumul_alt_red_ctx c r).
      eapply cumul_alt in X.
      destruct X as [T' [U' [[? ?] ?]]].
      pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ r1 r).
      pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ r2 r).
      destruct (red_eq_context_upto_l r1 e0). destruct p.
      destruct (red_eq_context_upto_l r2 e0). destruct p.
      exists (Δ ,, vass na' T'), (Δ' ,, vass na' x0).
      split; [split|]; constructor; auto.
      + red.
        eapply PCUICConfluence.red_red_ctx; eauto.
      + eapply eq_term_upto_univ_trans with U'; eauto; tc.
        now apply eq_term_leq_term.
    - destruct IHHctx as [Δ [Δ' [[? ?] ?]]].
      depelim p.
      pose proof (conv_alt_red_ctx c r).
      eapply conv_alt_red in X.
      destruct X as [t' [u' [[? ?] ?]]].
      pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ r1 r).
      pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ r2 r).
      destruct (red_eq_context_upto_l r1 e0) as [t'' [? ?]].
      destruct (red_eq_context_upto_l r2 e0) as [u'' [? ?]].
      pose proof (cumul_alt_red_ctx c0 r) as hTU.
      eapply cumul_alt in hTU.
      destruct hTU as [T' [U' [[rT rU] eTU']]].
      pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ rT r).
      pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ rU r).
      destruct (red_eq_context_upto_l rT e0) as [T'' [? ?]].
      destruct (red_eq_context_upto_l rU e0) as [U'' [? ?]].
      exists (Δ ,, vdef na' t' T'), (Δ' ,, vdef na' u'' U'').
      split; [split|]. all: constructor ; auto.
      * red. split; auto.
      * red. split.
        -- eapply PCUICConfluence.red_red_ctx; eauto.
        -- eapply PCUICConfluence.red_red_ctx; eauto.
      * eapply eq_term_upto_univ_trans with u'; eauto; tc.
      * transitivity U'; eauto. now apply eq_term_leq_term.
  Qed.

  Lemma conv_context_red_context Γ Γ' :
    conv_context Γ Γ' ->
    ∑ Δ Δ', red_ctx Σ Γ Δ * red_ctx Σ Γ' Δ' * eq_context_upto Σ (eq_universe Σ) (eq_universe Σ) Δ Δ'.
  Proof.
    intros Hctx.
    induction Hctx.
    - exists [], []; intuition pcuic. constructor.
    - destruct IHHctx as [Δ [Δ' [[? ?] ?]]].
      depelim p.
      pose proof (conv_alt_red_ctx c r).
      eapply conv_alt_red in X.
      destruct X as [T' [U' [[? ?] ?]]].
      pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ r1 r).
      pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ r2 r).
      destruct (red_eq_context_upto_l r1 e0). destruct p.
      destruct (red_eq_context_upto_l r2 e0). destruct p.
      exists (Δ ,, vass na' T'), (Δ' ,, vass na' x0).
      split; [split|]; constructor; auto.
      + red.
        eapply PCUICConfluence.red_red_ctx; eauto.
      + eapply eq_term_upto_univ_trans with U'; eauto; tc.
    - destruct IHHctx as [Δ [Δ' [[? ?] ?]]].
      depelim p.
      pose proof (conv_alt_red_ctx c r).
      eapply conv_alt_red in X.
      destruct X as [t' [u' [[? ?] ?]]].
      pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ r1 r).
      pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ r2 r).
      destruct (red_eq_context_upto_l r1 e0) as [t'' [? ?]].
      destruct (red_eq_context_upto_l r2 e0) as [u'' [? ?]].
      pose proof (conv_alt_red_ctx c0 r) as hTU.
      eapply conv_alt_red in hTU.
      destruct hTU as [T' [U' [[rT rU] eTU']]].
      pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ rT r).
      pose proof (PCUICConfluence.red_red_ctx wfΣ _ _ _ _ rU r).
      destruct (red_eq_context_upto_l rT e0) as [T'' [? ?]].
      destruct (red_eq_context_upto_l rU e0) as [U'' [? ?]].
      exists (Δ ,, vdef na' t' T'), (Δ' ,, vdef na' u'' U'').
      split; [split|]. all: constructor ; auto.
      * red. split; auto.
      * red. split.
        -- eapply PCUICConfluence.red_red_ctx; eauto.
        -- eapply PCUICConfluence.red_red_ctx; eauto.
      * eapply eq_term_upto_univ_trans with u'; eauto; tc.
      * transitivity U'; eauto.
  Qed.

  Lemma conv_cumul_ctx Γ Γ' T U :
    Σ ;;; Γ |- T = U ->
    cumul_context Γ' Γ ->
    Σ ;;; Γ' |- T = U.
  Proof.
    intros H Hctx.
    apply cumul_context_red_context in Hctx => //.
    destruct Hctx as [Δ [Δ' [[l r] elr]]].
    eapply conv_alt_red_ctx in r. 2:eauto.
    eapply conv_alt_red_ctx_inv in l; eauto.
    eapply conv_leq_context_upto; eauto.
  Qed.
  
  Lemma conv_conv_ctx Γ Γ' T U :
    Σ ;;; Γ |- T = U ->
    conv_context Γ Γ' ->
    Σ ;;; Γ' |- T = U.
  Proof.
    intros H Hctx.
    apply conv_context_red_context in Hctx => //.
    destruct Hctx as [Δ [Δ' [[l r] elr]]].
    eapply conv_alt_red_ctx in l. 2:eauto.
    eapply conv_alt_red_ctx_inv in r; eauto.
    eapply conv_eq_context_upto; eauto.
  Qed.

  Lemma cumul_conv_ctx Γ Γ' T U :
    Σ ;;; Γ |- T <= U ->
    conv_context Γ Γ' ->
    Σ ;;; Γ' |- T <= U.
  Proof.
    intros H Hctx.
    apply conv_context_red_context in Hctx => //.
    destruct Hctx as [Δ [Δ' [[l r] elr]]].
    eapply cumul_alt_red_ctx in l. 2:eauto.
    eapply cumul_alt_red_ctx_inv in r; eauto.
    eapply cumul_eq_context_upto; eauto.
  Qed.

  Lemma conv_cumul_context {Γ Δ} : 
    conv_context Γ Δ -> cumul_context Γ Δ.
  Proof.
    induction 1; constructor; auto;
    depelim p; constructor; auto; now apply conv_cumul.
  Qed.
  Hint Resolve conv_cumul_context : pcuic.

  #[global]
  Instance conv_context_sym : Symmetric (fun Γ Γ' => conv_context Γ Γ').
  Proof.
    intros Γ Γ'.
    induction Γ in Γ' |- *; try econstructor.
    intros conv; depelim conv; econstructor; eauto;
    constructor; pcuic. intros.
    depelim X; constructor; pcuic.
    - depelim c. constructor. now symmetry.
      eapply conv_sym. eapply conv_conv_ctx; eauto.
    - depelim c; constructor; auto. now symmetry.
      eapply conv_sym, conv_conv_ctx; eauto.
      eapply conv_sym, conv_conv_ctx; eauto.
  Qed.

  Lemma cumul_cumul_ctx Γ Γ' T U :
    Σ ;;; Γ |- T <= U ->
    cumul_context Γ' Γ ->
    Σ ;;; Γ' |- T <= U.
  Proof.
    intros H Hctx.
    apply cumul_context_red_context in Hctx => //.
    destruct Hctx as [Δ [Δ' [[l r] elr]]].
    eapply cumul_red_ctx in r. 2:eauto.
    eapply cumul_red_ctx_inv in l; eauto.
    eapply cumul_leq_context_upto; eauto.
  Qed.

  (** Again, this is only the case because conversion is untyped *)
  Local Remark cumul_cumul_ctx_inv Γ Γ' T U :
    Σ ;;; Γ |- T <= U ->
    cumul_context Γ Γ' ->
    Σ ;;; Γ' |- T <= U.
  Proof.
    intros H Hctx. 
    apply cumul_context_red_context in Hctx => //.
    destruct Hctx as [Δ [Δ' [[l r] elr]]].
    eapply cumul_red_ctx_inv in r; eauto.
    eapply cumul_red_ctx in l; eauto.
    eapply cumul_leq_context_upto_inv; eauto.
  Qed.

End ContextConversion.

Notation conv_context Σ Γ Γ' := (context_relation (conv_decls Σ) Γ Γ').
Notation cumul_context Σ Γ Γ' := (context_relation (cumul_decls Σ) Γ Γ').

#[global]
Hint Resolve conv_ctx_refl' : pcuic.

(* Lemma wf_local_conv_ctx {cf:checker_flags} Σ Γ Δ (wfΓ : wf_local Σ Γ) : wf Σ -> *)
(*   All_local_env_over typing *)
(*     (fun (Σ : global_env_ext) (Γ : context) wfΓ (t T : term) Ht => *)
(*        forall Γ' : context, conv_context Σ Γ Γ' -> Σ;;; Γ' |- t : T) Σ Γ wfΓ -> *)
(*   conv_context Σ Γ Δ -> wf_local Σ Δ. *)
(* Proof. *)
(*   intros wfΣ wfredctx. revert Δ. *)
(*   induction wfredctx; intros Δ wfred; unfold vass, vdef in *; depelim wfred. *)
(*   - constructor; eauto. *)
(*   - simpl. constructor. auto. red. depelim c. apply i. *)
(*   - simpl. depelim c. constructor; auto; hnf. *)
(*     eapply type_Cumul; eauto. eapply cumul_conv_ctx; eauto. *)
(*     eapply conv_alt_conv in c; auto. apply c. *)
(*     constructor; auto. *)
(* Qed. *)

Hint Constructors conv_decls : pcuic.

(* Hint Resolve conv_ctx_refl' cumul_ctx_refl' : pcuic. *)
(* Hint Constructors conv_decls cumul_decls : pcuic. *)

Lemma eq_context_upto_conv_context {cf:checker_flags} (Σ : global_env_ext) Re :
  RelationClasses.subrelation Re (eq_universe Σ) ->
  subrelation (eq_context_upto Σ Re Re) (fun Γ Γ' => conv_context Σ Γ Γ').
Proof.
  intros HRe Γ Δ h. induction h.
  - constructor.
  - constructor; tas.
    constructor; tas. eapply conv_refl.
    eapply eq_term_upto_univ_impl; tea. auto.
  - constructor; tas.
    constructor; tas. eapply conv_refl.
    eapply eq_term_upto_univ_impl; tea. auto.
    eapply conv_refl.
    eapply eq_term_upto_univ_impl => //; tea.
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
    constructor; tas. eapply cumul_refl.
    eapply eq_term_upto_univ_impl. 5:eauto. all:tea. now transitivity Rle. auto.
  - constructor; tas.
    constructor; tas. eapply conv_refl.
    eapply eq_term_upto_univ_impl. 5:eauto. all:tea. auto.
    eapply cumul_refl.
    eapply eq_term_upto_univ_impl => //; tea.
    now transitivity Rle.
Qed.

Instance eq_subrel_eq_univ {cf:checker_flags} Σ : RelationClasses.subrelation eq (eq_universe Σ).
Proof. intros x y []. reflexivity. Qed.

Lemma eq_context_upto_empty_conv_context {cf:checker_flags} (Σ : global_env_ext) :
  subrelation (eq_context_upto [] eq eq) (fun Γ Γ' => conv_context Σ Γ Γ').
Proof.
  intros Γ Δ h. induction h.
  - constructor.
  - constructor; tas.
    constructor; tas. eapply conv_refl.
    eapply eq_term_upto_univ_empty_impl; tea; try typeclasses eauto.
  - constructor; tas.
    constructor; tas. eapply conv_refl.
    eapply eq_term_upto_univ_empty_impl; tea; try typeclasses eauto.
    eapply conv_refl.
    eapply eq_term_upto_univ_empty_impl; tea; try typeclasses eauto.
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

Lemma context_cumulativity_prop {cf:checker_flags} :
  env_prop
    (fun Σ Γ t T =>
       forall Γ', cumul_context Σ Γ' Γ -> wf_local Σ Γ' -> Σ ;;; Γ' |- t : T)
    (fun Σ Γ wfΓ => 
    All_local_env_over typing
    (fun (Σ : global_env_ext) (Γ : context) (_ : wf_local Σ Γ) (t T : term) (_ : Σ;;; Γ |- t : T) =>
     forall Γ' : context, cumul_context Σ Γ' Γ -> wf_local Σ Γ' -> Σ;;; Γ' |- t : T) Σ Γ wfΓ).
Proof.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; intros **; rename_all_hyps;
    try solve [econstructor; eauto].

  - auto.

  - pose proof heq_nth_error.
    eapply (context_relation_nth_r X0) in H as [d' [Hnth [Hrel Hconv]]].
    unshelve eapply nth_error_All_local_env_over in X. 3:eapply heq_nth_error.
    destruct X as [onctx ondecl].
    destruct lookup_wf_local_decl. red in ondecl.
    destruct decl as [na [b|] ty] => /=.
    + specialize ondecl as [Hb Hty].
      simpl in Hty. specialize (Hty _ Hrel).
      forward Hty by now eapply All_local_env_skipn.
      eapply type_Cumul with _ o.2.π1.
      * econstructor. auto. eauto.
      * rewrite -(firstn_skipn (S n) Γ').
        change (tSort o.2.π1) with (lift0 (S n) (tSort o.2.π1)).
        eapply weakening_length. auto.
        rewrite firstn_length_le. eapply nth_error_Some_length in Hnth. lia. auto.
        now rewrite /app_context firstn_skipn.
        assumption.
      * depelim Hconv; simpl in *.
        rewrite -(firstn_skipn (S n) Γ').
        eapply weakening_cumul0; auto.
        pose proof (nth_error_Some_length Hnth).
        rewrite firstn_length_le; lia.
    + specialize (ondecl _ Hrel).
      depelim Hconv.
      forward ondecl by now eapply All_local_env_skipn.
      eapply type_Cumul with _ o.π1.
      * econstructor. auto. eauto.
      * rewrite -(firstn_skipn (S n) Γ').
        change (tSort o.π1) with (lift0 (S n) (tSort o.π1)).
        eapply weakening_length. auto.
        rewrite firstn_length_le. eapply nth_error_Some_length in Hnth. lia. auto.
        now rewrite /app_context firstn_skipn.
        assumption.
      * rewrite -(firstn_skipn (S n) Γ').
        eapply weakening_cumul0; auto.
        pose proof (nth_error_Some_length Hnth).
        rewrite firstn_length_le; lia.
  - constructor; pcuic.
    eapply forall_Γ'0. repeat (constructor; pcuic).
    constructor; auto. red. eexists; eapply forall_Γ'; auto.
  - econstructor; pcuic.
    eapply forall_Γ'0; repeat (constructor; pcuic).
  - econstructor; pcuic.
    eapply forall_Γ'1; repeat (constructor; pcuic).
  - econstructor; pcuic. intuition auto. eapply isdecl. eapply isdecl.
    eauto. solve_all.
    destruct b0 as [? [? ?]]; eauto.
  - econstructor; pcuic.
    eapply (All_impl X0).
    intros x [s [Hs IH]].
    exists s; eauto.
    eapply (All_impl X1).
    intros x [[Hs Hl] IH]. split; auto.
    eapply IH.
    now apply cumul_context_app_same.
    eapply (All_mfix_wf); auto.
    apply (All_impl X0); simpl.
    intros x' [s [Hs' IH']]. exists s.
    eapply IH'; auto.
  - econstructor; pcuic.
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
    
  - econstructor; eauto.
    eapply cumul_cumul_ctx; eauto.
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

Lemma context_conversion {cf:checker_flags} {Σ} {wfΣ : wf Σ.1} Γ {t T Γ'} :
    Σ ;;; Γ |- t : T ->
    wf_local Σ Γ' ->
    conv_context Σ Γ Γ' ->
    Σ ;;; Γ' |- t : T.
Proof.
  intros h hΓ' e.
  apply conv_context_sym in e; auto.
  apply conv_cumul_context in e.
  eapply context_cumulativity; eauto.
Qed.
