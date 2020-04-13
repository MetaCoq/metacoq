(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool List Program Lia.
From MetaCoq.Template Require Import config monad_utils utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICTyping PCUICWeakening
     PCUICCumulativity PCUICEquality
     PCUICContextConversion PCUICValidity.
Derive Signature for red.
Import MonadNotation.

Local Set Keyed Unification.
Set Equations With UIP.


Section Alpha.
  Context {cf:checker_flags}.

  Lemma build_branches_type_eq_term :
    forall p p' ind mdecl idecl pars u brtys,
      eq_term_upto_univ eq eq p p' ->
      map_option_out
        (build_branches_type ind mdecl idecl pars u p) =
      Some brtys ->
      ∑ brtys',
        map_option_out
          (build_branches_type ind mdecl idecl pars u p') =
        Some brtys' ×
        All2 (on_Trel_eq (eq_term_upto_univ eq eq) snd fst) brtys brtys'.
  Proof.
    intros p p' ind mdecl idecl pars u brtys e hb.
    unfold build_branches_type in *.
    destruct idecl as [ina ity ike ict ipr]. simpl in *.
    unfold mapi in *. revert hb.
    generalize 0 at 3 6.
    intros n hb.
    induction ict in brtys, n, hb |- *.
    - cbn in *. eexists. split.
      + eassumption.
      + apply All2_same. intros [m t]. simpl. split ; now auto.
    - cbn. cbn in hb.
      lazymatch type of hb with
      | match ?t with _ => _ end = _ =>
        case_eq (t) ;
          try (intro bot ; rewrite bot in hb ; discriminate hb)
      end.
      intros [m t] e'. rewrite e' in hb.
      destruct a as [[na ta] ar].
      lazymatch type of e' with
      | match ?expr with _ => _ end = _ =>
        case_eq (expr) ;
          try (intro bot ; rewrite bot in e' ; discriminate e')
      end.
      intros ty ety. rewrite ety in e'.
      case_eq (decompose_prod_assum [] ty). intros sign ccl edty.
      rewrite edty in e'.
      case_eq (chop (ind_npars mdecl) (snd (decompose_app ccl))).
      intros paramrels args ech. rewrite ech in e'.
      inversion e'. subst. clear e'.
      lazymatch type of hb with
      | match ?t with _ => _ end = _ =>
        case_eq (t) ;
          try (intro bot ; rewrite bot in hb ; discriminate hb)
      end.
      intros tl etl. rewrite etl in hb.
      inversion hb. subst. clear hb.
      edestruct IHict as [brtys' [eq' he]].
      + eauto.
      + eexists. rewrite eq'. split.
        * reflexivity.
        * constructor ; auto.
          simpl. split ; auto.
          eapply eq_term_upto_univ_it_mkProd_or_LetIn ; auto.
          eapply eq_term_upto_univ_mkApps.
          -- eapply eq_term_upto_univ_lift. assumption.
          -- apply All2_same. intro. apply eq_term_upto_univ_refl ; auto.
  Qed.

  (* TODO MOVE *)
  Lemma wf_local_nth_error_vass :
    forall Σ Γ i na ty,
      wf Σ.1 ->
      wf_local Σ Γ ->
      nth_error Γ i = Some (vass na ty) ->
      lift_typing typing Σ Γ (lift0 (S i) ty) None.
  Proof.
    intros Σ Γ i na ty hΣ hΓ e. simpl.
    induction i in Γ, hΓ, e |- *.
    - destruct Γ. 1: discriminate.
      simpl in e. apply some_inj in e. subst.
      inversion hΓ. subst. simpl in X0.
      destruct X0 as [s h].
      exists s. unfold PCUICTerm.tSort.
      change (tSort s) with (lift0 1 (tSort s)).
      eapply PCUICWeakening.weakening with (Γ' := [ vass na ty ]).
      all: assumption.
    - destruct Γ. 1: discriminate.
      simpl in e.
      specialize IHi with (2 := e).
      destruct IHi as [s h].
      + inversion hΓ. all: auto.
      + exists s.
        unfold PCUICTerm.tSort. (* TODO Why do I have to do this? *)
        change (tSort s) with (lift0 1 (lift0 (S i) (tSort s))).
        rewrite simpl_lift0.
        eapply PCUICWeakening.weakening with (Γ' := [ c ]).
        all: assumption.
  Qed.

  (* TODO MOVE *)
  Lemma fix_context_nth_error :
    forall m i d,
      nth_error m i = Some d ->
      nth_error (fix_context m) (#|m| - S i) =
      Some (vass (dname d) (lift0 i (dtype d))).
  Proof.
    intros m i d e.
    rewrite <- fix_context_length.
    unfold fix_context. rewrite List.rev_length.
    rewrite <- nth_error_rev.
    - rewrite nth_error_mapi. rewrite e. simpl. reflexivity.
    - rewrite mapi_length.
      eauto using nth_error_Some_length.
  Qed.

  (* TODO MOVE *)
  Lemma nth_error_weak_context :
    forall Γ Δ i d,
      nth_error Δ i = Some d ->
      nth_error (Γ ,,, Δ) i = Some d.
  Proof.
    intros Γ Δ i d h.
    rewrite nth_error_app_lt.
    - assumption.
    - apply nth_error_Some_length in h. assumption.
  Qed.

  (* TODO MOVE *)
  Lemma Forall2_eq :
    forall A (l l' : list A),
      Forall2 eq l l' ->
      l = l'.
  Proof.
    intros A l l' h.
    induction h.
    - reflexivity.
    - f_equal. all: auto.
  Qed.

Lemma All2_trans' {A B C}
      (P : A -> B -> Type) (Q : B -> C -> Type) (R : A -> C -> Type)
      (H : forall x y z, P x y × Q y z -> R x z) {l1 l2 l3}
  : All2 P l1 l2 -> All2 Q l2 l3 -> All2 R l1 l3.
Proof.
  induction 1 in l3 |- *.
  - inversion 1; constructor.
  - inversion 1; subst. constructor; eauto.
Qed.


  Lemma typing_alpha :
    forall Σ Γ u v A,
      wf Σ.1 ->
      Σ ;;; Γ |- u : A ->
      eq_term_upto_univ eq eq u v ->
      Σ ;;; Γ |- v : A.
  Proof.
    assert (tm :
      env_prop (fun Σ Γ u A =>
                  forall v,
                    eq_term_upto_univ eq eq u v ->
                    Σ ;;; Γ |- v : A)
              (fun Σ Γ wfΓ => wf_local Σ Γ)
    ).
    eapply typing_ind_env.
    all: intros Σ wfΣ Γ wfΓ.
    - auto.
    - intros n decl hnth ih v e.
      dependent destruction e.
      eapply type_Rel ; eassumption.
    - intros l ih hl v e.
      dependent destruction e. subst.
      eapply type_Sort; assumption.
    - intros na A B s1 s2 ih hA ihA hB ihB v e.
      dependent destruction e.
      econstructor.
      + eapply ihA. assumption.
      + eapply context_conversion'.
        * assumption.
        * constructor. 1: assumption.
          simpl. eexists. eapply ihA. assumption.
        * eapply ihB. assumption.
        * constructor.
          -- apply conv_ctx_refl ; auto.
          -- constructor. constructor.
             eapply upto_names_impl_eq_term. assumption.
    - intros na A t s1 B ih hA ihA hB ihB v e.
      dependent destruction e.
      econstructor.
      + econstructor.
        * eapply ihA. assumption.
        * eapply context_conversion'.
          -- assumption.
          -- constructor. 1: assumption.
             simpl. eexists. eapply ihA. assumption.
          -- eapply ihB. assumption.
          -- constructor.
             ++ apply conv_ctx_refl ; auto.
             ++ do 2 constructor.
                eapply upto_names_impl_eq_term. assumption.
      + eapply validity_term ; eauto.
        econstructor ; eauto.
      + constructor.
        eapply eq_term_leq_term.
        apply eq_term_sym.
        constructor.
        all: try (eapply upto_names_impl_eq_term ; assumption).
        all: eapply eq_term_refl.
    - intros na b B t s1 A ih hB ihB hb ihb hA ihA v e.
      dependent destruction e.
      econstructor.
      + econstructor.
        * eapply ihB. assumption.
        * econstructor.
          -- eapply ihb. assumption.
          -- right. eexists. eapply ihB. assumption.
          -- constructor. eapply eq_term_leq_term.
             eapply upto_names_impl_eq_term. assumption.
        * eapply context_conversion'.
          -- assumption.
          -- constructor.
             ++ assumption.
             ++ simpl. eexists. eapply ihB. assumption.
             ++ simpl. eapply type_Cumul.
                ** eapply ihb. assumption.
                ** right. eexists. eapply ihB. assumption.
                ** eapply cumul_refl.
                   eapply eq_term_upto_univ_impl. 3: eassumption.
                   all: intros x ? [].
                   --- eapply eq_universe_refl.
                   --- eapply leq_universe_refl.
          -- eapply ihA. assumption.
          -- constructor.
             ++ apply conv_ctx_refl ; auto.
             ++ econstructor. constructor.
                now apply upto_names_impl_eq_term.
                constructor.
                now apply upto_names_impl_eq_term.
      + eapply validity_term ; eauto.
        econstructor ; eauto.
      + constructor.
        eapply eq_term_leq_term.
        apply eq_term_sym.
        constructor.
        all: try (eapply upto_names_impl_eq_term ; assumption).
        all: eapply eq_term_refl.
    - intros t na A B u ih ht iht hu ihu v e.
      dependent destruction e.
      econstructor.
      + econstructor.
        * eapply iht. assumption.
        * eapply ihu. assumption.
      + eapply validity_term ; eauto.
        econstructor ; eauto.
      + constructor.
        eapply eq_term_leq_term.
        apply eq_term_sym.
        eapply upto_names_impl_eq_term.
        eapply eq_term_upto_univ_subst ; now auto.
    - intros cst u decl ? ? hdecl hcons v e.
      dependent destruction e.
      apply Forall2_eq in r. apply map_inj in r ; revgoals.
      { apply Universe.make_inj. }
      subst.
      constructor ; auto.
    - intros ind u mdecl idecl isdecl ? ? hcons v e.
      dependent destruction e.
      apply Forall2_eq in r. apply map_inj in r ; revgoals.
      { apply Universe.make_inj. }
      subst.
      econstructor ; eauto.
    - intros ind i u mdecl idecl cdecl isdecl ? ? ? v e.
      dependent destruction e.
      apply Forall2_eq in r. apply map_inj in r ; revgoals.
      { apply Universe.make_inj. }
      subst.
      econstructor ; eauto.
    - intros ind u npar p c brs args mdecl idecl isdecl X X0 H pars ps pty
             Hcpt X1 X2 H1 X3 X4 btys Hbbt Hbrs v e.
      (* intros ind u npar p c brs args mdecl idecl isdecl X X0 H pars pty X1 *)
      (*        indctx pctx ps btys htc H1 H2 ihp hc ihc ihbrs v e. *)
      dependent destruction e.
      (* eapply types_of_case_eq_term in htc as htc' ; eauto. *)
      (* destruct htc' as [btys' [ebtys' he]]. *)
      econstructor.
      + eapply build_branches_type_eq_term in Hbbt; tea.
        destruct Hbbt as [btys' [Hbbt1 Hbbt2]].
        econstructor; tea; eauto.
        unshelve eapply All2_trans'; [..|eassumption].
        * exact (fun br bty : nat × term =>
                   (((br.1 = bty.1 × Σ;;; Γ |- br.2 : bty.2)
                       × (forall v : term, upto_names' br.2 v -> Σ;;; Γ |- v : bty.2))
                      × Σ;;; Γ |- bty.2 : tSort ps)
                     × (forall v : term, upto_names' bty.2 v -> Σ;;; Γ |- v : tSort ps)).
        * clear. intros x y z X; rdest; cbn in *.
          congruence. 2: eauto. econstructor; tea. 
          right. exists ps. eauto. constructor.
          now eapply upto_names_impl_leq_term.
        * eapply All2_trans'; [..|eassumption].
          2: apply All2_sym; tea.
          clear. intros x y z X; rdest; cbn in *; eauto. congruence.
          intros v H. unshelve eapply (upto_names_trans _ _ _ _) in H; tea.
          eauto.
      + eapply validity_term ; eauto.
        instantiate (1 := tCase (ind, npar) p c brs).
        econstructor ; eauto.
        apply All2_prod_inv in Hbrs as [a1 a4].
        apply All2_prod_inv in a1 as [a1 a3].
        apply All2_prod_inv in a1 as [a1 a2].
        apply All2_prod. all: assumption.
      + constructor.
        eapply eq_term_leq_term.
        apply eq_term_sym.
        eapply eq_term_mkApps.
        all: try (eapply upto_names_impl_eq_term ; assumption).
        eapply All2_app.
        * eapply All2_same. intro. eapply eq_term_refl.
        * constructor ; eauto.
          eapply upto_names_impl_eq_term. assumption.
    - intros p c u mdecl idecl pdecl isdecl args X X0 hc ihc H ty v e.
      dependent destruction e.
      econstructor.
      + econstructor. all: try eassumption.
        eapply ihc. assumption.
      + eapply validity_term ; eauto.
        econstructor ; eauto.
      + constructor.
        eapply eq_term_leq_term.
        apply eq_term_sym.
        eapply upto_names_impl_eq_term.
        eapply eq_term_upto_univ_substs ; auto; try reflexivity.
        * constructor ; auto.
          eapply All2_same.
          intro. eapply eq_term_upto_univ_refl ; auto.
    - intros mfix n decl types hguard hnth hwf ihmfix ihmfixb v e.
      dependent destruction e.
      eapply All2_nth_error_Some in hnth as hnth' ; eauto.
      destruct hnth' as [decl' [hnth' hh]].
      destruct hh as [[ety ebo] era].
      assert (hwf' : wf_local Σ (Γ ,,, fix_context mfix')).
      { apply PCUICWeakening.All_mfix_wf; auto.
        eapply (All2_All_mix_left ihmfix) in a.
        clear -a.
        induction a; constructor; simpl; auto.
        destruct r as [[s [Hs IH]] [[eqty eqbod] eqrarg]].
        exists s; apply IH; eauto. }
      assert (convctx : conv_context Σ (Γ ,,, fix_context mfix) (Γ ,,, fix_context mfix')).
      { eapply eq_context_upto_univ_conv_context.
        eapply (eq_context_impl eq). intros x y eqx. subst. reflexivity. 
        change (fix_context mfix) with (fix_context_gen 0 mfix).
        change (fix_context mfix') with (fix_context_gen 0 mfix').
        eapply eq_context_upto_cat.
        * apply eq_context_upto_refl. typeclasses eauto.
        * generalize 0.
          unfold fix_context_gen.
          eapply (All2_All_mix_left ihmfix) in a.
          clear -a.
          induction a; try constructor; simpl; intros n; auto.
          destruct r as [[s [Hs IH]] [[eqty eqbod] eqrarg]].
          eapply eq_context_upto_cat.
          + constructor; [|constructor].
            now eapply eq_term_upto_univ_lift.
          + apply IHa. }
      assert(#|fix_context mfix| = #|fix_context mfix'|).
      { now rewrite !fix_context_length, (All2_length _ _ a). } 
      eapply type_Cumul.
      + econstructor.
        * eapply fix_guard_eq_term ; eauto.
          constructor. assumption.
        * eassumption.
        * assumption.
        * eapply (All2_All_mix_left ihmfix) in a.
          clear -a.
          induction a; constructor; simpl; auto.
          destruct r as [[s [Hs IH]] [[eqty eqbod] eqrarg]].
          exists s; apply IH; eauto.
        * solve_all.
          ** destruct a0 as [s [Hs IH]].
            specialize (IH _ a2).
            specialize (b _ b0).
            eapply context_conversion'; eauto.
            eapply type_Cumul with (lift0 #|fix_context mfix| (dtype x)); auto.
            right. exists s. rewrite <-H.
            eapply (weakening _ _ _ _ (tSort _)); eauto. now eapply typing_wf_local in b.
            apply cumul_refl. rewrite <- H.
            eapply eq_term_upto_univ_lift.
            eapply eq_term_upto_univ_impl.
            3: intuition eauto.
            all: intros ? ? [].
            *** eapply eq_universe_refl.
            *** eapply leq_universe_refl.
          ** eapply isLambda_eq_term_l.
            --- eassumption.
            --- intuition eauto. 
        + eapply All_nth_error in ihmfix as [s [Hs _]]; eauto.
        + apply cumul_refl. eapply eq_term_upto_univ_impl.
          3:intuition eauto. 3:symmetry; eauto.
          all: intros ? ? [].
          * eapply eq_universe_refl.
          * eapply leq_universe_refl.


  - intros mfix n decl types hnth hwf ihmfix ihmfixb allow_cofix v e.
    dependent destruction e.
    eapply All2_nth_error_Some in hnth as hnth' ; eauto.
    destruct hnth' as [decl' [hnth' hh]].
    destruct hh as [[ety ebo] era].
    assert (hwf' : wf_local Σ (Γ ,,, fix_context mfix')).
    { apply PCUICWeakening.All_mfix_wf; auto.
      eapply (All2_All_mix_left ihmfix) in a.
      clear -a.
      induction a; constructor; simpl; auto.
      destruct r as [[s [Hs IH]] [[eqty eqbod] eqrarg]].
      exists s; apply IH; eauto. }
    assert (convctx : conv_context Σ (Γ ,,, fix_context mfix) (Γ ,,, fix_context mfix')).
    { eapply eq_context_upto_univ_conv_context.
      eapply (eq_context_impl eq). intros x y eqx. subst. reflexivity. 
      change (fix_context mfix) with (fix_context_gen 0 mfix).
      change (fix_context mfix') with (fix_context_gen 0 mfix').
      eapply eq_context_upto_cat.
      * apply eq_context_upto_refl. typeclasses eauto.
      * generalize 0.
        unfold fix_context_gen.
        eapply (All2_All_mix_left ihmfix) in a.
        clear -a.
        induction a; try constructor; simpl; intros n; auto.
        destruct r as [[s [Hs IH]] [[eqty eqbod] eqrarg]].
        eapply eq_context_upto_cat.
        + constructor; [|constructor].
          now eapply eq_term_upto_univ_lift.
        + apply IHa. }
    assert(#|fix_context mfix| = #|fix_context mfix'|).
    { now rewrite !fix_context_length, (All2_length _ _ a). } 
    eapply type_Cumul.
    + econstructor.
      * eassumption.
      * eassumption.
      * now eapply All_local_env_app in hwf' as [? _]. 
      * eapply (All2_All_mix_left ihmfix) in a.
        clear -a.
        induction a; constructor; simpl; auto.
        destruct r as [[s [Hs IH]] [[eqty eqbod] eqrarg]].
        exists s; apply IH; eauto.
      * solve_all.
        destruct a0 as [s [Hs IH]].
        specialize (IH _ a2).
        specialize (b _ b0).
        eapply context_conversion'; eauto.
        eapply type_Cumul with (lift0 #|fix_context mfix| (dtype x)); auto.
        right. exists s. rewrite <-H.
        eapply (weakening _ _ _ _ (tSort _)); eauto. now eapply typing_wf_local in b.
        apply cumul_refl. rewrite <- H.
        eapply eq_term_upto_univ_lift.
        eapply eq_term_upto_univ_impl.
        3: intuition eauto.
        all: intros ? ? [].
        *** eapply eq_universe_refl.
        *** eapply leq_universe_refl.
      + eapply All_nth_error in ihmfix as [s [Hs _]]; eauto.
      + apply cumul_refl. eapply eq_term_upto_univ_impl.
        3:intuition eauto. 3:symmetry; eauto.
        all: intros ? ? [].
        * eapply eq_universe_refl.
        * eapply leq_universe_refl.

    - intros t A B X ht iht har hcu v e.
      eapply type_Cumul.
      + eapply iht. assumption.
      + destruct har as [[? ?] | [? [? ?]]].
        * left. assumption.
        * right. eexists. eassumption.
      + assumption.
    - rename wfΣ into Γ, wfΓ into v, Γ into u.
      intros A hΣ hu e.
      eapply tm ; eauto.
    Unshelve. exact 0.
  Qed.

  Local Ltac inv H := inversion H; subst; clear H.

  Lemma upto_names_eq_term_upto_univ Re Rle t u
    : eq_term_upto_univ Re Rle t u ->
      forall t' u', t ≡ t' -> u ≡ u' ->
               eq_term_upto_univ Re Rle t' u'.
  Proof.
    revert t u Rle. fix aux 4.
    destruct 1; cbn; intros t'' u'' H' H0';
      inv H'; inv H0'; try econstructor; eauto.
    - revert args'0 args'1 X X0.
      induction a; simpl; intros args0 args'0 H1 H2.
      + inv H1; inv H2; constructor; eauto.
      + inv H1; inv H2. constructor; eauto.
    - apply Forall2_eq, map_inj in H2.
      apply Forall2_eq, map_inj in H3.
      congruence.
      all: apply Universe.make_inj.
    - apply Forall2_eq, map_inj in H2.
      apply Forall2_eq, map_inj in H3.
      congruence.
      all: apply Universe.make_inj.
    - apply Forall2_eq, map_inj in H3.
      apply Forall2_eq, map_inj in H4.
      congruence.
      all: apply Universe.make_inj.
    - revert brs'0 brs'1 X3 X6.
      induction a; simpl; intros args0 args'0 H1 H2.
      + inv H1; inv H2; constructor; eauto.
      + inv H1; inv H2. constructor; eauto.
        destruct X3, X7, r. split; eauto. congruence.
    - revert mfix'0 mfix'1 X X0.
      induction a; simpl; intros args0 args'0 H1 H2.
      + inv H1; inv H2; constructor; eauto.
      + inv H1; inv H2. constructor; eauto.
        destruct X as [[? ?] ?], X1 as [[? ?] ?], r as [[? ?] ?].
        repeat split; eauto. congruence.
    - revert mfix'0 mfix'1 X X0.
      induction a; simpl; intros args0 args'0 H1 H2.
      + inv H1; inv H2; constructor; eauto.
      + inv H1; inv H2. constructor; eauto.
        destruct X as [[? ?] ?], X1 as [[? ?] ?], r as [[? ?] ?].
        repeat split; eauto. congruence.
  Qed.

  Lemma upto_names_leq_term φ t u t' u'
    : t ≡ t' -> u ≡ u' -> leq_term φ t u -> leq_term φ t' u'.
  Proof.
    intros; eapply upto_names_eq_term_upto_univ; eassumption.
  Qed.

  Lemma upto_names_eq_term φ t u t' u'
    : t ≡ t' -> u ≡ u' -> eq_term φ t u -> eq_term φ t' u'.
  Proof.
    intros; eapply upto_names_eq_term_upto_univ; eassumption.
  Qed.

  Definition upto_names_decl := eq_decl_upto eq.

  Definition upto_names_ctx := eq_context_upto eq.

  Infix "≡Γ" := upto_names_ctx (at level 60).


  Lemma destArity_alpha Γ u v ctx s :
    destArity Γ u = Some (ctx, s) ->
    u ≡ v ->
    ∑ ctx', destArity Γ v = Some (ctx', s) × ctx ≡Γ ctx'.
  Proof.
    induction u in v, Γ, ctx, s |- *; cbn; try discriminate.
    - intros X Y. destruct v; inv Y. inv X.
      eexists. split; reflexivity.
    - intros X Y. rewrite destArity_app in X.
      case_eq (destArity [] u2); [|intro e; rewrite e in X; discriminate].
      intros [ctx' s'] e; rewrite e in X; cbn in X; inv X.
      destruct v; inv Y.
      eapply IHu2 in e; tea. destruct e as [ctx'' [e1 e2]].
      eexists; split. cbn. rewrite destArity_app, e1; reflexivity.
      apply eq_context_upto_cat; tas. constructor; tas. reflexivity.
    - intros X Y. rewrite destArity_app in X.
      case_eq (destArity [] u3); [|intro e; rewrite e in X; discriminate].
      intros [ctx' s'] e; rewrite e in X; cbn in X; inv X.
      destruct v; inv Y.
      eapply IHu3 in e; tea. destruct e as [ctx'' [e1 e2]].
      eexists; split. cbn. rewrite destArity_app, e1; reflexivity.
      apply eq_context_upto_cat; tas. constructor; tas. reflexivity.
  Qed.


  Lemma upto_names_conv_context (Σ : global_env_ext) Γ Δ :
    Γ ≡Γ Δ -> conv_context Σ Γ Δ.
  Proof.
    eapply eq_context_upto_conv_context.
    intros x y []. eapply eq_universe_refl.
  Qed.

  Lemma wf_local_alpha Σ Γ Γ' :
    wf Σ.1 -> wf_local Σ Γ -> Γ ≡Γ Γ' -> wf_local Σ Γ'.
  Proof.
    intro hΣ. induction 1 in Γ' |- *.
    - intro Y; inv Y; constructor.
    - intro Y; inv Y. constructor. auto.
      destruct t0 as [s Ht]. exists s. eapply typing_alpha; tea.
      eapply context_conversion'; tea. auto.
      now apply upto_names_conv_context.
    - intro Y; inv Y. constructor; auto.
      + destruct t0 as [s Ht]. exists s. eapply typing_alpha; tea.
        eapply context_conversion'; tea. auto.
        now apply upto_names_conv_context.
      + cbn in *.
        eapply type_Cumul with t.
        * eapply typing_alpha; tea.
        eapply context_conversion'; tea. auto.
        apply upto_names_conv_context; tea.
        * right. destruct t0 as [s Ht]. exists s.
          eapply typing_alpha; tea.
          eapply context_conversion'; tea. auto.
          now apply upto_names_conv_context.
        * constructor; now apply upto_names_impl_leq_term.
  Qed.


  Lemma isWfArity_alpha Σ Γ u v :
    wf Σ.1 ->
    isWfArity typing Σ Γ u ->
    u ≡ v ->
    isWfArity typing Σ Γ v.
  Proof.
    intros hΣ [ctx [s [X1 X2]]] e.
    eapply destArity_alpha in X1; tea.
    destruct X1 as [ctx' [X1 X1']].
    exists ctx', s. split; tas.
    eapply wf_local_alpha; tea.
    now eapply eq_context_upto_cat.
  Qed.

End Alpha.

Infix "≡Γ" := upto_names_ctx (at level 60).
