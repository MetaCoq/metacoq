(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.CRelationClasses Omega ProofIrrelevance.
From MetaCoq.Template Require Import config Universes monad_utils utils BasicAst
     AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping
     PCUICCumulativity PCUICSR PCUICPosition PCUICEquality PCUICNameless
     PCUICContextConversion PCUICValidity.
From Equations Require Import Equations.

Require Import Equations.Prop.DepElim.
Require Import Equations.Type.Relation_Properties.
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

  Lemma types_of_case_eq_term :
    forall ind mdecl idecl npar args u p p' pty indctx pctx ps btys,
      types_of_case ind mdecl idecl (firstn npar args) u p pty =
      Some (indctx, pctx, ps, btys) ->
      eq_term_upto_univ eq eq p p' ->
      ∑ btys',
        types_of_case ind mdecl idecl (firstn npar args) u p' pty =
        Some (indctx, pctx, ps, btys') ×
        All2 (on_Trel_eq (eq_term_upto_univ eq eq) snd fst) btys btys'.
  Proof.
    intros ind mdecl idecl npar args u p p' pty indctx pctx ps btys htc e.
    unfold types_of_case in *.
    case_eq (instantiate_params (subst_instance_context u (ind_params mdecl)) (firstn npar args) (subst_instance_constr u (ind_type idecl))) ;
      try solve [ intro bot ; rewrite bot in htc ; discriminate htc ].
    intros ity eity. rewrite eity in htc.
    case_eq (destArity [] ity) ;
      try solve [ intro bot ; rewrite bot in htc ; discriminate htc ].
    intros [args0 ?] ear. rewrite ear in htc.
    case_eq (destArity [] pty) ;
      try solve [ intro bot ; rewrite bot in htc ; discriminate htc ].
    intros [args' s'] ear'. rewrite ear' in htc.
    case_eq (map_option_out (build_branches_type ind mdecl idecl (firstn npar args) u p)) ;
      try solve [ intro bot ; rewrite bot in htc ; discriminate htc ].
    intros brtys ebrtys. rewrite ebrtys in htc.
    eapply build_branches_type_eq_term in ebrtys as [brtys' [ebrtys' he]] ; eauto.
    inversion htc. subst. clear htc.
    rewrite ebrtys'. intuition eauto.
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
      exists s. change (tSort s) with (lift0 1 (tSort s)).
      eapply PCUICWeakening.weakening with (Γ' := [ vass na ty ]).
      all: assumption.
    - destruct Γ. 1: discriminate.
      simpl in e.
      specialize IHi with (2 := e).
      destruct IHi as [s h].
      + inversion hΓ. all: auto.
      + exists s. change (tSort s) with (lift0 1 (lift0 (S i) (tSort s))).
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
    ).
    eapply typing_ind_env.
    all: intros Σ wfΣ Γ wfΓ.
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
             eapply eq_term_upto_univ_eq_eq_term. assumption.
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
                eapply eq_term_upto_univ_eq_eq_term. assumption.
      + eapply validity_term ; eauto.
        econstructor ; eauto.
      + constructor.
        eapply eq_term_leq_term.
        apply eq_term_sym.
        constructor.
        all: try (eapply eq_term_upto_univ_eq_eq_term ; assumption).
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
             eapply eq_term_upto_univ_eq_eq_term. assumption.
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
                now apply eq_term_upto_univ_eq_eq_term.
                constructor.
                now apply eq_term_upto_univ_eq_eq_term.
      + eapply validity_term ; eauto.
        econstructor ; eauto.
      + constructor.
        eapply eq_term_leq_term.
        apply eq_term_sym.
        constructor.
        all: try (eapply eq_term_upto_univ_eq_eq_term ; assumption).
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
        eapply eq_term_upto_univ_eq_eq_term.
        eapply eq_term_upto_univ_subst ; now auto.
    - intros cst u decl ? ? hdecl hcons v e.
      dependent destruction e.
      apply All2_eq in r. apply map_inj in r ; revgoals.
      { intros x y h. inversion h. reflexivity. }
      subst.
      constructor ; auto.
    - intros ind u mdecl idecl isdecl ? ? hcons v e.
      dependent destruction e.
      apply All2_eq in r. apply map_inj in r ; revgoals.
      { intros x y h. inversion h. reflexivity. }
      subst.
      econstructor ; eauto.
    - intros ind i u mdecl idecl cdecl isdecl ? ? ? v e.
      dependent destruction e.
      apply All2_eq in r. apply map_inj in r ; revgoals.
      { intros x y h. inversion h. reflexivity. }
      subst.
      econstructor ; eauto.
    - intros ind u npar p c brs args mdecl idecl isdecl X X0 H pars pty X1
             indctx pctx ps btys htc H1 H2 ihp hc ihc ihbrs v e.
      dependent destruction e.
      eapply types_of_case_eq_term in htc as htc' ; eauto.
      destruct htc' as [btys' [ebtys' he]].
      econstructor.
      + econstructor. all: try eassumption.
        * eapply ihp. assumption.
        * eapply ihc. assumption.
        * assert (All2 (fun x y => (fst x = fst y × Σ ;;; Γ |- snd x : snd y) × (Σ ;;; Γ |- y.2 : tSort ps)) brs' btys)
            as hty.
          { clear - ihbrs a.
            induction ihbrs in brs', a |- *.
            - dependent destruction a. constructor.
            - dependent destruction a.
              constructor. all: auto.
              destruct p, r as [[[? ?] ?] ?]. intuition eauto.
              transitivity (fst x) ; eauto.
          }
          clear - he hty ihbrs.
          induction hty in brs, ihbrs, btys', he |- *.
          -- dependent destruction he. constructor.
          -- dependent destruction he.
             dependent destruction ihbrs.
             destruct r. destruct p1.
             destruct p.
             destruct p0 as [[[? ?] ?] ihy].
             constructor ; eauto. intuition eauto.
             ++ solve [ etransitivity ; eauto ].
             ++ econstructor.
                ** eassumption.
                ** right. eexists. eapply ihy. assumption.
                ** constructor.
                   eapply eq_term_leq_term.
                   eapply eq_term_upto_univ_eq_eq_term. assumption.
      + eapply validity_term ; eauto.
        instantiate (1 := tCase (ind, npar) p c brs).
        econstructor ; eauto.
        apply All2_prod_inv in ihbrs as [a1 a4].
        apply All2_prod_inv in a1 as [a1 a3].
        apply All2_prod_inv in a1 as [a1 a2].
        apply All2_prod. all: assumption.
      + constructor.
        eapply eq_term_leq_term.
        apply eq_term_sym.
        eapply eq_term_mkApps.
        all: try (eapply eq_term_upto_univ_eq_eq_term ; assumption).
        eapply All2_app.
        * eapply All2_same. intro. eapply eq_term_refl.
        * constructor ; eauto.
          eapply eq_term_upto_univ_eq_eq_term. assumption.
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
        eapply eq_term_upto_univ_eq_eq_term.
        eapply eq_term_upto_univ_substs ; auto; try reflexivity.
        * constructor ; auto.
          eapply All2_same.
          intro. eapply eq_term_upto_univ_refl ; auto.
    - intros mfix n decl types hnth hguard hwf ihmfix v e.
      dependent destruction e.
      eapply All2_nth_error_Some in hnth as hnth' ; eauto.
      destruct hnth' as [decl' [hnth' hh]].
      destruct hh as [[ety ebo] era].
      assert (hwf' : wf_local Σ (Γ ,,, fix_context mfix')).
      { rename types into Δ. set (Ξ := fix_context mfix').
        assert (e : eq_context_upto eq Δ Ξ).
        { eapply eq_context_upto_rev'.
          clear - a.
          unfold mapi. generalize 0 at 2 4. intro n.
          induction a in n |- *.
          - constructor.
          - simpl. constructor.
            + eapply eq_term_upto_univ_lift. apply r.
            + eapply IHa.
        }
        clearbody Δ Ξ.
        clear - e hwf wfΣ wfΓ.
        induction e.
        - assumption.
        - simpl in *. inversion hwf. subst.
          constructor.
          + eapply IHe. assumption.
          + simpl. destruct X0 as [? [? ih]].
            eexists.
            eapply context_conversion'.
            * assumption.
            * eapply IHe. assumption.
            * eapply ih. assumption.
            * eapply eq_context_upto_conv_context.
              eapply eq_context_impl ; revgoals.
              -- eapply eq_context_upto_cat. 2: eassumption.
                 eapply eq_context_upto_refl. auto.
              -- intros ? ? []. eapply eq_universe_refl.
        - simpl in *. inversion hwf. subst.
          constructor.
          + eapply IHe. assumption.
          + simpl. destruct X0 as [? [? ih]].
            eexists.
            eapply context_conversion'.
            * assumption.
            * eapply IHe. assumption.
            * eapply ih. assumption.
            * eapply eq_context_upto_conv_context.
              eapply eq_context_impl ; revgoals.
              -- eapply eq_context_upto_cat. 2: eassumption.
                 eapply eq_context_upto_refl. auto.
              -- intros ? ? []. eapply eq_universe_refl.
          + simpl in *. destruct X0 as [? [? ih1]]. destruct X1 as [? ih2].
            eapply context_conversion'.
            * assumption.
            * eapply IHe. assumption.
            * eapply type_Cumul.
              -- eapply ih2. assumption.
              -- right. eexists. eapply ih1. assumption.
              -- eapply cumul_refl.
                 eapply eq_term_upto_univ_impl. 3: eassumption.
                 all: intros ? ? [].
                 ++ eapply eq_universe_refl.
                 ++ eapply leq_universe_refl.
            * eapply eq_context_upto_conv_context.
              eapply eq_context_impl ; revgoals.
              -- eapply eq_context_upto_cat. 2: eassumption.
                 eapply eq_context_upto_refl. auto.
              -- intros ? ? []. eapply eq_universe_refl.
      }
      eapply type_Cumul.
      + econstructor.
        * eapply fix_guard_eq_term ; eauto.
          constructor. assumption.
        * eassumption.
        * assumption.
        * assert (val :
            All (fun d =>
              lift_typing typing Σ (Γ ,,, fix_context mfix')
                          ((lift0 #|fix_context mfix'|) (dtype d))
                          None
            ) mfix'
          ).
          { eapply forall_nth_error_All.
            intros i d e.
            apply fix_context_nth_error in e as e'.
            apply nth_error_weak_context with (Γ := Γ) in e'.
            eapply wf_local_nth_error_vass in e'. all: try eassumption.
            rewrite simpl_lift in e' by lia.
            apply nth_error_Some_length in e as hl.
            replace (S (#|mfix'| - S i) + i)
              with (#|mfix'|)
              in e'
              by lia.
            rewrite fix_context_length. assumption.
          }
          rename types into Δ. set (Ξ := fix_context mfix') in *.
          assert (e : eq_context_upto eq Δ Ξ).
          { eapply eq_context_upto_rev'.
            clear - a.
            unfold mapi. generalize 0 at 2 4. intro n.
            induction a in n |- *.
            - constructor.
            - simpl. constructor.
              + eapply eq_term_upto_univ_lift. apply r.
              + eapply IHa.
          }
          clearbody Δ Ξ.
          assert (el : #|Δ| = #|Ξ|).
          { eapply eq_context_upto_length. eassumption. }
          clear - e a ihmfix wfΣ hwf' el val.
          induction a.
          -- constructor.
          -- inversion ihmfix. subst.
             destruct X as [[? ?] ih].
             constructor.
             ++ split.
                ** eapply context_conversion'.
                   --- assumption.
                   --- assumption.
                   --- eapply type_Cumul.
                       +++ eapply ih. intuition eauto.
                       +++ right. simpl in val. inversion val. subst.
                           destruct X.
                           eexists. eapply context_conversion'.
                           *** assumption.
                           *** eauto using typing_wf_local.
                           *** eassumption.
                           *** eapply eq_context_upto_conv_context.
                               eapply eq_context_upto_sym.
                               ---- intros ? ? ?. eapply eq_universe_sym.
                                    assumption.
                               ---- eapply eq_context_impl ; revgoals.
                                    ++++ eapply eq_context_upto_cat.
                                         2: eassumption.
                                         eapply eq_context_upto_refl. auto.
                                    ++++ intros ? ? []. eapply eq_universe_refl.
                       +++ eapply cumul_refl. rewrite <- el.
                           eapply eq_term_upto_univ_lift.
                           eapply eq_term_upto_univ_impl.
                           3: intuition eauto.
                           all: intros ? ? [].
                           *** eapply eq_universe_refl.
                           *** eapply leq_universe_refl.
                   --- eapply eq_context_upto_conv_context.
                       eapply eq_context_impl ; revgoals.
                       +++ eapply eq_context_upto_cat. 2: eassumption.
                           eapply eq_context_upto_refl. auto.
                       +++ intros ? ? []. eapply eq_universe_refl.
                ** eapply isLambda_eq_term_l.
                   --- eassumption.
                   --- intuition eauto.
             ++ eapply IHa.
                ** assumption.
                ** inversion val. assumption.
      + eapply validity_term ; eauto.
        instantiate (1 := tFix mfix n).
        econstructor ; eauto.
        * apply All_local_env_lift_prod_inv in hwf as [? ?]. assumption.
        * apply All_prod_inv in ihmfix as [? ?]. assumption.
      + constructor. eapply eq_term_leq_term.
        apply eq_term_sym.
        eapply eq_term_upto_univ_eq_eq_term. assumption.
    - intros mfix n decl types hnth hwf ihmfix hac v e. subst types.
      dependent destruction e.
      eapply All2_nth_error_Some in hnth as hnth' ; eauto.
      destruct hnth' as [decl' [hnth' hh]].
      destruct hh as [[ety ebo] era].
      assert (hwf' : wf_local Σ (Γ ,,, fix_context mfix')).
      { set (Δ := fix_context mfix) in *.
        set (Ξ := fix_context mfix').
        assert (e : eq_context_upto eq Δ Ξ).
        { eapply eq_context_upto_rev'.
          clear - a.
          unfold mapi. generalize 0 at 2 4. intro n.
          induction a in n |- *.
          - constructor.
          - simpl. constructor.
            + eapply eq_term_upto_univ_lift. apply r.
            + eapply IHa.
        }
        clearbody Δ Ξ.
        clear - e hwf wfΣ wfΓ.
        induction e.
        - assumption.
        - simpl in *. inversion hwf. subst.
          constructor.
          + eapply IHe. assumption.
          + simpl. destruct X0 as [? [? ih]].
            eexists.
            eapply context_conversion'.
            * assumption.
            * eapply IHe. assumption.
            * eapply ih. assumption.
            * eapply eq_context_upto_conv_context.
              eapply eq_context_impl ; revgoals.
              -- eapply eq_context_upto_cat. 2: eassumption.
                 eapply eq_context_upto_refl. auto.
              -- intros ? ? []. eapply eq_universe_refl.
        - simpl in *. inversion hwf. subst.
          constructor.
          + eapply IHe. assumption.
          + simpl. destruct X0 as [? [? ih]].
            eexists.
            eapply context_conversion'.
            * assumption.
            * eapply IHe. assumption.
            * eapply ih. assumption.
            * eapply eq_context_upto_conv_context.
              eapply eq_context_impl ; revgoals.
              -- eapply eq_context_upto_cat. 2: eassumption.
                 eapply eq_context_upto_refl. auto.
              -- intros ? ? []. eapply eq_universe_refl.
          + simpl in *. destruct X0 as [? [? ih1]]. destruct X1 as [? ih2].
            eapply context_conversion'.
            * assumption.
            * eapply IHe. assumption.
            * eapply type_Cumul.
              -- eapply ih2. assumption.
              -- right. eexists. eapply ih1. assumption.
              -- eapply cumul_refl.
                 eapply eq_term_upto_univ_impl. 3: eassumption.
                 all: intros ? ? [].
                 ++ eapply eq_universe_refl.
                 ++ eapply leq_universe_refl.
            * eapply eq_context_upto_conv_context.
              eapply eq_context_impl ; revgoals.
              -- eapply eq_context_upto_cat. 2: eassumption.
                 eapply eq_context_upto_refl. auto.
              -- intros ? ? []. eapply eq_universe_refl.
      }
      eapply type_Cumul.
      + econstructor.
        * assumption.
        * eassumption.
        * assumption.
        * assert (val :
            All (fun d =>
              lift_typing typing Σ (Γ ,,, fix_context mfix')
                          ((lift0 #|fix_context mfix'|) (dtype d))
                          None
            ) mfix'
          ).
          { eapply forall_nth_error_All.
            intros i d e.
            apply fix_context_nth_error in e as e'.
            apply nth_error_weak_context with (Γ := Γ) in e'.
            eapply wf_local_nth_error_vass in e'. all: try eassumption.
            rewrite simpl_lift in e' by lia.
            apply nth_error_Some_length in e as hl.
            replace (S (#|mfix'| - S i) + i)
              with (#|mfix'|)
              in e'
              by lia.
            rewrite fix_context_length. assumption.
          }
          set (Δ := fix_context mfix) in *.
          set (Ξ := fix_context mfix') in *.
          assert (e : eq_context_upto eq Δ Ξ).
          { eapply eq_context_upto_rev'.
            clear - a.
            unfold mapi. generalize 0 at 2 4. intro n.
            induction a in n |- *.
            - constructor.
            - simpl. constructor.
              + eapply eq_term_upto_univ_lift. apply r.
              + eapply IHa.
          }
          clearbody Δ Ξ.
          assert (el : #|Δ| = #|Ξ|).
          { eapply eq_context_upto_length. eassumption. }
          clear - e a ihmfix wfΣ hwf' el val.
          induction a.
          -- constructor.
          -- inversion ihmfix. subst.
             destruct X as [? ih].
             constructor.
             ++ eapply context_conversion'.
                ** assumption.
                ** assumption.
                ** eapply type_Cumul.
                   --- eapply ih. intuition eauto.
                   --- right. simpl in val. inversion val. subst.
                       destruct X.
                       eexists. eapply context_conversion'.
                       +++ assumption.
                       +++ eauto using typing_wf_local.
                       +++ eassumption.
                       +++ eapply eq_context_upto_conv_context.
                           eapply eq_context_upto_sym.
                           *** intros ? ? ?. eapply eq_universe_sym.
                               assumption.
                           *** eapply eq_context_impl ; revgoals.
                               ---- eapply eq_context_upto_cat.
                                    2: eassumption.
                                    eapply eq_context_upto_refl. auto.
                               ---- intros ? ? []. eapply eq_universe_refl.
                   --- eapply cumul_refl. rewrite <- el.
                       eapply eq_term_upto_univ_lift.
                       eapply eq_term_upto_univ_impl.
                       3: intuition eauto.
                       all: intros ? ? [].
                       +++ eapply eq_universe_refl.
                       +++ eapply leq_universe_refl.
                ** eapply eq_context_upto_conv_context.
                   eapply eq_context_impl ; revgoals.
                   --- eapply eq_context_upto_cat. 2: eassumption.
                       eapply eq_context_upto_refl. auto.
                   --- intros ? ? []. eapply eq_universe_refl.
             ++ eapply IHa.
                ** assumption.
                ** inversion val. assumption.
      + eapply validity_term ; eauto.
        instantiate (1 := tCoFix mfix n).
        econstructor ; eauto.
        * apply All_local_env_lift_prod_inv in hwf as [? ?]. assumption.
        * apply All_prod_inv in ihmfix as [? ?]. assumption.
      + constructor. eapply eq_term_leq_term.
        apply eq_term_sym.
        eapply eq_term_upto_univ_eq_eq_term. assumption.
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
      eapply typing_wf_local. eassumption.
    Unshelve. exact 0.
  Qed.

  Corollary type_nameless :
    forall Σ Γ u A,
      wf Σ.1 ->
      Σ ;;; Γ |- u : A ->
      Σ ;;; Γ |- nl u : A.
  Proof.
    intros Σ Γ u A hΣ h.
    eapply typing_alpha ; eauto.
    eapply eq_term_upto_univ_tm_nl. all: auto.
  Qed.


End Alpha.