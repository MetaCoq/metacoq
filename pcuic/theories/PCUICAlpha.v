(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICTyping PCUICWeakening PCUICCumulativity PCUICEquality
     PCUICConversion PCUICContextConversion PCUICValidity PCUICArities PCUICSpine
     PCUICInductives PCUICInductiveInversion.
From Equations Require Import Equations.

(* Alpha convertible terms and contexts have the same typings *)

Infix "≡α" := upto_names (at level 60).

Definition upto_names_ctx := eq_context_upto [] eq eq.

Infix "≡Γ" := upto_names_ctx (at level 60).

Section Alpha.
  Context {cf:checker_flags}.

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
    rewrite -> nth_error_app_context_lt.
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

  Lemma decompose_app_upto {Σ Re Rle x y hd tl} : 
    eq_term_upto_univ Σ Re Rle x y ->
    decompose_app x = (hd, tl) ->
    ∑ hd' tl', (y = mkApps hd' tl') *
    eq_term_upto_univ_napp Σ Re Rle #|tl| hd hd' *
    negb (isApp hd') *
    All2 (eq_term_upto_univ Σ Re Re) tl tl'.
  Proof.
    intros eq dapp.
    pose proof (decompose_app_notApp _ _ _ dapp).
    apply decompose_app_inv in dapp.
    subst x.
    eapply eq_term_upto_univ_mkApps_l_inv in eq as [u' [l' [[eqh eqtl] ->]]].
    eexists _, _; intuition eauto.
    revert H.
    inv eqh; simpl in *; try discriminate; auto.
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

  Lemma decompose_prod_assum_upto_names' ctx ctx' x y : 
    eq_context_upto [] eq eq ctx ctx' -> upto_names' x y -> 
    let (ctx0, x0) := decompose_prod_assum ctx x in 
    let (ctx1, x1) := decompose_prod_assum ctx' y in
    eq_context_upto [] eq eq ctx0 ctx1 * upto_names' x0 x1.
  Proof.
    induction x in ctx, ctx', y |- *; intros eqctx eqt; inv eqt; simpl; 
      try split; auto; try constructor; auto.
    - specialize (IHx2 (ctx,, vass na x1) (ctx',,vass na' a') b').
      apply IHx2; auto. constructor; auto; constructor; auto.
    - apply IHx3; auto. constructor; auto; constructor; auto. 
  Qed.

  Lemma destInd_spec t : 
    match destInd t with
    | Some (ind, u) => t = tInd ind u
    | None => forall ind u, t <> tInd ind u
    end.
  Proof.
    destruct t; congruence.
  Qed.

  Lemma upto_names_destInd Re Rle t u : 
    eq_term_upto_univ [] Re Rle t u ->
    rel_option (fun '(ind, u) '(ind', u') => (ind = ind') * R_universe_instance Re u u')%type (destInd t) (destInd u).
  Proof.
    induction 1; simpl; constructor; try congruence.
    split; auto.
  Qed.

  Lemma upto_names_check_fix mfix mfix' :
     All2
      (fun x y : def term =>
        (upto_names' (dtype x) (dtype y) × upto_names' (dbody x) (dbody y))
        × rarg x = rarg y) mfix mfix' ->
      map check_one_fix mfix = map check_one_fix mfix'.
  Proof.
    induction 1; simpl; auto.
    rewrite IHX. f_equal.
    unfold check_one_fix.
    destruct x as [name ty body rarg].
    destruct y as [name' ty' body' rarg'].
    simpl in r. destruct r as [[eqty eqb] eqrarg].
    pose proof (decompose_prod_assum_upto_names' [] [] ty ty' ltac:(constructor) eqty).
    do 2 destruct decompose_prod_assum.
    destruct X0 as [eqctx eqt].
    apply (eq_context_upto_smash_context [] [] []) in eqctx; try constructor.
    apply eq_context_upto_rev' in eqctx.
    eapply (eq_context_upto_nth_error [] _ _ _ _ rarg) in eqctx.
    subst rarg'.
    destruct (nth_error (List.rev (smash_context [] c)) rarg).
    inv eqctx. destruct X0.
    destruct (decompose_app) eqn:eqdec.
    destruct (decompose_app_upto e eqdec) as [hd' [tl' [[[eq eqhd] napp] eqtl]]].
    rewrite eq. rewrite decompose_app_mkApps; auto.
    eapply (eq_term_upto_univ_empty_impl _ Logic.eq Logic.eq Logic.eq Logic.eq #|l0| 0) in eqhd.
    all:try typeclasses eauto.
    apply upto_names_destInd in eqhd.
    inv eqhd; auto.
    destruct a as [ind u], b0 as [ind' u']; simpl in *; auto.
    destruct X0 as [-> _]; auto.
    now inv eqctx.
  Qed.

  Lemma upto_names_check_cofix mfix mfix' :
    All2 (fun x y : def term =>
     (upto_names' (dtype x) (dtype y) × upto_names' (dbody x) (dbody y))
     × rarg x = rarg y) mfix mfix' ->
   map check_one_cofix mfix = map check_one_cofix mfix'.
  Proof.
    induction 1; simpl; auto.
    rewrite IHX. f_equal.
    unfold check_one_cofix. clear X IHX.
    destruct x as [name ty body rarg].
    destruct y as [name' ty' body' rarg'].
    simpl in r. destruct r as [[eqty eqb] <-].
    pose proof (decompose_prod_assum_upto_names' [] [] ty ty' ltac:(constructor) eqty).
    do 2 destruct decompose_prod_assum.
    destruct X as [_ eqt].
    destruct (decompose_app) eqn:eqdec.
    destruct (decompose_app_upto eqt eqdec) as [hd' [tl' [[[eq eqhd] napp] eqtl]]].
    rewrite eq. rewrite decompose_app_mkApps; auto.
    eapply (eq_term_upto_univ_empty_impl _ Logic.eq Logic.eq Logic.eq Logic.eq #|l0| 0) in eqhd.
    all:try typeclasses eauto.
    apply upto_names_destInd in eqhd.
    inv eqhd; auto.
    destruct a as [ind u], b as [ind' u']; simpl in *; auto.
    destruct X as [-> _]; auto.
  Qed.

  Lemma conv_context_app {Σ : global_env_ext} {wfΣ : wf Σ} (Γ1 Γ2 Γ2' : context) :
    conv_context_rel Σ Γ1 Γ2 Γ2' -> conv_context Σ (Γ1 ,,, Γ2) (Γ1 ,,, Γ2').
  Proof.
    intros wf.
    eapply All2_fold_app. apply (length_of wf).
    apply conv_ctx_refl.
    eapply All2_fold_impl; tea. intros ???? []; constructor; auto.
  Qed.

  Lemma eq_context_upto_conv_context_rel {Σ : global_env_ext} {wfΣ : wf Σ} (Γ Δ Δ' : context) :
    eq_context_upto [] eq eq Δ Δ' ->  
    conv_context_rel Σ Γ Δ Δ'.
  Proof.
    intros eq.
    eapply All2_fold_impl; tea.
    intros ???? []; constructor; auto; now constructor; apply upto_names_impl_eq_term.
  Qed.
  Lemma R_universe_instance_eq {u u'} : R_universe_instance eq u u' -> u = u'.
  Proof.
    intros H.
    apply Forall2_eq in H. apply map_inj in H ; revgoals.
    { apply Universe.make_inj. }
    subst. constructor ; auto.
  Qed.

  Lemma case_predicate_context_equiv Σ ind mdecl idecl p p' : 
    eq_predicate upto_names' eq p p' ->
    eq_context_upto Σ eq eq 
      (case_predicate_context ind mdecl idecl p)
      (case_predicate_context ind mdecl idecl p').
  Proof.
    intros [eqpars [eqinst [eqctx eqret]]].
    rewrite /case_predicate_context /case_predicate_context_gen.
  Admitted.

  Lemma eq_context_upto_lift_context Σ Re Rle :
  RelationClasses.subrelation Re Rle ->
  forall u v n k,
    eq_context_upto Σ Re Rle u v ->
    eq_context_upto Σ Re Rle (lift_context n k u) (lift_context n k v).
Proof.
  intros re u v n k.
  induction 1.
  - constructor.
  - rewrite !lift_context_snoc; constructor; eauto.
    depelim p; constructor; simpl; intuition auto;
    rewrite -(length_of X);
    apply eq_term_upto_univ_lift; auto.
Qed.
(* 
Lemma upto_names_subst_instance Σ u :
  valid_constraints (global_ext_constraints Σ) (subst_instance_cstrs u Σ) ->
  upto_names*)

Lemma eq_context_upto_subst_instance Σ :
  forall u v i,
  valid_constraints (global_ext_constraints Σ)
                    (subst_instance_cstrs i Σ) ->
  eq_context_upto Σ eq eq u v ->
  eq_context_upto Σ eq eq (subst_instance i u) (subst_instance i v).
Proof.
intros u v i vc.
induction 1.
- constructor.
- rewrite !PCUICUnivSubst.subst_instance_cons. constructor; eauto.
  depelim p; constructor; simpl; intuition auto.
  eapply (PCUICUnivSubstitution.eq_term_upto_univ_subst_preserved Σ (fun _ => eq) (fun _ => eq)).
  intros x y u v ? ? ->; reflexivity.
  intros x y u v ? ? ->; reflexivity. exact vc.
  assumption.
  eapply (PCUICUnivSubstitution.eq_term_upto_univ_subst_preserved Σ (fun _ => eq) (fun _ => eq)).
  intros x y u v ? ? ->; reflexivity.
  intros x y u v ? ? ->; reflexivity. exact vc.
  assumption.
  eapply (PCUICUnivSubstitution.eq_term_upto_univ_subst_preserved Σ (fun _ => eq) (fun _ => eq)).
  intros x y u v ? ? ->; reflexivity.
  intros x y u v ? ? ->; reflexivity. exact vc.
  assumption.
Qed.

Lemma valid_constraints_empty i : valid_constraints (empty_ext []) (subst_instance_cstrs i (empty_ext [])).
Proof.
  red. destruct check_univs => //.
Qed.

  Lemma case_branch_context_equiv ind mdecl p p' bctx bctx' cdecl : 
    eq_predicate upto_names' eq p p' ->
    eq_context_upto [] eq eq bctx bctx' ->
    eq_context_upto [] eq eq 
      (case_branch_context ind mdecl p (forget_types bctx) cdecl)
      (case_branch_context ind mdecl p' (forget_types bctx') cdecl).
  Proof.
    intros [eqpars [eqinst [eqctx eqret]]] eqctx'.
    eapply R_universe_instance_eq in eqinst.
    rewrite /case_branch_context /case_branch_context_gen -eqinst.
    apply eq_context_upto_subst_context. tc.
    2:now eapply All2_rev.
    rewrite /expand_lets_ctx /expand_lets_k_ctx.
    apply eq_context_upto_subst_context. tc.
    2:eapply All2_refl; reflexivity.
    eapply eq_context_upto_lift_context. tc.
    apply eq_context_upto_subst_context. tc.
    2:eapply All2_refl; reflexivity.
    eapply (eq_context_upto_subst_instance (empty_ext [])).
    apply valid_constraints_empty.
    simpl. apply All2_fold_All2.
    eapply All2_fold_All2 in eqctx'.
    generalize (cstr_args cdecl).
    induction eqctx'.
    * simpl. constructor.
    * simpl. intros []. constructor.
      constructor; auto.
      destruct r, c as [na'' [b''|] ty']; constructor; auto; try reflexivity.
  Qed.

  From Coq Require Import CRelationClasses CMorphisms.
  Lemma eq_term_upto_univ_it_mkLambda_or_LetIn Σ Re Rle :
  RelationClasses.Reflexive Re ->
  Proper (eq_context_upto Σ Re Re ==> eq_term_upto_univ Σ Re Rle ==> eq_term_upto_univ Σ Re Rle) it_mkLambda_or_LetIn.
Proof.
  intros he Γ Δ eq u v h.
  induction eq in u, v, h, he |- *.
  - assumption.
  - simpl. cbn. apply IHeq => //.
    destruct p; cbn; constructor ; tas; try reflexivity.
Qed.

Lemma eq_context_upto_empty_impl {Σ : global_env_ext} ctx ctx' :
  eq_context_upto [] eq eq ctx ctx' ->
  eq_context_upto Σ (eq_universe Σ) (eq_universe Σ) ctx ctx'.
Proof.
  intros; eapply All2_fold_impl; tea.
  intros ???? []; constructor; subst; auto;
  eapply eq_term_upto_univ_empty_impl; tea; tc.
Qed.

  Lemma case_branch_type_equiv (Σ : global_env_ext) ind mdecl idecl p p' br br' c cdecl : 
    eq_predicate upto_names' eq p p' ->
    bcontext br ≡Γ bcontext br' ->
    let ptm := it_mkLambda_or_LetIn (pcontext p) (preturn p) in
    let ptm' := it_mkLambda_or_LetIn (pcontext p') (preturn p') in
    eq_term Σ Σ
      (case_branch_type ind mdecl idecl p br ptm c cdecl).2
      (case_branch_type ind mdecl idecl p' br' ptm' c cdecl).2.
  Proof.
    intros [eqpars [eqinst [eqctx eqret]]] eqctx'.
    eapply R_universe_instance_eq in eqinst.
    intros ptm ptm'.
    rewrite /case_branch_type /case_branch_type_gen -eqinst. cbn.
    eapply eq_term_mkApps.
    - eapply eq_term_upto_univ_lift.
      rewrite /ptm /ptm'.
      eapply eq_term_upto_univ_it_mkLambda_or_LetIn. tc.
      eapply eq_context_upto_empty_impl; tea.
      eapply eq_term_upto_univ_empty_impl; tea; tc.
    - eapply All2_app.
      * eapply All2_map, All2_refl.
        intros.
        eapply eq_term_upto_univ_empty_impl; tea; tc.
        eapply eq_term_upto_univ_substs. tc.
        reflexivity.
        now eapply All2_rev.
      * constructor. 2:constructor.
        eapply eq_term_upto_univ_empty_impl; tea; tc.
        eapply eq_term_upto_univ_mkApps. len.
        reflexivity.
        eapply All2_app.
        + eapply All2_map. eapply (All2_impl eqpars).
          intros. now eapply eq_term_upto_univ_lift.
        + eapply All2_refl. reflexivity.
  Qed.

Lemma All2_map_left_inv {A B C} (P : A -> B -> Type) (l : list C) (f : C -> A) l' : 
  All2 P (map f l) l' -> All2 (fun x => P (f x)) l l'.
Proof.
  rewrite -{1}(map_id l').
  intros. now eapply All2_map_inv in X.
Qed.

  Lemma All2i_All2_All2i_All2i {A B C n} {P : nat -> A -> B -> Type} {Q : B -> C -> Type} {R : nat -> A -> C -> Type}
    {S : nat -> A -> C -> Type} {l l' l''} :
    All2i P n l l' ->
    All2 Q l' l'' ->
    All2i R n l l'' ->
    (forall n x y z, P n x y -> Q y z -> R n x z -> S n x z) ->
    All2i S n l l''.
  Proof.
    intros a b c H.
    induction a in l'', b, c |- *; depelim b; depelim c; try constructor; auto.
    eapply H; eauto.
  Qed.

  Lemma typing_alpha :
    forall Σ Γ u v A,
      wf Σ.1 ->
      Σ ;;; Γ |- u : A ->
      u ≡' v ->
      Σ ;;; Γ |- v : A.
  Proof.
    assert (tm :
      env_prop (fun Σ Γ u A =>
                  forall v,
                    eq_term_upto_univ [] eq eq u v ->
                    Σ ;;; Γ |- v : A)
              (fun Σ Γ => 
                forall Γ' Δ Δ', 
                  Γ = Γ' ,,, Δ ->
                  Δ ≡Γ Δ' ->
                  wf_local Σ (Γ' ,,, Δ'))
    ).
    eapply typing_ind_env.
    all: intros Σ wfΣ Γ wfΓ.
    - induction 1.
      * intros Γ' Δ Δ' eq H; destruct Δ; noconf eq; depelim H; constructor.
      * intros Γ' Δ Δ' eq H; destruct Δ; noconf eq; depelim H.
        + constructor; auto.
        + depelim c. simpl; constructor; auto. eapply IHX; eauto.
          destruct tu as [s Hs].
          exists s. simpl in p.
          eapply context_conversion.
          { eapply p; eauto. }
          { eapply IHX; eauto. }
          now eapply conv_context_app, eq_context_upto_conv_context_rel.
      * intros Γ' Δ Δ' eq H; destruct Δ; noconf eq; depelim H.
        { constructor; auto. }
        depelim c. simpl; constructor; auto. eapply IHX; eauto.
        + destruct tu as [s Hs].
          exists s. simpl in p.
          eapply context_conversion.
          { eapply p0; eauto. }
          { eapply IHX; eauto. }
          { now eapply conv_context_app, eq_context_upto_conv_context_rel. }
        + red.
          specialize (p0 _ e1).
          specialize (p _ e0).
          eapply context_conversion in p0; revgoals.
          { eapply conv_context_app, eq_context_upto_conv_context_rel; tea. }
          eauto.
          eapply context_conversion in p; revgoals.
          { eapply conv_context_app, eq_context_upto_conv_context_rel; tea. }
          { eapply IHX; eauto. }
          eapply type_Cumul'; eauto.
          now exists tu.π1.
          constructor. now eapply eq_term_leq_term, upto_names_impl_eq_term.     

    - intros n decl hnth ih v e; invs e.
      eapply type_Rel ; eassumption.
    - intros l ih hl v e; invs e.
      eapply type_Sort; assumption.
    - intros na A B s1 s2 ih hA ihA hB ihB v e; invs e.
      econstructor.
      + eapply ihA. assumption.
      + eapply context_conversion.
        * eapply ihB. assumption.
        * constructor. 1: assumption.
          simpl. eexists. eapply ihA. assumption.
        * constructor.
          -- apply conv_ctx_refl ; auto.
          -- constructor. assumption. constructor.
             eapply upto_names_impl_eq_term. assumption.
    - intros na A t s1 B ih hA ihA hB ihB v e; invs e.
      eapply type_Cumul'.
      + econstructor.
        * eapply ihA. assumption.
        * eapply context_conversion.
          -- eapply ihB. assumption.
          -- constructor. 1: assumption.
             simpl. eexists. eapply ihA. assumption.
          -- constructor.
             ++ apply conv_ctx_refl ; auto.
             ++ constructor. assumption. constructor.
                eapply upto_names_impl_eq_term. assumption.
      + eapply validity in hB;tea.
        eapply isType_tProd; eauto. split; eauto with pcuic.
      + constructor.
        eapply eq_term_leq_term.
        apply eq_term_sym.
        constructor; auto.
        all: try (eapply upto_names_impl_eq_term ; assumption).
        all: eapply eq_term_refl.
    - intros na b B t s1 A ih hB ihB hb ihb hA ihA v e; invs e.
      eapply type_Cumul'.
      + econstructor.
        * eapply ihB. assumption.
        * econstructor.
          -- eapply ihb. assumption.
          -- eapply ihB. assumption.
          -- constructor. eapply eq_term_leq_term.
             eapply upto_names_impl_eq_term. assumption.
        * eapply context_conversion.
          -- eapply ihA. assumption.
          -- constructor.
            ++ assumption.
            ++ simpl. eexists. eapply ihB. assumption.
            ++ simpl. eapply type_Cumul.
              ** eapply ihb. assumption.
              ** eapply ihB. assumption.
              ** eapply cumul_refl.
                  eapply eq_term_upto_univ_empty_impl. 4:eassumption.
                  all:try typeclasses eauto.
                  all: intros x ? [].
                  --- reflexivity.
                  --- reflexivity.
          -- constructor.
             ++ apply conv_ctx_refl ; auto.
             ++ econstructor. assumption. constructor.
                now apply upto_names_impl_eq_term.
                constructor.
                now apply upto_names_impl_eq_term.
      + eapply validity ; eauto.
        econstructor ; eauto.
      + constructor.
        eapply eq_term_leq_term.
        apply eq_term_sym.
        constructor. assumption.
        all: try (eapply upto_names_impl_eq_term ; assumption).
        all: eapply eq_term_refl.
    - intros t na A B s u ih hty ihty ht iht hu ihu v e; invs e.
      eapply type_Cumul'.
      + econstructor; cycle 1.
        * eapply iht.
          eapply eq_term_upto_univ_empty_impl in X; eauto.
          all:typeclasses eauto.
        * eapply ihu. assumption.
        * eapply hty.
      + eapply validity ; eauto.
        econstructor ; eauto.
      + constructor.
        eapply eq_term_leq_term.
        apply eq_term_sym.
        eapply upto_names_impl_eq_term.
        eapply eq_term_upto_univ_subst ; now auto.
    - intros cst u decl ? ? hdecl hcons v e; invs e.
      eapply R_universe_instance_eq in H2. subst.
      constructor; eauto.
    - intros ind u mdecl idecl isdecl ? ? hcons v e; invs e.
      eapply R_universe_instance_eq in H2. subst.
      econstructor ; eauto.
    - intros ind i u mdecl idecl cdecl isdecl ? ? ? v e; invs e.
      eapply R_universe_instance_eq in H4. subst.
      econstructor ; eauto.
    - intros ind p c brs args ps mdecl idecl isdecl X X0 H cpc wfp 
        cup wfpctx convpctx Hret IHret
            wfcpc kelim Hctxi IHctxi Hc IHc iscof ptm wfbrs Hbrs v e; invs e.
      have eqp := X1.
      destruct X1 as [eqpars [eqinst [eqctx eqret]]].
      assert (wf_predicate mdecl idecl p').
      { destruct wfp. split; auto.
        { now rewrite <-(All2_length eqpars). }
        eapply Forall2_All2 in H1. eapply All2_Forall2.
        eapply All2_fold_All2 in eqctx. eapply All2_sym in eqctx.
        eapply (All2_trans' (@eq_binder_annot name name)); tea.
        2:{ eapply All2_map; tea. eapply All2_impl; tea.
            simpl; intros. destruct X1; simpl; now symmetry. }              
        simpl. intros x y [] []; etransitivity; tea. }
      assert (conv_context Σ (Γ,,, cpc) (Γ,,, case_predicate_context ind mdecl idecl p')).
      { eapply conv_context_app, eq_context_upto_conv_context_rel.
        now eapply case_predicate_context_equiv. }
      assert (conv_context Σ (Γ,,, pcontext p) (Γ,,, pcontext p')).
      { eapply (eq_context_upto_conv_context_rel Γ) in eqctx; tea.
        now apply conv_context_app. }
      eapply R_universe_instance_eq in eqinst.
      assert (isType Σ Γ (mkApps ptm (args ++ [c]))).
      { eapply validity. econstructor; eauto. eapply wfpctx; eauto.
        reflexivity. eapply wfcpc; eauto. reflexivity.
        solve_all. eapply a0; eauto; reflexivity.
        eapply b; eauto; reflexivity. }
      eapply type_Cumul'; tea.
      + have cu' : consistent_instance_ext Σ (ind_universes mdecl) (puinst p').
        { now rewrite -eqinst. }
        have convctx' : conv_context Σ (Γ,,, pcontext p')
          (Γ,,, case_predicate_context ind mdecl idecl p').
        { eapply conv_context_trans; tea.
          eapply conv_context_trans; tea.
          now eapply conv_context_sym. }
        have ty' : Σ;;; Γ,,, pcontext p' |- preturn p' : tSort ps.
        { eapply context_conversion; eauto. }
        have wfcpc' : wf_local Σ (Γ,,, case_predicate_context ind mdecl idecl p').
        { eapply wfcpc. reflexivity.
          rewrite /cpc.
          now eapply case_predicate_context_equiv. }
        have ctxinst' : ctx_inst Σ Γ (pparams p' ++ args)
          (List.rev
             (subst_instance (puinst p') (ind_params mdecl,,, ind_indices idecl))).
        { rewrite -eqinst.
          move: IHctxi => ctxi.
          destruct eqp.
          eapply ctx_inst_eq_context; tea.
          rewrite List.rev_involutive.
          * eapply weaken_wf_local; tea.
           eapply (on_minductive_wf_params_indices_inst isdecl _ cup).
          * eapply All2_app => //. apply All2_refl => //. reflexivity. }
        have wfbrs' : wf_branches idecl brs'.
        { move/Forall2_All2: wfbrs => wf.
          apply All2_Forall2. eapply All2_trans'; tea.
          intros cdecl br br'.
          intros [wfbr [eqbrctx eqbodies]].
          rewrite /wf_branch.
          red. do 2 red in wfbr.
          eapply Forall2_All2 in wfbr. eapply All2_Forall2.
          eapply All2_map_left.
          eapply All2_fold_All2 in eqbrctx.
          eapply All2_map_left_inv in wfbr.
          eapply All2_trans'; tea.
          2:{ eapply All2_symP; tea. tc. }
          intros ??? [[] ?]; try constructor; simpl; auto; now transitivity na'. }
        econstructor; tea; eauto.
        * eapply type_Cumul'.
          eapply IHc; eauto.
          eexists; eapply isType_mkApps_Ind; tea.
          unshelve eapply (ctx_inst_spine_subst _ ctxinst').
          eapply weaken_wf_local; tea.
          now eapply (on_minductive_wf_params_indices_inst isdecl).
          eapply conv_cumul. rewrite -eqinst.
          eapply mkApps_conv_args; trea.
          eapply All2_app.
          2:{ eapply All2_refl; reflexivity. }
          eapply (All2_impl eqpars).
          intros. now constructor; eapply upto_names_impl_eq_term.
        * eapply All2i_All2_mix_left in Hbrs; tea.
          2:now eapply Forall2_All2 in wfbrs.
          epose proof (wf_case_branches_types (p:=p') c ps args brs' isdecl).
          forward X6.
          eexists; eapply isType_mkApps_Ind; tea.
          unshelve eapply (ctx_inst_spine_subst _ ctxinst').
          eapply weaken_wf_local; tea.
          eapply (on_minductive_wf_params_indices_inst isdecl _ cu').
          specialize (X6 H0 ty' convctx' wfbrs').
          eapply All2i_All2_mix_left in X6; tea.
          2:now eapply Forall2_All2 in wfbrs'.
          eapply (All2i_All2_All2i_All2i Hbrs X3 X6).
          clear Hbrs X3 X6 wfbrs wfbrs'.
          intros n cdecl br br' [wfbr [[IHbrctx Hbrctx] [[Hbbody IHcbc] [IHbbody [Hcbty IHcbty]]]]].
          intros [eqbrctxs eqbods] [wfbr' [wfcbc' brty']] brctxty.
          have wfbrctx' : wf_local Σ (Γ,,, bcontext br').
          { eapply IHbrctx; [reflexivity|tas]. }
          assert (cbreq := case_branch_context_equiv ind mdecl p p' (bcontext br) (bcontext br') cdecl eqp eqbrctxs).
          have convbrctx' : conv_context Σ (Γ,,, bcontext br') (Γ,,, brctxty.1).
          { eapply conv_context_trans; tea.
            2:{ rewrite /brctxty case_branch_type_fst.
              eapply eq_context_upto_empty_conv_context.
              eapply eq_context_upto_cat. reflexivity.
              eassumption. }
            eapply conv_context_trans. tea. 2:tea.
            eapply conv_context_sym. tea. 
            eapply eq_context_upto_empty_conv_context.
            eapply eq_context_upto_cat. reflexivity. eassumption. }
          repeat splits => //.
          { now eapply typing_wf_local in brty'. }
          { eapply type_Cumul'.
            * eapply context_conversion; tea.
              eapply IHbbody => //.
              eapply eq_context_upto_empty_conv_context.
              apply eq_context_upto_cat. reflexivity. tas.
            * eexists; red.
              eapply context_conversion.
              eapply brty'. assumption.
              rewrite case_branch_type_fst.
              now apply conv_context_sym.
            * eapply conv_cumul. constructor.
              rewrite /brctxty /ptm.
              eapply case_branch_type_equiv => //. }
          { eapply context_conversion. exact brty'. assumption.
            now apply conv_context_sym. }

      + eapply conv_cumul, mkApps_conv_args; tea.
        rewrite /ptm.
        eapply it_mkLambda_or_LetIn_conv; tea.
        now eapply conv_context_sym.
        constructor. now eapply upto_names_impl_eq_term.
        eapply All2_app. apply All2_refl; reflexivity.
        constructor. constructor; now apply upto_names_impl_eq_term. constructor.

    - intros p c u mdecl idecl pdecl isdecl args X X0 hc ihc H ty v e; invs e.
      eapply type_Cumul'.
      + econstructor. all: try eassumption.
        eapply ihc. assumption.
      + eapply validity ; eauto.
        econstructor ; eauto.
      + constructor.
        eapply eq_term_leq_term.
        apply eq_term_sym.
        eapply upto_names_impl_eq_term.
        eapply eq_term_upto_univ_substs ; auto; try reflexivity.
        * constructor ; auto.
          eapply All2_same.
          intro. eapply eq_term_upto_univ_refl ; auto.
    - intros mfix n decl types hguard hnth hwf ihmfix ihmfixb wffix v e; invs e.
      eapply All2_nth_error_Some in hnth as hnth' ; eauto.
      destruct hnth' as [decl' [hnth' hh]].
      destruct hh as [[[ety eqann] ebo] era].
      assert (hwf' : wf_local Σ (Γ ,,, fix_context mfix')).
      { apply PCUICWeakening.All_mfix_wf; auto.
        eapply (All2_All_mix_left ihmfix) in X.
        clear -X.
        induction X; constructor; simpl; auto.
        destruct r as [[s [Hs IH]] [[[eqty eqann] eqbod] eqrarg]].
        exists s; apply IH; eauto. }
      assert (convctx : conv_context Σ (Γ ,,, fix_context mfix) (Γ ,,, fix_context mfix')).
      { eapply eq_context_upto_univ_conv_context.
        eapply (eq_context_impl _ eq). intros x y eqx. subst. reflexivity.
        1-2:typeclasses eauto. 
        change (fix_context mfix) with (fix_context_gen 0 mfix).
        change (fix_context mfix') with (fix_context_gen 0 mfix').
        eapply eq_context_upto_cat.
        * apply eq_context_upto_refl; typeclasses eauto.
        * generalize 0 at 3 4.
          unfold fix_context_gen.
          eapply (All2_All_mix_left ihmfix) in X.
          clear -X.
          induction X; try constructor; simpl; intros n; auto.
          destruct r as [[s [Hs IH]] [[[eqty eqbod] eqrarg] eqann]].
          eapply eq_context_upto_cat.
          + constructor; constructor; auto.
            eapply eq_term_upto_univ_empty_impl; eauto.
            4:now eapply eq_term_upto_univ_lift. all:tc.
          + apply IHX. }
      assert(#|fix_context mfix| = #|fix_context mfix'|).
      { now rewrite !fix_context_length (All2_length X). } 
      eapply type_Cumul'.
      + econstructor.
        * eapply (fix_guard_eq_term _ _ _ _ n); eauto.
          constructor. assumption.
        * eassumption.
        * assumption.
        * eapply (All2_All_mix_left ihmfix) in X.
          clear -X.
          induction X; constructor; simpl; auto.
          destruct r as [[s [Hs IH]] [[[eqty eqann] eqbod] eqrarg]].
          exists s; apply IH; eauto.
        * solve_all.
          destruct a0 as [s [Hs IH]].
          specialize (IH _ a).
          specialize (b _ b2).
          eapply context_conversion; eauto.
          eapply (type_Cumul' (lift0 #|fix_context mfix| (dtype x))); auto.
          exists s. rewrite <-H.
          eapply (weakening _ _ _ _ (tSort _)); eauto.
          eapply hwf; eauto. reflexivity.
          apply cumul_refl. rewrite <- H.
          eapply eq_term_upto_univ_lift.
          eapply eq_term_upto_univ_empty_impl.
          4: intuition eauto.
          all: intros ? ? []; reflexivity.
        * revert wffix.
          unfold wf_fixpoint.
          enough (map check_one_fix mfix = map check_one_fix mfix') as ->; auto.
          apply upto_names_check_fix. solve_all.
        + eapply All_nth_error in ihmfix as [s [Hs _]]; eauto. exists s; apply Hs.
        + apply cumul_refl. eapply eq_term_upto_univ_empty_impl.
          4:intuition eauto. 4:symmetry; eauto.
          all: intros ? ? []; reflexivity.

  - intros mfix n decl types guard hnth hwf ihmfix ihmfixb wfcofix v e; invs e.
    eapply All2_nth_error_Some in hnth as hnth' ; eauto.
    destruct hnth' as [decl' [hnth' hh]].
    destruct hh as [[[ety eann] ebo] era].
    assert (hwf' : wf_local Σ (Γ ,,, fix_context mfix')).
    { apply PCUICWeakening.All_mfix_wf; auto.
      eapply (All2_All_mix_left ihmfix) in X.
      clear -X.
      induction X; constructor; simpl; auto.
      destruct r as [[s [Hs IH]] [[[eqty eqann] eqbod] eqrarg]].
      exists s; apply IH; eauto. }
    assert (convctx : conv_context Σ (Γ ,,, fix_context mfix) (Γ ,,, fix_context mfix')).
    { eapply eq_context_upto_univ_conv_context.
      eapply (eq_context_impl _ eq). intros x y eqx. subst. reflexivity. 
      1-2:typeclasses eauto.
      change (fix_context mfix) with (fix_context_gen 0 mfix).
      change (fix_context mfix') with (fix_context_gen 0 mfix').
      eapply eq_context_upto_cat.
      * apply eq_context_upto_refl; typeclasses eauto.
      * generalize 0 at 3 4.
        unfold fix_context_gen.
        eapply (All2_All_mix_left ihmfix) in X.
        clear -X.
        induction X; try constructor; simpl; intros n; auto.
        destruct r as [[s [Hs IH]] [[[eqty eqann] eqbod] eqrarg]].
        eapply eq_context_upto_cat.
        + constructor; constructor; tas.
          eapply eq_term_upto_univ_empty_impl.
          4:now eapply eq_term_upto_univ_lift.
          all: intros ? ? []; reflexivity.
        + apply IHX. }
    assert(#|fix_context mfix| = #|fix_context mfix'|).
    { now rewrite !fix_context_length (All2_length X). } 
    eapply type_Cumul'.
    + econstructor.
      * eapply (cofix_guard_eq_term _ _ _ _ n) ; eauto.
        constructor. assumption.
      * eassumption.
      * eassumption.
      * eapply (All2_All_mix_left ihmfix) in X.
        clear -X.
        induction X; constructor; simpl; auto.
        destruct r as [[s [Hs IH]] [[[eqty eqann] eqbod] eqrarg]].
        exists s; apply IH; eauto.
      * solve_all.
        destruct a0 as [s [Hs IH]].
        specialize (IH _ a).
        specialize (b _ b2).
        eapply context_conversion; eauto.
        eapply (type_Cumul' (lift0 #|fix_context mfix| (dtype x))); auto.
        exists s. rewrite <-H.
        eapply (weakening _ _ _ _ (tSort _)); eauto.
        eapply hwf; eauto. reflexivity. 
        apply cumul_refl. rewrite <- H.
        eapply eq_term_upto_univ_lift.
        eapply eq_term_upto_univ_empty_impl.
        4: intuition eauto.
        all: intros ? ? []; reflexivity.
      * revert wfcofix; unfold wf_cofixpoint.
        enough (map check_one_cofix mfix = map check_one_cofix mfix') as ->; auto.
        apply upto_names_check_cofix. solve_all.
      + eapply All_nth_error in ihmfix as [s [Hs _]]; eauto. exists s; apply Hs.
      + apply cumul_refl. eapply eq_term_upto_univ_empty_impl.
        3:intuition eauto. 4:symmetry; eauto.
        all: intros ? ? []; reflexivity.

    - intros t A B X wf ht iht har ihar hcu v e.
      eapply type_Cumul'.
      + eapply iht. assumption.
      + exists X; auto.
      + assumption.
    - rename wfΣ into Γ, wfΓ into v, Γ into u.
      intros A hΣ hu e.
      eapply tm ; eauto.
  Qed.

  Local Ltac inv H := inversion H; subst; clear H.

  Lemma eq_term_upto_univ_napp_0 n t t' :
    eq_term_upto_univ_napp [] eq eq n t t' ->
    upto_names' t t'. 
  Proof.
    apply eq_term_upto_univ_empty_impl; typeclasses eauto.
  Qed.

  Lemma upto_names_eq_term_refl Σ Re n t t' :
    RelationClasses.Reflexive Re ->
    upto_names' t t' ->
    eq_term_upto_univ_napp Σ Re Re n t t'.
  Proof.
    intros.
    eapply eq_term_upto_univ_empty_impl; tea; tc.
    all:intros x y ->; reflexivity.
  Qed.

  Lemma upto_names_eq_term_upto_univ Σ Re Rle napp t u : 
    RelationClasses.Reflexive Re -> 
    RelationClasses.Reflexive Rle ->
    RelationClasses.Symmetric Re ->
    RelationClasses.Transitive Re -> 
    RelationClasses.Transitive Rle ->
    RelationClasses.subrelation Re Rle ->
    eq_term_upto_univ_napp Σ Re Rle napp t u ->
    forall t' u', t ≡ t' -> u ≡ u' ->
    eq_term_upto_univ_napp Σ Re Rle napp t' u'.
  Proof.
    intros.
    eapply (upto_names_eq_term_refl Σ Re) in X0; tea.
    eapply (upto_names_eq_term_refl Σ Re) in X1; tea.
    symmetry in X0.
    eapply eq_term_upto_univ_trans; tea.
    eapply eq_term_upto_univ_impl; tea. reflexivity. reflexivity.
    eapply eq_term_upto_univ_trans; tea.
    eapply eq_term_upto_univ_impl; tea. reflexivity. reflexivity.
  Qed.

  Lemma upto_names_leq_term Σ φ t u t' u'
    : t ≡ t' -> u ≡ u' -> leq_term Σ φ t u -> leq_term Σ φ t' u'.
  Proof.
    intros; eapply upto_names_eq_term_upto_univ; try eassumption; tc.
  Qed.

  Lemma upto_names_eq_term Σ φ t u t' u'
    : t ≡ t' -> u ≡ u' -> eq_term Σ φ t u -> eq_term Σ φ t' u'.
  Proof.
    intros; eapply upto_names_eq_term_upto_univ; tea; tc.
  Qed.

  Definition upto_names_decl := eq_decl_upto_gen [] eq eq.

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
      eexists; split. cbn. rewrite destArity_app e1; reflexivity.
      apply eq_context_upto_cat; tas. constructor; tas. reflexivity.
      constructor; auto.
    - intros X Y. rewrite destArity_app in X.
      case_eq (destArity [] u3); [|intro e; rewrite e in X; discriminate].
      intros [ctx' s'] e; rewrite e in X; cbn in X; inv X.
      destruct v; inv Y.
      eapply IHu3 in e; tea. destruct e as [ctx'' [e1 e2]].
      eexists; split. cbn. rewrite destArity_app e1; reflexivity.
      apply eq_context_upto_cat; tas. constructor; tas. reflexivity.
      constructor; auto.
  Qed.

  Lemma upto_names_conv_context (Σ : global_env_ext) Γ Δ :
    Γ ≡Γ Δ -> conv_context Σ Γ Δ.
  Proof.
    eapply eq_context_upto_empty_conv_context.
  Qed.

  Lemma wf_local_alpha Σ Γ Γ' :
    wf Σ.1 -> wf_local Σ Γ -> Γ ≡Γ Γ' -> wf_local Σ Γ'.
  Proof.
    intro hΣ. induction 1 in Γ' |- *.
    - intro Y; inv Y; constructor.
    - intro Y; inv Y. inv X1. constructor. auto.
      destruct t0 as [s Ht]. exists s. eapply typing_alpha; tea.
      eapply context_conversion; tea. auto.
      now apply upto_names_conv_context.
    - intro Y; inv Y. inv X1. constructor; auto.
      + destruct t0 as [s Ht]. exists s. eapply typing_alpha; tea.
        eapply context_conversion; tea. auto.
        now apply upto_names_conv_context.
      + cbn in *.
        eapply type_Cumul' with t.
        * eapply typing_alpha; tea.
        eapply context_conversion; tea. auto.
        apply upto_names_conv_context; tea.
        * destruct t0 as [s Ht]. exists s.
          eapply typing_alpha; tea.
          eapply context_conversion; tea. auto.
          now apply upto_names_conv_context.
        * constructor; now apply upto_names_impl_leq_term.
  Qed.

  Lemma isType_alpha Σ Γ u v :
    wf Σ.1 ->
    isType Σ Γ u ->
    u ≡ v ->
    isType Σ Γ v.
  Proof.
    intros hΣ [s Hs] eq.
    exists s; eapply typing_alpha; eauto.
  Qed.

  Lemma isWfArity_alpha Σ Γ u v :
    wf Σ.1 ->
    isWfArity Σ Γ u ->
    u ≡ v ->
    isWfArity Σ Γ v.
  Proof.
    intros hΣ [isTy [ctx [s X1]]] e.
    eapply destArity_alpha in X1; tea.
    split; [eapply isType_alpha; eauto|].
    destruct X1 as [ctx' [X1 X1']].
    exists ctx', s; auto.
  Qed.

End Alpha.
