(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICTyping PCUICWeakening PCUICCumulativity PCUICEquality
     PCUICConversion PCUICContextConversion PCUICValidity PCUICArities PCUICSpine.
From Equations Require Import Equations.

(* Alpha convertible terms and contexts have the same typings *)

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

  Lemma case_predicate_context_equiv Σ ind mdecl idecl p p' : 
    eq_predicate upto_names' eq p p' ->
    eq_context_upto Σ eq eq 
      (case_predicate_context ind mdecl idecl p)
      (case_predicate_context ind mdecl idecl p').
  Proof.
    intros [eqpars [eqinst [eqctx eqret]]].
    rewrite /case_predicate_context /case_predicate_context_gen.
  Admitted.

  Lemma R_universe_instance_eq {u u'} : R_universe_instance eq u u' -> u = u'.
  Proof.
    intros H.
    apply Forall2_eq in H. apply map_inj in H ; revgoals.
    { apply Universe.make_inj. }
    subst. constructor ; auto.
  Qed.

Lemma subst_context_subst_telescope s k Γ :
subst_context s k (List.rev Γ) = List.rev (subst_telescope s k Γ).
Proof.
rewrite /subst_telescope subst_context_alt.
rewrite rev_mapi. apply mapi_rec_ext.
intros n [na [b|] ty] le le'; rewrite /= /subst_decl /map_decl /=; 
rewrite List.rev_length Nat.add_0_r in le'; len; lia_f_equal.
Qed.

Lemma cumul_ctx_rel_app {Σ Γ Δ Δ'} :
  cumul_ctx_rel Σ Γ Δ Δ' <~> cumul_context Σ (Γ ,,, Δ) (Γ ,,, Δ').
Proof.
  split.
  - intros; eapply PCUICContextRelation.All2_fold_app.
    apply (length_of X). reflexivity. apply X.
  - intros; eapply PCUICContextRelation.All2_fold_app_inv.
    move: (length_of X); len; lia.
    assumption.
Qed.
    
Lemma cumul_ctx_rel_trans {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ Δ' Δ''} :
  cumul_ctx_rel Σ Γ Δ Δ' ->
  cumul_ctx_rel Σ Γ Δ' Δ'' ->
  cumul_ctx_rel Σ Γ Δ Δ''.
Proof.
  move/cumul_ctx_rel_app => h /cumul_ctx_rel_app h'.
  apply cumul_ctx_rel_app.
  now eapply cumul_context_trans; tea. 
Qed.


Lemma ctx_inst_merge {Σ : global_env_ext} {wfΣ : wf Σ} Γ inst inst' Δ :
  wf_local Σ (Γ ,,, (List.rev Δ)) ->
  PCUICTyping.ctx_inst
    (fun (Σ : global_env_ext) (Γ : context) (t T : term) =>
    forall u : term, red1 Σ Γ t u -> Σ;;; Γ |- u : T) Σ Γ inst Δ ->
  ctx_inst Σ Γ inst Δ ->
  OnOne2 (red1 Σ Γ) inst inst' ->
  ctx_inst Σ Γ inst' Δ.
Proof.
  intros wf c.
  induction c in inst', wf |- *; intros ctxi; depelim ctxi; intros o.
  - depelim o.
  - depelim o. constructor. apply t0. auto.
    rewrite -(List.rev_involutive Δ).
    rewrite subst_telescope_subst_context.
    simpl in wf. rewrite - !/(app_context _ _) app_context_assoc in wf. 
    eapply ctx_inst_cumul.
    2:{ instantiate (1:=subst_context [i] 0 (List.rev Δ)).
        rewrite -subst_telescope_subst_context List.rev_involutive. exact ctxi. }
    eapply cumul_ctx_rel_app.
    eapply conv_cumul_context.
    eapply (onone_red_cont_context_subst _ [i] [hd']); tea.
    repeat constructor. repeat constructor. constructor. auto.
    eapply wf_local_app_inv. eapply substitution_wf_local; tea.
    repeat (constructor; tea). rewrite subst_empty; tea.
    eapply wf_local_app_inv. eapply substitution_wf_local; tea.
    repeat (constructor; tea). rewrite subst_empty; tea. now eapply t0.
    constructor; auto. eapply IHc.
    rewrite -subst_context_subst_telescope.
    eapply substitution_wf_local; tea.
    repeat (constructor; tea). rewrite subst_empty; tea.
    simpl in wf. rewrite - !/(app_context _ _) app_context_assoc in wf.
    exact wf. tas. tas.
  - constructor. eapply IHc; eauto.
    simpl in wf. rewrite - !/(app_context _ _) app_context_assoc in wf.
    rewrite -subst_context_subst_telescope.
    eapply substitution_wf_local; tea.
    repeat (constructor; tea). eapply subslet_def. constructor.
    all:rewrite !subst_empty //.
    eapply wf_local_app_inv in wf as [wf _]. now depelim wf.
Qed.



  Lemma ctx_inst_conv_context {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ : context} {args Δ'} :
    ctx_inst Σ Γ args Δ -> 
    conv_context_rel Σ Γ (List.rev Δ) (List.rev Δ') ->
    wf_local_rel Σ Γ (List.rev Δ') ->
    ctx_inst Σ Γ args Δ'.
  Proof.
    intros h; induction h in Δ' |- *.
    - intros h; depelim h. destruct Δ' => //. constructor. simpl in H.
      apply (f_equal (@length _)) in H. simpl in H. len in H. simpl in H. lia. 
    - intros h'.
      destruct Δ'. simpl in h'.
      eapply conv_context_rel_app in h'.
      eapply All2_fold_length in h'. simpl in h'. len in h'. simpl in h'. lia.
      simpl in h'. eapply All2_fold_app_inv in h' as []. depelim a. depelim a0.
      simpl. intros wfna.
      destruct (All_local_env_app_inv _ _ _ wfna) as [wfd wfna']. depelim wfd.
      constructor; eauto.
      eapply type_Cumul'; tea. now eapply conv_cumul.
      eapply IHh. rewrite - !subst_context_subst_telescope.
      apply conv_context_rel_app. eapply conv_context_sym; tea.
      apply conv_context_rel_app.
      eapply (conv_ctx_subst (Γ'' := [])).
      rewrite - !app_context_assoc.
      rewrite app_context_nil_l.
      eapply wf_local_app; tea. pcuic.
      rewrite - !app_context_assoc /= //. 
      apply conv_context_rel_app. eapply conv_context_sym; tea.
      apply conv_context_rel_app => //.
      all:admit.
    - intros. eapply IHh.

      
      2:exact wfna. split. 2:exact wfna.
      now depelim wfna.
      todo "case".
  Admitted.


  Lemma ctx_inst_eq_context {Σ Γ} {Δ : context} {args args'} :
   PCUICTyping.ctx_inst
         (fun (Σ : global_env_ext) (Γ : context) (u A : term) =>
          forall v : term, upto_names' u v -> Σ;;; Γ |- v : A) Σ Γ args Δ ->  
    ctx_inst Σ Γ args Δ -> 
    All2 upto_names' args args' ->
    (* eq_context_upto [] eq eq Δ Δ' -> *)
    ctx_inst Σ Γ args' Δ.
  Proof.
    intros h; induction h in args' |- *.
    - intros h h'; depelim h; depelim h'. constructor.
    - intros h'; depelim h'. intros heq; depelim heq. constructor. eauto. eauto.
      eapply ctx_inst_conv_context; tea. eapply IHh; eauto.
      admit. admit.
    - admit.
  Admitted.

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
                  eq_context_upto [] eq eq Δ Δ' ->
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
      + econstructor; tea; eauto.
        * now rewrite -eqinst.
        * eapply conv_context_trans; tea.
          eapply conv_context_trans; tea.
          now eapply conv_context_sym.
        * eapply context_conversion; eauto.
        * eapply wfcpc. reflexivity.
          rewrite /cpc.
          now eapply case_predicate_context_equiv.
        * rewrite -eqinst.
          move: IHctxi.
          instantiate (1:=args).
          intros ctxi.
          destruct eqp.
          eapply ctx_inst_eq_context; tea.
          eapply All2_app => //. apply All2_refl => //. reflexivity.
        * eapply type_Cumul'.
          eapply IHc; eauto.
          eapply validity in Hc as [s Hs]; eauto.
          red in Hs. exists s.
          eapply inversion_mkApps in Hs as [indty [Hind Hsp]]; tea.
          (* eapply type_mkApps_arity; eauto. *)
          all:todo "case".
        * todo "case".
        (* unshelve eapply All2_trans'; [..|eassumption]. *)
        * todo "case".
        (* exact (fun br bty : nat × term => 
                   (((br.1 = bty.1 × Σ;;; Γ |- br.2 : bty.2)
                       × (forall v : term, upto_names' br.2 v -> Σ;;; Γ |- v : bty.2))
                      × ∑ s, Σ;;; Γ |- bty.2 : tSort s ×
                        (forall v : term, upto_names' bty.2 v -> Σ;;; Γ |- v : tSort s))).
        * clear. intros x y z X; rdest; cbn in *.
          congruence. 2: eauto. econstructor; tea. 
           eauto. constructor.
          now eapply upto_names_impl_leq_term.
        * eapply All2_trans'; [..|eassumption].
          2: apply All2_sym; tea.
          clear. intros x y z X; rdest; cbn in *; eauto. congruence.
          intros v H. unshelve eapply (upto_names_trans _ _ _ _) in H; tea.
          eauto. *)

      + todo "case".
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

  Lemma upto_names_eq_term_upto_univ Σ Re Rle napp t u
    : eq_term_upto_univ_napp Σ Re Rle napp t u ->
      forall t' u', t ≡ t' -> u ≡ u' ->
      eq_term_upto_univ_napp Σ Re Rle napp t' u'.
  Proof.
    revert napp t u Rle. fix aux 5.
    destruct 1; cbn; intros t'' u'' H' H0';
      inv H'; inv H0'; try econstructor; eauto.
    - revert args'0 args'1 X X0.
      induction a; simpl; intros args0 args'0 H1 H2.
      + inv H1; inv H2; constructor; eauto.
      + inv H1; inv H2. constructor; eauto.
    - apply eq_term_upto_univ_napp_0 in X.
      apply eq_term_upto_univ_napp_0 in X3.
      eapply aux; eauto.
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
    - simpl. transitivity na'.
      transitivity na; auto.
      now symmetry. assumption.
    - simpl. transitivity na'.
      transitivity na; auto.
      now symmetry. assumption.
    - simpl. transitivity na'.
      transitivity na; auto.
      now symmetry. assumption.
    - todo "case" (* predicates*).
    - todo "case" (* branches *).
      (*auto. revert brs'0 brs'1 X2 X5.
      induction a; simpl; intros args0 args'0 H1 H2.
      + inv H1; inv H2; constructor; eauto.
      + inv H1; inv H2. constructor; eauto.
        destruct X3, X7, r. split; eauto. congruence.*)
    - revert mfix'0 mfix'1 X X0.
      induction a; simpl; intros args0 args'0 H1 H2.
      + inv H1; inv H2; constructor; eauto.
      + inv H1; inv H2. constructor; eauto.
        destruct X as [[[? ?] ?] ?], X1 as [[[? ?] ?] ?], r as [[[? ?] ?] ?].
        repeat split; eauto. congruence.
        etransitivity. symmetry. apply e2.
        etransitivity. eapply e10. assumption.
    - revert mfix'0 mfix'1 X X0.
      induction a; simpl; intros args0 args'0 H1 H2.
      + inv H1; inv H2; constructor; eauto.
      + inv H1; inv H2. constructor; eauto.
        destruct X as [[[? ?] ?] ?], X1 as [[[? ?] ?] ?], r as [[[? ?] ?] ?].
        repeat split; eauto. congruence.
        etransitivity. symmetry. apply e2.
        etransitivity. eapply e10. assumption.
  Qed.

  Lemma upto_names_leq_term Σ φ t u t' u'
    : t ≡ t' -> u ≡ u' -> leq_term Σ φ t u -> leq_term Σ φ t' u'.
  Proof.
    intros; eapply upto_names_eq_term_upto_univ; eassumption.
  Qed.

  Lemma upto_names_eq_term Σ φ t u t' u'
    : t ≡ t' -> u ≡ u' -> eq_term Σ φ t u -> eq_term Σ φ t' u'.
  Proof.
    intros; eapply upto_names_eq_term_upto_univ; eassumption.
  Qed.

  Definition upto_names_decl := eq_decl_upto_gen [] eq eq.

  Definition upto_names_ctx := eq_context_upto [] eq eq.

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

Infix "≡Γ" := upto_names_ctx (at level 60).
