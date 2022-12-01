(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect ssrbool CRelationClasses CMorphisms.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics
     PCUICLiftSubst PCUICTyping PCUICWeakeningConv PCUICWeakeningTyp
     PCUICCumulativity PCUICEquality PCUICClosedTyp
     PCUICConversion PCUICContextConversion PCUICContextConversionTyp
     PCUICValidity PCUICArities PCUICSpine
     PCUICInductives PCUICInductiveInversion PCUICOnFreeVars
     PCUICWellScopedCumulativity PCUICGuardCondition.

From Equations Require Import Equations.

(* Alpha convertible terms and contexts have the same typings *)

Implicit Types cf : checker_flags.

Notation "`≡α`" := upto_names.
Infix "≡α" := upto_names (at level 60).
Notation "`≡Γ`" := (eq_context_upto empty_global_env eq eq).
Infix "≡Γ" := (eq_context_upto empty_global_env eq eq) (at level 20, no associativity).

#[global]
Instance upto_names_terms_refl : CRelationClasses.Reflexive (All2 `≡α`).
Proof. intro; apply All2_refl; reflexivity. Qed.

Lemma eq_context_upto_empty_impl {cf} {Σ : global_env_ext} ctx ctx' :
  ctx ≡Γ ctx' ->
  eq_context_upto Σ (eq_universe Σ) (eq_universe Σ) ctx ctx'.
Proof.
  intros; eapply All2_fold_impl; tea.
  intros ???? []; constructor; subst; auto;
  eapply eq_term_upto_univ_empty_impl; tea; tc.
Qed.

Section Alpha.
  Context {cf:checker_flags}.

  (* TODO MOVE *)
  Lemma wf_local_nth_error_vass :
    forall Σ Γ i na ty,
      wf Σ.1 ->
      wf_local Σ Γ ->
      nth_error Γ i = Some (vass na ty) ->
      lift_typing typing Σ Γ (lift0 (S i) ty) Sort.
  Proof using Type.
    intros Σ Γ i na ty hΣ hΓ e. simpl.
    induction i in Γ, hΓ, e |- *.
    - destruct Γ. 1: discriminate.
      simpl in e. apply some_inj in e. subst.
      inversion hΓ. subst.
      apply infer_typing_sort_impl with id X0; intros Hs.
      change (tSort _) with (lift0 1 (tSort X0.π1)).
      eapply weakening with (Γ' := [ vass na ty ]).
      all: assumption.
    - destruct Γ. 1: discriminate.
      simpl in e.
      specialize IHi with (2 := e).
      forward IHi by inversion hΓ; tas.
      apply infer_typing_sort_impl with id IHi; intros Hs.
      change (tSort _) with (lift0 1 (lift0 (S i) (tSort IHi.π1))).
      rewrite simpl_lift0.
      eapply weakening with (Γ' := [ c ]).
      all: assumption.
  Qed.

  (* TODO MOVE *)
  Lemma fix_context_nth_error :
    forall m i d,
      nth_error m i = Some d ->
      nth_error (fix_context m) (#|m| - S i) =
      Some (vass (dname d) (lift0 i (dtype d))).
  Proof using Type.
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
  Proof using Type.
    intros Γ Δ i d h.
    rewrite -> nth_error_app_context_lt.
    - assumption.
    - apply nth_error_Some_length in h. assumption.
  Qed.

  Lemma decompose_app_upto {Σ Re Rle x y hd tl} :
    eq_term_upto_univ Σ Re Rle x y ->
    decompose_app x = (hd, tl) ->
    ∑ hd' tl', (y = mkApps hd' tl') *
    eq_term_upto_univ_napp Σ Re Rle #|tl| hd hd' *
    negb (isApp hd') *
    All2 (eq_term_upto_univ Σ Re Re) tl tl'.
  Proof using Type.
    intros eq dapp.
    pose proof (decompose_app_notApp _ _ _ dapp).
    apply decompose_app_inv in dapp.
    subst x.
    eapply eq_term_upto_univ_mkApps_l_inv in eq as [u' [l' [[eqh eqtl] ->]]].
    eexists _, _; intuition eauto.
    revert H.
    inv eqh; simpl in *; try discriminate; auto.
  Qed.

  Lemma decompose_prod_assum_upto_names' ctx ctx' x y :
    ctx ≡Γ ctx' -> upto_names' x y ->
    let (ctx0, x0) := decompose_prod_assum ctx x in
    let (ctx1, x1) := decompose_prod_assum ctx' y in
    ctx0 ≡Γ ctx1 * upto_names' x0 x1.
  Proof using Type.
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
  Proof using Type.
    destruct t; congruence.
  Qed.

  Lemma upto_names_destInd Re Rle t u :
    eq_term_upto_univ empty_global_env Re Rle t u ->
    rel_option (fun '(ind, u) '(ind', u') => (ind = ind') * R_universe_instance Re u u')%type (destInd t) (destInd u).
  Proof using Type.
    induction 1; simpl; constructor; try congruence.
    split; auto.
  Qed.

  Lemma upto_names_check_fix mfix mfix' :
     All2
      (fun x y : def term =>
        (upto_names' (dtype x) (dtype y) × upto_names' (dbody x) (dbody y))
        × rarg x = rarg y) mfix mfix' ->
      map check_one_fix mfix = map check_one_fix mfix'.
  Proof using Type.
    induction 1; simpl; auto.
    rewrite IHX. f_equal.
    unfold check_one_fix.
    destruct x as [name ty body rarg].
    destruct y as [name' ty' body' rarg'].
    simpl in r. destruct r as [[eqty eqb] eqrarg].
    pose proof (decompose_prod_assum_upto_names' [] [] ty ty' ltac:(constructor) eqty).
    do 2 destruct decompose_prod_assum.
    destruct X0 as [eqctx eqt].
    apply (eq_context_upto_smash_context empty_global_env [] []) in eqctx; try constructor.
    apply eq_context_upto_rev' in eqctx.
    eapply (eq_context_upto_nth_error empty_global_env _ _ _ _ rarg) in eqctx.
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
     (dtype x ≡α dtype y × dbody x ≡α dbody y)
     × rarg x = rarg y) mfix mfix' ->
   map check_one_cofix mfix = map check_one_cofix mfix'.
  Proof using Type.
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

  Import PCUICClosed PCUICOnFreeVars PCUICParallelReduction PCUICConfluence.

  Lemma is_closed_context_app_left Γ Δ :
    is_closed_context (Γ ,,, Δ) ->
    is_closed_context Γ.
  Proof using Type.
    rewrite on_free_vars_ctx_app => /andP[] //.
  Qed.
  Hint Resolve is_closed_context_app_left : fvs.

  Lemma is_closed_context_app_right Γ Δ :
    is_closed_context (Γ ,,, Δ) ->
    on_free_vars_ctx (shiftnP #|Γ| xpred0) Δ.
  Proof using Type.
    rewrite on_free_vars_ctx_app => /andP[] //.
  Qed.
  Hint Resolve is_closed_context_app_right : fvs.
  Hint Constructors All_fold : core.

  Lemma on_free_vars_ctx_All_fold_over P Γ Δ :
    on_free_vars_ctx (shiftnP #|Γ| P) Δ <~>
    All_fold (fun Δ => on_free_vars_decl (shiftnP #|Γ ,,, Δ| P)) Δ.
  Proof using Type.
    split.
    - move/alli_Alli/Alli_rev_All_fold.
      intros a; eapply All_fold_impl; tea. cbn.
      intros Γ' x; now rewrite shiftnP_add app_length.
    - intros a'.
      apply alli_Alli.
      eapply (All_fold_impl (fun Δ d => on_free_vars_decl (shiftnP #|Δ| (shiftnP #|Γ| P)) d)) in a'.
      now apply (All_fold_Alli_rev (fun k => on_free_vars_decl (shiftnP k (shiftnP #|Γ| P))) 0) in a'.
      intros.
      now rewrite shiftnP_add -app_length.
  Qed.

  Lemma All2_fold_All_fold_mix_right A P Q Γ Γ' :
    All_fold P Γ' ->
    @All2_fold A Q Γ Γ' ->
    All2_fold (fun Γ Γ' d d' => P Γ' d' × Q Γ Γ' d d') Γ Γ'.
  Proof using Type.
    induction 1 in Γ |- *; intros H; depelim H; constructor; auto.
  Qed.

  Lemma All2_fold_All_right A P Γ Γ' :
    All2_fold (fun _ Γ _ d => P Γ d) Γ Γ' ->
    @All_fold A P Γ'.
  Proof using Type.
    induction 1; constructor; auto.
  Qed.

  Lemma All_decls_alpha_pb_ws_decl {le P} {Γ : context} {d d'} :
    (forall le t t', is_open_term Γ t -> is_open_term Γ t' -> upto_names' t t' -> P le t t') ->
    compare_decls upto_names' upto_names' d d' ->
    ws_decl Γ d ->
    ws_decl Γ d' ->
    All_decls_alpha_pb le P d d'.
  Proof using Type.
    intros HP []; cbn. constructor; eauto.
    move/andP=> [] /= clb clT /andP[] => clb' clT'.
    constructor; auto.
  Qed.

  Lemma eq_context_upto_conv_context_rel {Σ : global_env_ext} {wfΣ : wf Σ} {le} (Γ Δ Δ' : context) :
    is_closed_context (Γ ,,, Δ) ->
    is_closed_context (Γ ,,, Δ') ->
    Δ ≡Γ Δ' ->
    ws_cumul_ctx_pb_rel le Σ Γ Δ Δ'.
  Proof using Type.
    intros cl cl' eq.
    split; eauto with fvs.
    eapply on_free_vars_ctx_All_fold in cl.
    eapply on_free_vars_ctx_All_fold in cl'.
    eapply All_fold_app_inv in cl as [onΓ onΔ].
    eapply All_fold_app_inv in cl' as [_ onΔ'].
    eapply All2_fold_All_fold_mix_left in eq; tea.
    eapply All2_fold_All_fold_mix_right in eq; tea.
    cbn in eq.
    eapply All2_fold_impl_ind. tea. cbn.
    intros ???? IH IH' [? [? ?]].
    apply All2_fold_prod_inv in IH as [a a'].
    apply All2_fold_prod_inv in a' as [a' a''].
    eapply All2_fold_All_left in a'.
    eapply All2_fold_All_right in a.
    eapply on_free_vars_ctx_All_fold_over in a.
    eapply on_free_vars_ctx_All_fold_over in a'.
    eapply on_free_vars_ctx_All_fold in onΓ.
    move: (on_free_vars_ctx_app xpred0 Γ Γ0).
    rewrite onΓ a' /= => iscl.
    move: (on_free_vars_ctx_app xpred0 Γ Δ0).
    rewrite onΓ a /= => iscl'.
    eapply All_decls_alpha_pb_ws_decl; tea.
    intros. apply ws_cumul_pb_compare => //. now apply eq_term_compare_term, upto_names_impl_eq_term.
    rewrite app_length (All2_fold_length IH') -app_length //.

  Qed.

  Lemma eq_context_upto_map2_set_binder_name Σ pctx pctx' Γ Δ :
    pctx ≡Γ pctx' ->
    eq_context_upto Σ eq eq Γ Δ ->
    eq_context_upto Σ eq eq
      (map2 set_binder_name (forget_types pctx) Γ)
      (map2 set_binder_name (forget_types pctx') Δ).
  Proof using Type.
    intros eqp.
    induction 1 in pctx, pctx', eqp |- *.
    - induction eqp; cbn; constructor.
    - depelim eqp. simpl. constructor.
      simpl. constructor; auto.
      destruct c, p; constructor; auto.
  Qed.

  Lemma eq_context_upto_lift_context Σ Re Rle :
    RelationClasses.subrelation Re Rle ->
    forall u v n k,
      eq_context_upto Σ Re Rle u v ->
      eq_context_upto Σ Re Rle (lift_context n k u) (lift_context n k v).
  Proof using Type.
    intros re u v n k.
    induction 1.
    - constructor.
    - rewrite !lift_context_snoc; constructor; eauto.
      depelim p; constructor; simpl; intuition auto;
      rewrite -(length_of X);
      apply eq_term_upto_univ_lift; auto.
  Qed.

  Lemma eq_context_upto_subst_instance Σ :
    forall u v i,
    valid_constraints (global_ext_constraints Σ)
                      (subst_instance_cstrs i Σ) ->
    eq_context_upto Σ eq eq u v ->
    eq_context_upto Σ eq eq (subst_instance i u) (subst_instance i v).
  Proof using Type.
    intros u v i vc.
    induction 1.
    - constructor.
    - rewrite !PCUICUnivSubst.subst_instance_cons. constructor; eauto.
      depelim p; constructor; simpl; intuition auto.
      eapply (PCUICUnivSubstitutionConv.eq_term_upto_univ_subst_preserved Σ (fun _ => eq) (fun _ => eq)).
      intros x y u v ? ? ->; reflexivity.
      intros x y u v ? ? ->; reflexivity. exact vc.
      assumption.
      eapply (PCUICUnivSubstitutionConv.eq_term_upto_univ_subst_preserved Σ (fun _ => eq) (fun _ => eq)).
      intros x y u v ? ? ->; reflexivity.
      intros x y u v ? ? ->; reflexivity. exact vc.
      assumption.
      eapply (PCUICUnivSubstitutionConv.eq_term_upto_univ_subst_preserved Σ (fun _ => eq) (fun _ => eq)).
      intros x y u v ? ? ->; reflexivity.
      intros x y u v ? ? ->; reflexivity. exact vc.
      assumption.
  Qed.

  Lemma eq_context_gen_upto ctx ctx' :
    eq_context_gen eq eq ctx ctx' ->
    eq_context_upto empty_global_env eq eq ctx ctx'.
  Proof using Type.
    intros a; eapply All2_fold_impl; tea.
    intros. destruct X; subst; constructor; auto; try reflexivity.
  Qed.

  Lemma case_predicate_context_equiv {ind mdecl idecl p p'} :
    eq_predicate upto_names' eq p p' ->
    eq_context_upto empty_global_env eq eq
      (case_predicate_context ind mdecl idecl p)
      (case_predicate_context ind mdecl idecl p').
  Proof using Type.
    intros [eqpars [eqinst [eqctx eqret]]].
    rewrite /case_predicate_context /case_predicate_context_gen.
    apply eq_context_upto_map2_set_binder_name => //.
    now eapply eq_context_gen_upto.
    rewrite /pre_case_predicate_context_gen.
    eapply R_universe_instance_eq in eqinst. rewrite -eqinst.
    apply eq_context_upto_subst_context; tea; tc.
    reflexivity.
    now apply All2_rev.
  Qed.

  Lemma case_branch_context_equiv {ind mdecl p p' bctx bctx' cdecl} :
    eq_predicate upto_names' eq p p' ->
    bctx ≡Γ bctx' ->
    (case_branch_context ind mdecl p (forget_types bctx) cdecl) ≡Γ
    (case_branch_context ind mdecl p' (forget_types bctx') cdecl).
  Proof using Type.
    intros [eqpars [eqinst [eqctx eqret]]] eqctx'.
    eapply R_universe_instance_eq in eqinst.
    rewrite /case_branch_context /case_branch_context_gen -eqinst.
    apply eq_context_upto_map2_set_binder_name => //.
    rewrite /pre_case_branch_context_gen.
    apply eq_context_upto_subst_context; tea; tc.
    reflexivity.
    now apply All2_rev.
  Qed.

  Lemma case_branch_type_equiv (Σ : global_env_ext) {ind mdecl idecl p p' br br' ctx ctx' c cdecl} :
    eq_predicate upto_names' eq p p' ->
    bcontext br ≡Γ bcontext br' ->
    ctx ≡Γ ctx' ->
    let ptm := it_mkLambda_or_LetIn ctx (preturn p) in
    let ptm' := it_mkLambda_or_LetIn ctx' (preturn p') in
    eq_term Σ Σ
      (case_branch_type ind mdecl idecl p br ptm c cdecl).2
      (case_branch_type ind mdecl idecl p' br' ptm' c cdecl).2.
  Proof using Type.
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

  Lemma eq_binder_annots_eq_context_gen_ctx {Δ : context} {nas} :
    All2 (fun x y => eq_binder_annot x y.(decl_name)) nas Δ ->
    eq_context_gen eq eq (map2 set_binder_name nas Δ) Δ.
  Proof using Type.
  induction Δ in nas |- * using PCUICInduction.ctx_length_rev_ind; simpl; intros hlen.
  - depelim hlen. simpl. reflexivity.
  - destruct nas as [|nas na] using rev_case => //;
    pose proof (All2_length hlen) as hlen';len in hlen'; simpl in hlen'; try lia.
    eapply All2_app_inv_l in hlen as (l1'&l2'&heq&alnas&allna).
    depelim allna. depelim allna.
    rewrite map2_app => /= //; try lia. unfold aname. lia.
    eapply app_inj_tail in heq as [<- <-].
    simpl. eapply All2_fold_app; auto.
    constructor. constructor.
    destruct d as [na' [d|] ty]; constructor; cbn in *; auto;
    try reflexivity.
  Qed.

  Import PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp.
  Lemma inst_case_predicate_context_eq {Σ : global_env_ext} {wfΣ : wf Σ} {ind mdecl idecl p} :
    wf_predicate mdecl idecl p ->
    eq_context_gen eq eq (ind_predicate_context ind mdecl idecl) (pcontext p) ->
    eq_context_gen eq eq (case_predicate_context ind mdecl idecl p) (inst_case_predicate_context p).
  Proof using Type.
    intros wfp eq.
    rewrite /case_predicate_context /case_predicate_context_gen.
    epose proof (wf_pre_case_predicate_context_gen wfp).
    etransitivity.
    now apply eq_binder_annots_eq_context_gen_ctx.
    rewrite /pre_case_predicate_context_gen /inst_case_predicate_context.
    rewrite /inst_case_context.
    eapply eq_context_gen_subst_context.
    now eapply eq_context_gen_eq_univ_subst_preserved.
  Qed.

  Lemma ctx_inst_impl {Σ P Q Γ s Δ}:
    (forall Σ Γ u U, P Σ Γ u U -> Q Σ Γ u U) ->
    PCUICTyping.ctx_inst P Σ Γ s Δ -> PCUICTyping.ctx_inst Q Σ Γ s Δ.
  Proof using Type.
    intros HP.
    induction 1; constructor; auto.
  Qed.

  Lemma ctx_inst_eq_context {Σ P Q Γ Γ' s Δ}:
    (forall Σ Γ Γ' u U, (Γ ≡Γ Γ') -> P Σ Γ u U -> Q Σ Γ' u U) ->
    Γ ≡Γ Γ' ->
    PCUICTyping.ctx_inst P Σ Γ s Δ -> PCUICTyping.ctx_inst Q Σ Γ' s Δ.
  Proof using Type.
    intros HP e.
    induction 1; constructor; eauto.
  Qed.

  Lemma wf_local_eq_context_upto_names {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ Δ'} :
    wf_local Σ (Γ,,, Δ) ->
    eq_context_gen eq eq Δ' Δ ->
    wf_local Σ (Γ ,,, Δ').
  Proof using Type.
    intros a eq.
    eapply All2_fold_All2 in eq.
    induction eq; depelim a; cbn; try solve [constructor; auto];
    depelim r; subst; constructor; auto.
    1,2: apply infer_typing_sort_impl with id l; intros Hs.
    3: rename l0 into Hs.
    all: eapply (closed_context_cumulativity _ (pb:=Conv)); tea; [apply IHeq; pcuic|].
    all: eapply ws_cumul_ctx_pb_rel_app.
    all: eapply eq_context_upto_conv_context_rel; fvs.
    all: eapply eq_context_gen_upto.
    all: now eapply All2_fold_All2 in eq.
  Qed.

  Lemma case_branch_type_eq_context_gen_1 {ind mdecl idecl cdecl p n br} {ctx ctx' ret} :
    (case_branch_type ind mdecl idecl p br
      (it_mkLambda_or_LetIn ctx ret) n cdecl).1 ≡Γ
    (case_branch_type ind mdecl idecl p br
      (it_mkLambda_or_LetIn ctx' ret) n cdecl).1.
  Proof using Type. reflexivity. Qed.

  Lemma case_branch_type_eq_context_gen_2 {ind mdecl idecl cdecl p n br} {ctx ctx' ret} :
    ctx ≡Γ ctx' ->
    (case_branch_type ind mdecl idecl p br
      (it_mkLambda_or_LetIn ctx ret) n cdecl).2 ≡'
    (case_branch_type ind mdecl idecl p br
      (it_mkLambda_or_LetIn ctx' ret) n cdecl).2.
  Proof using Type.
    intros eq.
    rewrite /case_branch_type /=.
    rewrite /case_branch_context_gen /=. cbn.
    eapply eq_term_upto_univ_mkApps.
    2:{ eapply All2_refl. reflexivity. }
    len. eapply eq_term_upto_univ_lift.
    eapply eq_term_upto_univ_impl; revgoals.
    eapply eq_term_upto_univ_it_mkLambda_or_LetIn; tea.
    2:reflexivity. 2:lia. all:tc.
  Qed.

  Lemma eq_context_conversion {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ} {t T} :
    Σ ;;; Γ |- t : T ->
    Γ ≡Γ Δ ->
    wf_local Σ Δ ->
    Σ ;;; Δ |- t : T.
  Proof using Type.
    intros.
    eapply closed_context_conversion; tea.
    eapply typing_wf_local in X.
    eapply (eq_context_upto_conv_context_rel []) in X0.
    eapply ws_cumul_ctx_pb_rel_app in X0; tea.
    rewrite !app_context_nil_l in X0. exact X0.
    all:rewrite !app_context_nil_l; fvs.
  Qed.

  Lemma upto_names_conv_context (Σ : global_env_ext) Γ Δ :
    Γ ≡Γ Δ -> conv_context cumulAlgo_gen Σ Γ Δ.
  Proof using Type.
    eapply eq_context_upto_empty_conv_context.
  Qed.

  Lemma isType_eq_context_conversion {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ} {T} :
    isType Σ Γ T ->
    Γ ≡Γ Δ ->
    wf_local Σ Δ ->
    isType Σ Δ T.
  Proof using Type.
    intros Hty eq wfΔ; apply infer_typing_sort_impl with id Hty; intros Hs.
    now eapply eq_context_conversion.
  Qed.

  Lemma typing_alpha_prop :
    env_prop (fun Σ Γ u A =>
      forall Δ v,
        eq_term_upto_univ empty_global_env eq eq u v ->
        Γ ≡Γ Δ ->
        Σ ;;; Δ |- v : A)
    (fun Σ Γ => forall Δ, Γ ≡Γ Δ ->  wf_local Σ Δ).
  Proof using Type*.
    eapply typing_ind_env.
    all: intros Σ wfΣ Γ wfΓ.
    - induction 1.
      * intros Δ eq; destruct Δ; depelim eq; constructor.
      * intros Δ eq; depelim eq. depelim c.
        constructor; auto.
        apply infer_typing_sort_impl with id tu; intros _. eapply Hs; auto.
      * intros Δ eq; depelim eq. depelim c.
        constructor; auto.
        apply infer_typing_sort_impl with id tu; intros _. eapply Hs; auto.
        red.
        specialize (Hc _ _ e0 eq).
        specialize (Hs _ _ e1 eq).
        eapply type_Cumul'; tea. now exists tu.π1.
        eapply eq_term_upto_univ_cumulSpec.
        eapply eq_term_leq_term.
        now eapply upto_names_impl_eq_term.

    - intros n decl hnth ih Δ v e eqctx; invs e.
      assert (isType Σ Γ (lift0 (S n) (decl_type decl))).
      { eapply validity. econstructor; eauto. }
      specialize (ih _ eqctx).
      epose proof (eq_context_upto_nth_error _ _ _ _ _ _ eqctx).
      erewrite hnth in X0. depelim X0.
      eapply type_Cumul.
      eapply type_Rel ; tea.
      eapply eq_context_conversion; tea. eapply X.π2.
      depelim e. destruct p.
      eapply eq_term_upto_univ_cumulSpec, eq_term_leq_term, eq_term_upto_univ_lift.
      eapply upto_names_impl_eq_term. now symmetry.
    - intros l ih hl Δ v e eqctx; invs e.
      specialize (ih _ eqctx).
      eapply eq_context_conversion; tea.
      eapply type_Sort; assumption.
    - intros na A B s1 s2 ih hA ihA hB ihB Δ v e eqctx; invs e.
      econstructor.
      + eapply ihA. assumption. eauto.
      + eapply context_conversion.
        * eapply ihB. assumption. reflexivity.
        * constructor; eauto.
          simpl. eexists. eapply ihA; tea.
        * constructor.
          -- now eapply eq_context_upto_empty_conv_context.
          -- constructor. assumption. constructor.
             eapply upto_names_impl_eq_term. assumption.
    - intros na A t s1 B ih hA ihA hB ihB Δ v e e'; invs e.
      eapply type_Cumul'.
      + econstructor.
        * eapply ihA; tea.
        * eapply eq_context_conversion.
          -- eapply ihB. assumption. reflexivity.
          -- constructor. 1: assumption.
             simpl. constructor; auto.
          -- constructor; eauto. exists s1.
              now eapply ihA.
      + eapply validity in hB;tea.
        eapply isType_tProd; eauto. split; eauto with pcuic.
        eapply validity. eapply ihB; eauto.
        constructor; auto. constructor ; auto. reflexivity.
      + apply eq_term_upto_univ_cumulSpec, eq_term_leq_term.
        symmetry. constructor; auto.
        all: try (eapply upto_names_impl_eq_term ; assumption).
        all: reflexivity.
    - intros na b B t s1 A ih hB ihB hb ihb hA ihA Δ v e e'; invs e.
      specialize (ihB _ _ X0 e').
      specialize (ihb _ _ X e').
      assert (isType Σ Γ (tLetIn na b B A)).
      { eapply validity. econstructor; eauto. }
      eapply type_Cumul'.
      + econstructor.
        * eapply ihB; trea.
        * econstructor.
          -- eapply ihb; trea.
          -- eapply ihB; trea.
          --  eapply eq_term_upto_univ_cumulSpec, eq_term_leq_term.
             eapply upto_names_impl_eq_term. assumption.
        * eapply eq_context_conversion.
          -- eapply ihA; trea.
          -- constructor.
            ++ assumption.
            ++ constructor; auto.
          -- constructor; auto.
             ++ exists s1; eapply ihB; eauto.
             ++ eapply type_Cumul'; tea.
                exists s1. eapply ihB; eauto.
                eapply eq_term_upto_univ_cumulSpec, eq_term_leq_term.
                now apply upto_names_impl_eq_term.
      + apply infer_typing_sort_impl with id X2; intros Hs.
        eapply eq_context_conversion; tea. eauto.
      + eapply eq_term_upto_univ_cumulSpec, eq_term_leq_term.
        symmetry; constructor. assumption.
        all: try (eapply upto_names_impl_eq_term ; assumption).
        all: reflexivity.
    - intros t na A B s u ih hty ihty ht iht hu ihu Δ v e e'; invs e.
      assert (isType Σ Γ (B {0 := s})).
      { eapply validity; econstructor; eauto. }
      eapply type_Cumul'.
      + econstructor; cycle 1.
        * eapply iht; trea.
          eapply eq_term_upto_univ_empty_impl in X; eauto.
          all:typeclasses eauto.
        * eapply ihu; trea.
        * eapply ihty. reflexivity. auto.
      + apply infer_typing_sort_impl with id X1; intros Hs. eapply eq_context_conversion; tea. eauto.
      + eapply eq_term_upto_univ_cumulSpec, eq_term_leq_term.
        symmetry.
        eapply upto_names_impl_eq_term.
        eapply eq_term_upto_univ_subst ; now auto.
    - intros cst u decl ? ? hdecl hcons Δ v e e'; invs e.
      eapply R_universe_instance_eq in H2. subst.
      constructor; eauto.
    - intros ind u mdecl idecl isdecl ? ? hcons Δ v e e'; invs e.
      eapply R_universe_instance_eq in H2. subst.
      econstructor ; eauto.
    - intros ind i u mdecl idecl cdecl isdecl ? ? ? Δ v e e'; invs e.
      eapply R_universe_instance_eq in H4. subst.
      econstructor ; eauto.
    - intros ind p c brs args ps mdecl idecl isdecl X X0 H Hpctx cpc wfp
        cup wfpctx Hret IHret
            wfcpc kelim HIHctxi Hc IHc iscof ptm wfbrs Hbrs Δ v e e'; invs e.
      have eqp := X1.
      eassert (ctx_inst _ _ _ _) as Hctxi by now eapply ctx_inst_impl with (2 := HIHctxi).
      eassert (PCUICEnvTyping.ctx_inst _ _ _ _ _) as IHctxi.
      { eapply ctx_inst_impl with (2 := HIHctxi). intros ? ? ? ? [? r]; exact r. }
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
      have wfcpc' := wfcpc (Δ ,,, case_predicate_context ind mdecl idecl p').
      forward wfcpc'. { eapply eq_context_upto_cat; auto.
      apply (case_predicate_context_equiv eqp). }
      eapply R_universe_instance_eq in eqinst.
      assert (isType Σ Δ (mkApps ptm (args ++ [c]))).
      { eapply isType_eq_context_conversion. eapply validity. econstructor; eauto.
        constructor; eauto. constructor; eauto.
        solve_all. eapply a0; eauto; reflexivity. all:auto. }
      eapply type_Cumul'; tea.
      + have cu' : consistent_instance_ext Σ (ind_universes mdecl) (puinst p').
        { now rewrite -eqinst. }
        have convctx' : eq_context_upto_names (pcontext p') (ind_predicate_context ind mdecl idecl).
        { etransitivity; tea. symmetry. now eapply All2_fold_All2 in eqctx. }
        assert (eqp' : eq_context_gen eq eq (inst_case_predicate_context p')
          (case_predicate_context ind mdecl idecl p')).
        { rewrite /inst_case_predicate_context.
          rewrite /case_predicate_context /case_predicate_context_gen in wfcpc.
          symmetry. apply inst_case_predicate_context_eq; tea.
          eapply All2_fold_All2. now symmetry. }
        assert (wf_local Σ (Δ,,, inst_case_predicate_context p')).
        { eapply wf_local_eq_context_upto_names.
          exact wfcpc'. assumption. }
        have ty' : Σ;;; Δ,,, case_predicate_context ind mdecl idecl p' |- preturn p' : tSort ps.
        { eapply eq_context_conversion. eapply IHret. eauto. reflexivity. all:eauto.
          eapply eq_context_upto_cat; eauto. now eapply case_predicate_context_equiv. }
        have ctxinst' : ctx_inst Σ Δ (pparams p' ++ args)
          (List.rev
             (subst_instance (puinst p') (ind_params mdecl,,, ind_indices idecl))).
        { rewrite -eqinst.
          move: IHctxi => ctxi.
          destruct eqp.
          eapply PCUICSpine.ctx_inst_eq_context; tea.
          rewrite List.rev_involutive.
          * eapply weaken_wf_local; tea. now eapply wf_local_app_inv in X4 as [].
            eapply (on_minductive_wf_params_indices_inst isdecl _ cup).
          * eapply ctx_inst_eq_context; tea. cbn; eauto.
          * eapply ctx_inst_eq_context; tea. cbn; intros; eauto.
            now exact (X6 _ u ltac:(reflexivity) X5).
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
        destruct (wf_local_app_inv X4) as [wfΔ _].
        assert (clΔ := (wf_local_closed_context wfΔ)).
        econstructor; tea; eauto. 2,3: constructor; tea ; eauto.
        * eapply (type_ws_cumul_pb (pb:=Cumul)).
          eapply IHc; eauto.
          eexists; eapply isType_mkApps_Ind; tea.
          unshelve eapply (ctx_inst_spine_subst _ ctxinst').
          eapply weaken_wf_local; tea.
          now eapply (on_minductive_wf_params_indices_inst isdecl).
          eapply ws_cumul_pb_eq_le. rewrite -eqinst.
          eapply ws_cumul_pb_mkApps; trea.
          eapply ws_cumul_pb_refl => //. eauto with fvs.
          eapply wf_local_closed_context in wfΓ.
          eapply isType_open in X1.
          rewrite on_free_vars_mkApps in X1. move/andP: X1 => [] _.
          rewrite forallb_app => /andP[] hargs hc.
          eapply All2_app.
          2:{ eapply eq_terms_ws_cumul_pb_terms => //.
              now eapply wf_local_closed_context in wfΔ. }
          eapply ctx_inst_closed, All_app in Hctxi as []; eauto.
          eapply ctx_inst_closed, All_app in ctxinst' as []; eauto.
          eapply eq_terms_ws_cumul_pb_terms => //.
          rewrite (All2_fold_length e') in a, a0.
          solve_all. now eapply closedn_on_free_vars.
          solve_all. now eapply closedn_on_free_vars.
          eapply (All2_impl eqpars).
          intros. now eapply upto_names_impl_eq_term.
        * eapply All2i_All2_mix_left in Hbrs; tea.
          2:now eapply Forall2_All2 in wfbrs.
          epose proof (wf_case_branches_types' (p:=p') ps args brs' isdecl) as a.
          forward a.
          { eexists; eapply isType_mkApps_Ind; tea.
            unshelve eapply (ctx_inst_spine_subst _ ctxinst').
            eapply weaken_wf_local; tea.
            eapply (on_minductive_wf_params_indices_inst isdecl _ cu'). }
          specialize (a H0). cbn in a.
          forward a.
          { eapply eq_context_conversion; tea.
            eapply eq_context_upto_cat; auto. reflexivity.
            eapply eq_context_gen_upto. now symmetry. }
          do 2 forward a by auto.
          eapply (All2i_All2_All2i_All2i Hbrs X3 a).
          intros n cdecl br br' [wfbr [wfbrctx wfbrty]].
          destruct wfbrty as (IHbrctx & (Hbbody & IHbbody) & (Hbty & IHbty)).
          intros [eqbctx eqbodies] [wfbr' wfcpars wfcparsn wfcbctx Hbr'ty].
          split; intuition auto.
          etransitivity. symmetry. eapply All2_fold_All2. exact eqbctx. assumption.
          eapply eq_context_gen_upto in eqbctx.
          assert (cbreq := case_branch_context_equiv (ind:=ind) (mdecl:=mdecl) (cdecl:=cdecl) eqp eqbctx).
          rewrite case_branch_type_fst.
          intuition auto.
          { eapply type_Cumul. eapply IHbbody; auto.
            eapply eq_context_upto_cat; auto. eapply Hbr'ty.
            eapply eq_term_upto_univ_cumulSpec, eq_term_leq_term.
            rewrite /ptm /cpc. eapply case_branch_type_equiv; auto.
            now eapply case_predicate_context_equiv. }


      + apply eq_term_upto_univ_cumulSpec, eq_term_leq_term.
        apply eq_term_mkApps; tea.
        rewrite /ptm.
        eapply eq_term_upto_univ_it_mkLambda_or_LetIn; tea; tc.
        2:eapply upto_names_impl_eq_term => //. 2:now symmetry.
        apply eq_context_upto_empty_impl.
        eapply case_predicate_context_equiv. now symmetry.
        eapply All2_app. apply All2_refl; reflexivity.
        repeat constructor. now apply upto_names_impl_eq_term.

    - intros p c u mdecl idecl cdecl pdecl isdecl args X X0 hc ihc H Δ v e e'; invs e.
      eapply type_Cumul'.
      + econstructor. all: try eassumption.
        eapply ihc; tea.
      + eapply validity ; eauto.
        econstructor ; eauto.
        eapply eq_context_conversion; tea; pcuic.
      + apply eq_term_upto_univ_cumulSpec, eq_term_leq_term.
        symmetry.
        eapply upto_names_impl_eq_term.
        eapply eq_term_upto_univ_substs ; auto; try reflexivity.
        * constructor ; auto.
          eapply All2_same.
          intro. eapply eq_term_upto_univ_refl ; auto.

    - intros mfix n decl types hguard hnth hwf ihmfix ihmfixb wffix Δ v e e'; invs e.
      eapply All2_nth_error_Some in hnth as hnth' ; eauto.
      destruct hnth' as [decl' [hnth' hh]].
      destruct hh as [[[ety eqann] ebo] era].
      assert (hwf' : wf_local Σ (Γ ,,, fix_context mfix')).
      { apply PCUICWeakeningTyp.All_mfix_wf; auto.
        eapply (All2_All_mix_left ihmfix) in X.
        clear -X.
        induction X; constructor; simpl; auto.
        destruct r as [Hty [[[eqty eqann] eqbod] eqrarg]].
        apply infer_typing_sort_impl with id Hty; intros [Hs IH].
        apply IH; eauto. reflexivity. }
      assert (convctx : conv_context cumulAlgo_gen Σ (Γ ,,, fix_context mfix) (Γ ,,, fix_context mfix')).
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
          destruct r as [Hty [[[eqty eqbod] eqrarg] eqann]].
          eapply eq_context_upto_cat.
          + constructor; constructor; auto.
            eapply eq_term_upto_univ_empty_impl; eauto.
            4:now eapply eq_term_upto_univ_lift. all:tc.
          + apply IHX. }
      assert(#|fix_context mfix| = #|fix_context mfix'|).
      { now rewrite !fix_context_length (All2_length X). }
      specialize (hwf (Δ ,,, types)) as hwfΔ.
      forward hwfΔ.
      { apply eq_context_upto_cat; auto. reflexivity. }
      specialize (hwf (Γ ,,, types)).
      forward hwf. { apply eq_context_upto_cat; auto; reflexivity. }
      eapply wf_local_app_inv in hwfΔ as [].
      eapply eq_context_conversion; tea.
      eapply type_Cumul'.
      + econstructor.
        * assumption.
        * eapply (fix_guard_eq_term _ _ _ _ n); eauto.
          constructor. assumption.
        * eassumption.
        * eapply (All2_All_mix_left ihmfix) in X.
          clear -X.
          induction X; constructor; simpl; auto.
          destruct r as [Hty [[[eqty eqann] eqbod] eqrarg]].
          apply infer_typing_sort_impl with id Hty; intros [Hs IH].
          apply IH; eauto. reflexivity.
        * solve_all.
          destruct b0 as [Hb IHb].
          specialize (IHb (Γ ,,, types) _ b2).
          forward IHb. { apply eq_context_upto_cat; reflexivity. }
          eapply context_conversion; eauto.
          eapply (type_Cumul' (lift0 #|fix_context mfix| (dtype x))); auto.
          apply infer_typing_sort_impl with id a1; intros [Hs IH].
          specialize (IH _ _ a0 e').
          rewrite <-H.
          eapply (weakening _ _ _ _ (tSort _)); eauto.
          eapply eq_context_conversion; tea. now symmetry.
          eapply eq_term_upto_univ_cumulSpec.
          rewrite <- H.
          eapply eq_term_upto_univ_lift.
          eapply eq_term_upto_univ_empty_impl.
          4: intuition eauto.
          all: intros ? ? []; reflexivity.
        * revert wffix.
          unfold wf_fixpoint, wf_fixpoint_gen.
          move/andP => [] hm ho.
          apply/andP; split.
          { solve_all. move: b b2.
            generalize (dbody x) (dbody y).
            clear=> t t' isL eq.
            destruct t => //. now depelim eq. }
          move: ho; enough (map check_one_fix mfix = map check_one_fix mfix') as ->; auto.
          apply upto_names_check_fix. solve_all.
        + eapply All_nth_error in ihmfix; tea.
          now apply infer_typing_sort_impl with id ihmfix; intros [].
        + apply eq_term_upto_univ_cumulSpec, eq_term_leq_term, upto_names_impl_eq_term.
          now symmetry.

  - intros mfix n decl types hguard hnth hwf ihmfix ihmfixb wffix Δ v e e'; invs e.
    eapply All2_nth_error_Some in hnth as hnth' ; eauto.
    destruct hnth' as [decl' [hnth' hh]].
    destruct hh as [[[ety eqann] ebo] era].
    assert (hwf' : wf_local Σ (Γ ,,, fix_context mfix')).
    { apply PCUICWeakeningTyp.All_mfix_wf; auto.
      eapply (All2_All_mix_left ihmfix) in X.
      clear -X.
      induction X; constructor; simpl; auto.
      destruct r as [Hty [[[eqty eqann] eqbod] eqrarg]].
      apply infer_typing_sort_impl with id Hty; intros [Hs IH].
      apply IH; eauto. reflexivity. }
    assert (convctx : conv_context cumulAlgo_gen Σ (Γ ,,, fix_context mfix) (Γ ,,, fix_context mfix')).
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
        destruct r as [Hty [[[eqty eqbod] eqrarg] eqann]].
        eapply eq_context_upto_cat.
        + constructor; constructor; auto.
          eapply eq_term_upto_univ_empty_impl; eauto.
          4:now eapply eq_term_upto_univ_lift. all:tc.
        + apply IHX. }
    assert(#|fix_context mfix| = #|fix_context mfix'|).
    { now rewrite !fix_context_length (All2_length X). }
    specialize (hwf (Δ ,,, types)) as hwfΔ.
    forward hwfΔ.
    { apply eq_context_upto_cat; auto. reflexivity. }
    specialize (hwf (Γ ,,, types)).
    forward hwf. { apply eq_context_upto_cat; auto; reflexivity. }
    eapply wf_local_app_inv in hwfΔ as [].
    eapply eq_context_conversion; tea.
    eapply type_Cumul'.
    + econstructor.
      * assumption.
      * eapply (cofix_guard_eq_term _ _ _ _ n); eauto.
        constructor. assumption.
      * eassumption.
      * eapply (All2_All_mix_left ihmfix) in X.
        clear -X.
        induction X; constructor; simpl; auto.
        destruct r as [Hty [[[eqty eqann] eqbod] eqrarg]].
        apply infer_typing_sort_impl with id Hty; intros [Hs IH].
        apply IH; eauto. reflexivity.
      * solve_all.
        destruct b0 as [Hb IHb].
        specialize (IHb (Γ ,,, types) _ b2).
        forward IHb. { apply eq_context_upto_cat; reflexivity. }
        eapply context_conversion; eauto.
        eapply (type_Cumul' (lift0 #|fix_context mfix| (dtype x))); auto.
        apply infer_typing_sort_impl with id a1; intros [Hs IH].
        specialize (IH _ _ a0 e').
        rewrite <-H.
        eapply (weakening _ _ _ _ (tSort _)); eauto.
        eapply eq_context_conversion; tea. now symmetry.
        apply eq_term_upto_univ_cumulSpec. rewrite <- H.
        eapply eq_term_upto_univ_lift.
        eapply eq_term_upto_univ_empty_impl.
        4: intuition eauto.
        all: intros ? ? []; reflexivity.
      * revert wffix.
        unfold wf_cofixpoint, wf_cofixpoint_gen.
        enough (map check_one_cofix mfix = map check_one_cofix mfix') as ->; auto.
        apply upto_names_check_cofix. solve_all.
      + eapply All_nth_error in ihmfix; tea.
        now apply infer_typing_sort_impl with id ihmfix; intros [].
      + apply eq_term_upto_univ_cumulSpec, eq_term_leq_term, upto_names_impl_eq_term.
        now symmetry.
    - intros p prim_ty cdecl IH prim decl pinv Δ v e e'.
      depelim e. econstructor; tea. now apply IH.

    - intros t A B X wf ht iht har ihar hcu Δ v e e'.
      eapply (type_ws_cumul_pb (pb:=Cumul)).
      + eapply iht; tea.
      + exists X; eauto.
        specialize (wf _ e'). now eapply eq_context_conversion.
      + eapply (ws_cumul_pb_ws_cumul_ctx (pb':=Conv)); tea.
        2:eapply PCUICInversion.into_ws_cumul; tea.
        specialize (wf _ e').
        apply wf_conv_context_closed => //.
        apply upto_names_conv_context. now symmetry. pcuic.
  Qed.

  Lemma typing_alpha {Σ : global_env_ext} {Γ u v A} {wfΣ : wf Σ.1} :
    Σ ;;; Γ |- u : A ->
    u ≡' v ->
    Σ ;;; Γ |- v : A.
  Proof using Type.
    intros. eapply (env_prop_typing typing_alpha_prop); eauto. reflexivity.
  Qed.

  Local Ltac inv H := inversion H; subst; clear H.

  Lemma eq_term_upto_univ_napp_0 n t t' :
    eq_term_upto_univ_napp empty_global_env eq eq n t t' ->
    t ≡α t'.
  Proof using Type.
    apply eq_term_upto_univ_empty_impl; typeclasses eauto.
  Qed.

  Lemma upto_names_eq_term_refl Σ Re n t t' :
    RelationClasses.Reflexive Re ->
    t ≡α t' ->
    eq_term_upto_univ_napp Σ Re Re n t t'.
  Proof using Type.
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
    forall t' u', t ≡α t' -> u ≡α u' ->
    eq_term_upto_univ_napp Σ Re Rle napp t' u'.
  Proof using Type.
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
    : t ≡α t' -> u ≡α u' -> leq_term Σ φ t u -> leq_term Σ φ t' u'.
  Proof using Type.
    intros; eapply upto_names_eq_term_upto_univ; try eassumption; tc.
  Qed.

  Lemma upto_names_eq_term Σ φ t u t' u'
    : t ≡α t' -> u ≡α u' -> eq_term Σ φ t u -> eq_term Σ φ t' u'.
  Proof using Type.
    intros; eapply upto_names_eq_term_upto_univ; tea; tc.
  Qed.

  Lemma destArity_alpha Γ u v ctx s :
    destArity Γ u = Some (ctx, s) ->
    u ≡α v ->
    ∑ ctx', destArity Γ v = Some (ctx', s) × ctx ≡Γ ctx'.
  Proof using Type.
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

  Lemma wf_local_alpha {Σ} {wfΣ : wf Σ.1} {Γ Γ'} :
    wf_local Σ Γ -> Γ ≡Γ Γ' -> wf_local Σ Γ'.
  Proof using Type.
    intros; eapply (env_prop_wf_local typing_alpha_prop); tea.
  Qed.

  Lemma isType_alpha {Σ} {wfΣ : wf Σ.1} Γ u v :
    isType Σ Γ u ->
    u ≡α v ->
    isType Σ Γ v.
  Proof using Type.
    intros Hty eq.
    apply infer_typing_sort_impl with id Hty; intros Hs.
    eapply typing_alpha; eauto.
  Qed.

  Lemma isType_alpha_ctx {Σ} {wfΣ : wf Σ.1} {Γ Δ u v} :
    isType Σ Γ u ->
    Γ ≡Γ Δ ->
    u ≡α v ->
    isType Σ Δ v.
  Proof using Type.
    intros Hty eqctx eqtm.
    apply infer_typing_sort_impl with id Hty; intros Hs.
    eapply typing_alpha_prop; eauto.
  Qed.

  Lemma isWfArity_alpha {Σ} {wfΣ : wf Σ.1} {Γ u v} :
    isWfArity Σ Γ u ->
    u ≡α v ->
    isWfArity Σ Γ v.
  Proof using Type.
    intros [isTy [ctx [s X1]]] e.
    eapply destArity_alpha in X1; tea.
    split; [eapply isType_alpha; eauto|].
    destruct X1 as [ctx' [X1 X1']].
    exists ctx', s; auto.
  Qed.

End Alpha.
