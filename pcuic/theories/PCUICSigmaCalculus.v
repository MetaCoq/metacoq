(* Distributed under the terms of the MIT license.   *)
From Equations Require Import Equations.
From Coq Require Import Bool String List BinPos Compare_dec Omega Lia.
Require Import Coq.Program.Syntax Coq.Program.Basics.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICUnivSubst
     PCUICTyping PCUICWeakeningEnv PCUICClosed PCUICReduction.
Require Import ssreflect ssrbool.

(* TODO Maybe remove later? *)
Require PCUICWeakening.

(** * Type preservation for σ-calculus *)

Set Asymmetric Patterns.
Open Scope sigma_scope.

Section Renaming.

Context `{checker_flags}.

Lemma meta_conv :
  forall Σ Γ t A B,
    Σ ;;; Γ |- t : A ->
    A = B ->
    Σ ;;; Γ |- t : B.
Proof.
  intros Σ Γ t A B h []. assumption.
Qed.

Definition renaming Σ Γ Δ f :=
  forall i decl,
    nth_error Δ i = Some decl ->
    (Σ ;;; Γ |- tRel (f i) : rename f ((lift0 (S i)) decl.(decl_type))) ×
    (forall b,
        decl.(decl_body) = Some b ->
        ∑ decl' b',
          (nth_error Γ (f i) = Some decl') ×
          (decl'.(decl_body) = Some b') ×
          (Σ ;;; Γ |- rename f (lift0 (S i) b) = lift0 (S (f i)) b')
    ).

Lemma renaming_vass :
  forall Σ Γ Δ na A f,
    wf_local Σ (Γ ,, vass na (rename f A)) ->
    renaming Σ Γ Δ f ->
    renaming Σ (Γ ,, vass na (rename f A)) (Δ ,, vass na A) (shiftn 1 f).
Proof.
  intros Σ Γ Δ na A f hΓ h [|i] decl e.
  - simpl in e. inversion e. subst. clear e.
    simpl. split.
    + unfold shiftn at 1. simpl.
      eapply meta_conv.
      * econstructor. all: auto.
        simpl. reflexivity.
      * rewrite !lift_rename.
        autorewrite with sigma.
        eapply inst_ext. intro i.
        unfold ren, lift_renaming, shiftn, subst_compose. simpl.
        f_equal. f_equal. f_equal. lia.
    + intros. discriminate.
  - simpl in e. simpl. split.
    + unfold shiftn at 1. simpl.
      eapply meta_conv.
      * econstructor. all: auto.
        simpl. specialize (h i).
        apply h in e as [h' _].
        (* WOULD NEED Inversion, but it depends on substitution,
           probably doesn't need to... *)
        (* Other solution is to ask for this in renaming! *)
        admit.
      * instantiate (1 := decl).
        rewrite !lift_rename.
        autorewrite with sigma. eapply inst_ext. intro j.
        unfold ren, lift_renaming, shiftn, subst_compose. simpl.
        replace (i - 0) with i by lia.
        (* How did it become this?? *)
        give_up.
    + intros b e'.
      replace (i - 0) with i by lia.
      specialize (h i). eapply h in e as [h1 h2].
      eapply h2 in e' as [decl' [b' [? [? ?]]]].
      eexists decl', b'. split ; [| split]. all: auto.
      admit.
Admitted.

Lemma typing_rename :
  forall Σ Γ Δ f t A,
    wf Σ.1 ->
    wf_local Σ Γ ->
    wf_local Σ Δ ->
    renaming Σ Δ Γ f ->
    Σ ;;; Γ |- t : A ->
    Σ ;;; Δ |- rename f t : rename f A.
Proof.
  intros Σ Γ Δ f t A hΣ hΓ hΔ hf h.
  revert Σ hΣ Γ hΓ t A h Δ f hΔ hf.
  apply (typing_ind_env (fun Σ Γ t T => forall Δ f,
    wf_local Σ Δ ->
    renaming Σ Δ Γ f ->
    Σ ;;; Δ |- rename f t : rename f T
  )).
  - intros Σ wfΣ Γ wfΓ n decl H0 X Δ f hΔ hf.
    simpl. eapply hf. assumption.
  - intros Σ wfΣ Γ wfΓ l X H0 Δ f hΔ hf.
    simpl. constructor. all: auto.
  - intros Σ wfΣ Γ wfΓ na A B s1 s2 X hA ihA hB ihB Δ f hΔ hf.
    simpl.
    econstructor.
    + eapply ihA. all: auto.
    + eapply ihB.
      * econstructor. all: auto.
        eexists. eapply ihA. all: auto.
      *
Admitted.

End Renaming.


Definition inst_context σ (Γ : context) : context :=
  fold_context (fun i => inst (⇑^i σ)) Γ.

Lemma inst_context_length :
  forall σ Γ,
    #|inst_context σ Γ| = #|Γ|.
Proof.
  intros σ Γ. unfold inst_context.
  apply fold_context_length.
Qed.
Hint Rewrite inst_context_length : sigma wf.

Definition inst_decl σ d :=
  map_decl (inst σ) d.

(* TODO MOVE *)
Lemma nth_error_idsn_Some :
  forall n k,
    k < n ->
    nth_error (idsn n) k = Some (tRel k).
Proof.
  intros n k h.
  induction n in k, h |- *.
  - inversion h.
  - simpl. destruct (Nat.ltb_spec0 k n).
    + rewrite nth_error_app1.
      * rewrite idsn_length. auto.
      * eapply IHn. assumption.
    + assert (k = n) by omega. subst.
      rewrite nth_error_app2.
      * rewrite idsn_length. auto.
      * rewrite idsn_length. replace (n - n) with 0 by omega.
        simpl. reflexivity.
Qed.

(* TODO MOVE *)
Lemma nth_error_idsn_None :
  forall n k,
    k >= n ->
    nth_error (idsn n) k = None.
Proof.
  intros n k h.
  eapply nth_error_None.
  rewrite idsn_length. auto.
Qed.

Lemma inst_context_snoc :
  forall σ Γ d,
    inst_context σ (d :: Γ) =
    inst_context σ Γ ,, inst_decl (⇑^#|Γ| σ) d.
Proof.
  intros σ Γ d.
  unfold inst_context, fold_context.
  rewrite !rev_mapi !rev_involutive /mapi mapi_rec_eqn /snoc.
  f_equal.
  - rewrite Nat.sub_0_r List.rev_length. reflexivity.
  - rewrite mapi_rec_Sk. simpl. apply mapi_rec_ext.
    intros k x H H0.
    rewrite app_length !List.rev_length. simpl.
    unfold map_decl. f_equal.
    + destruct (decl_body x) ; auto.
      simpl. f_equal. eapply inst_ext. intro i.
      unfold Upn, subst_consn, subst_compose.
      destruct (Nat.ltb_spec0 i (Nat.pred #|Γ| - k)).
      * rewrite nth_error_idsn_Some. 1: lia.
        rewrite nth_error_idsn_Some. 1: lia.
        reflexivity.
      * rewrite nth_error_idsn_None. 1: lia.
        rewrite nth_error_idsn_None. 1: lia.
        rewrite !idsn_length.
        assert (e : (i - (Nat.pred (#|Γ| + 1) - S k)) = (i - (Nat.pred #|Γ| - k))) by lia.
        rewrite e. eapply inst_ext.
        intro j. unfold shiftk. f_equal. lia.
    + f_equal. f_equal. lia.
Qed.
Hint Rewrite inst_context_snoc : sigma.

Section Sigma.

Context `{checker_flags}.

(* Well-typedness of a substitution *)

Definition well_subst Σ (Γ : context) σ (Δ : context) :=
  forall x decl,
    nth_error Γ x = Some decl ->
    Σ ;;; Δ |- σ x : ((lift0 (S x)) (decl_type decl)).[ σ ] ×
    (forall b,
        decl.(decl_body) = Some b ->
        σ x = b.[⇑^(S x) σ]
    ).

Notation "Σ ;;; Δ ⊢ σ : Γ" :=
  (well_subst Σ Γ σ Δ) (at level 50, Δ, σ, Γ at next level).

Lemma well_subst_Up :
  forall Σ Γ Δ σ na A,
    wf_local Σ (Δ ,, vass na A.[σ]) ->
    Σ ;;; Δ ⊢ σ : Γ ->
    Σ ;;; Δ ,, vass na A.[σ] ⊢ ⇑ σ : Γ ,, vass na A.
Proof.
  intros Σ Γ Δ σ na A hΔ h [|n] decl e.
  - simpl in *. inversion e. subst. clear e. simpl.
    split.
    + eapply meta_conv.
      * econstructor ; auto.
        reflexivity.
      * simpl. rewrite !lift_rename.
        autorewrite with sigma.
        eapply inst_ext. intro i.
        unfold subst_compose.
        eapply inst_ext. intro j.
        unfold shift, ren. reflexivity.
    + intros b e. discriminate.
  - simpl in *.
    specialize (h _ _ e) as [h1 h2].
    split.
Admitted.

Lemma well_subst_Up' :
  forall Σ Γ Δ σ na t A,
    Σ ;;; Δ ⊢ σ : Γ ->
    Σ ;;; Δ ,, vdef na t.[σ] A.[σ] ⊢ ⇑ σ : Γ ,, vdef na t A.
Proof.
  intros Σ Γ Δ σ na t A h [|n] decl e.
  - simpl in *. inversion e. subst. clear e. simpl.
    (* NEED commutation lemma between lift and inst *)
    admit.
  - simpl in *.
    specialize (h _ _ e).
Admitted.

Lemma instantiate_params_subst_inst :
  forall params pars s t σ s' t',
    instantiate_params_subst params pars s t = Some (s', t') ->
    instantiate_params_subst
      (mapi_rec (fun i decl => inst_decl (⇑^i σ) decl) params #|s|)
      (map (inst σ) pars)
      (map (inst σ) s)
      t.[⇑^#|s| σ]
    = Some (map (inst σ) s', t'.[⇑^(#|s| + #|params|) σ]).
Proof.
  intros params pars s t σ s' t' h.
  induction params in pars, s, t, σ, s', t', h |- *.
  - simpl in *. destruct pars. 2: discriminate.
    simpl. inversion h. subst. clear h.
    f_equal. f_equal. f_equal. f_equal. omega.
  - simpl in *. destruct (decl_body a).
    + simpl. destruct t. all: try discriminate.
      simpl. eapply IHparams with (σ := σ) in h.
      simpl in h.
      replace (#|s| + S #|params|)
        with (S (#|s| + #|params|))
        by omega.
      rewrite <- h. f_equal.
      * f_equal. autorewrite with sigma.
        eapply inst_ext. intro i.
        unfold Upn, subst_consn, subst_compose.
        case_eq (nth_error s i).
        -- intros t e.
           rewrite nth_error_idsn_Some.
           ++ eapply nth_error_Some_length. eassumption.
           ++ simpl.
              rewrite nth_error_map. rewrite e. simpl.
              reflexivity.
        -- intro neq.
           rewrite nth_error_idsn_None.
           ++ eapply nth_error_None. assumption.
           ++ simpl. rewrite idsn_length.
              autorewrite with sigma.
              rewrite <- subst_ids. eapply inst_ext. intro j.
              cbn. unfold ids. rewrite map_length.
              replace (#|s| + j - #|s|) with j by omega.
              rewrite nth_error_map.
              erewrite (iffRL (nth_error_None _ _)) by omega.
              simpl. reflexivity.
      * autorewrite with sigma. reflexivity.
    + simpl. destruct t. all: try discriminate.
      simpl. destruct pars. 1: discriminate.
      simpl. eapply IHparams with (σ := σ) in h. simpl in h.
      replace (#|s| + S #|params|)
        with (S (#|s| + #|params|))
        by omega.
      rewrite <- h.
      f_equal. autorewrite with sigma. reflexivity.
Qed.

Lemma inst_decl_closed :
  forall σ k d,
    closed_decl k d ->
    inst_decl (⇑^k σ) d = d.
Proof.
  intros σ k d.
  case: d => na [body|] ty. all: rewrite /closed_decl /inst_decl /map_decl /=.
  - move /andP => [cb cty]. rewrite !inst_closed //.
  - move => cty. rewrite !inst_closed //.
Qed.

Lemma closed_tele_inst :
  forall σ ctx,
    closed_ctx ctx ->
    mapi (fun i decl => inst_decl (⇑^i σ) decl) (List.rev ctx) =
    List.rev ctx.
Proof.
  intros σ ctx.
  rewrite /closedn_ctx /mapi. simpl. generalize 0.
  induction ctx using rev_ind; try easy.
  move => n.
  rewrite /closedn_ctx !rev_app_distr /id /=.
  move /andP => [closedx Hctx].
  rewrite inst_decl_closed //.
  f_equal. now rewrite IHctx.
Qed.

(* (* Could be more precise *) *)
(* Lemma instantiate_params_subst_length : *)
(*   forall params pars s t s' t', *)
(*     instantiate_params_subst params pars s t = Some (s', t') -> *)
(*     #|params| >= #|pars|. *)
(* Proof. *)
(*   intros params pars s t s' t' h. *)
(*   induction params in pars, s, t, s', t', h |- *. *)
(*   - cbn in h. destruct pars. all: try discriminate. auto. *)
(*   - cbn in h. destruct (decl_body a). *)
(*     + destruct t. all: try discriminate. *)
(*       cbn. eapply IHparams in h. lia. *)
(*     + destruct t. all: try discriminate. *)
(*       destruct pars. 1: discriminate. *)
(*       cbn. eapply IHparams in h. lia. *)
(* Qed. *)

(* Lemma instantiate_params_length : *)
(*   forall params pars T T', *)
(*     instantiate_params params pars T = Some T' -> *)
(*     #|params| >= #|pars|. *)
(* Proof. *)
(*   intros params pars T T' e. *)
(*   unfold instantiate_params in e. *)
(*   case_eq (instantiate_params_subst (List.rev params) pars [] T) ; *)
(*     try solve [ intro bot ; rewrite bot in e ; discriminate e ]. *)
(*   intros [s' t'] e'. rewrite e' in e. inversion e. subst. clear e. *)
(*   eapply instantiate_params_subst_length in e'. *)
(*   rewrite List.rev_length in e'. assumption. *)
(* Qed. *)

(* Could be more precise *)
Lemma instantiate_params_subst_length :
  forall params pars s t s' t',
    instantiate_params_subst params pars s t = Some (s', t') ->
    #|params| + #|s| = #|s'|.
Proof.
  intros params pars s t s' t' h.
  induction params in pars, s, t, s', t', h |- *.
  - cbn in h. destruct pars. all: try discriminate.
    inversion h. reflexivity.
  - cbn in h. destruct (decl_body a).
    + destruct t. all: try discriminate.
      cbn. eapply IHparams in h. cbn in h. lia.
    + destruct t. all: try discriminate.
      destruct pars. 1: discriminate.
      cbn. eapply IHparams in h. cbn in h. lia.
Qed.

Lemma instantiate_params_inst :
  forall params pars T σ T',
    closed_ctx params ->
    instantiate_params params pars T = Some T' ->
    instantiate_params params (map (inst σ) pars) T.[σ] = Some T'.[σ].
Proof.
  intros params pars T σ T' hcl e.
  unfold instantiate_params in *.
  case_eq (instantiate_params_subst (List.rev params) pars [] T) ;
    try solve [ intro bot ; rewrite bot in e ; discriminate e ].
  intros [s' t'] e'. rewrite e' in e. inversion e. subst. clear e.
  eapply instantiate_params_subst_inst with (σ := σ) in e'.
  simpl in e'.
  autorewrite with sigma in e'.
  rewrite List.rev_length in e'.
  match type of e' with
  | context [ mapi_rec ?f ?l 0 ] =>
    change (mapi_rec f l 0) with (mapi f l) in e'
  end.
  rewrite closed_tele_inst in e' ; auto.
  rewrite e'. f_equal. autorewrite with sigma.
  eapply inst_ext. intro i.
  unfold Upn, subst_consn, subst_compose.
  rewrite idsn_length map_length.
  apply instantiate_params_subst_length in e'.
  rewrite List.rev_length map_length in e'. cbn in e'.
  replace (#|params| + 0) with #|params| in e' by lia.
  rewrite e'. clear e'.
  case_eq (nth_error s' i).
  - intros t e.
    rewrite nth_error_idsn_Some.
    { eapply nth_error_Some_length in e. lia. }
    simpl.
    rewrite nth_error_map. rewrite e. simpl. reflexivity.
  - intro neq.
    rewrite nth_error_idsn_None.
    { eapply nth_error_None in neq. lia. }
    simpl. autorewrite with sigma. rewrite <- subst_ids.
    eapply inst_ext. intro j.
    cbn. unfold ids.
    replace (#|s'| + j - #|s'|) with j by omega.
    rewrite nth_error_map.
    erewrite (iffRL (nth_error_None _ _)) by omega.
    simpl. reflexivity.
Qed.

Lemma typed_inst :
  forall Σ Γ t T k σ,
    wf Σ.1 ->
    k >= #|Γ| ->
    Σ ;;; Γ |- t : T ->
    T.[⇑^k σ] = T /\ t.[⇑^k σ] = t.
Proof.
  intros Σ Γ t T k σ hΣ hk h.
  apply typing_wf_local in h as hΓ.
  apply typecheck_closed in h. all: eauto.
  destruct h as [_ hcl].
  rewrite -> andb_and in hcl. destruct hcl as [clt clT].
  pose proof (closed_upwards k clt) as ht.
  pose proof (closed_upwards k clT) as hT.
  forward ht by lia.
  forward hT by lia.
  rewrite !inst_closed. all: auto.
Qed.

Lemma inst_wf_local :
  forall Σ Γ σ,
    wf Σ.1 ->
    wf_local Σ Γ ->
    inst_context σ Γ = Γ.
Proof.
  intros Σ Γ σ hΣ h.
  induction h.
  - reflexivity.
  - unfold inst_context, snoc. rewrite fold_context_snoc0.
    unfold snoc. f_equal. all: auto.
    unfold map_decl. simpl. unfold vass. f_equal.
    destruct t0 as [s ht]. eapply typed_inst. all: eauto.
  - unfold inst_context, snoc. rewrite fold_context_snoc0.
    unfold snoc. f_equal. all: auto.
    unfold map_decl. simpl. unfold vdef. f_equal.
    + f_equal. eapply typed_inst. all: eauto.
    + eapply typed_inst in t1 as [? _]. all: eauto.
Qed.

Definition inst_mutual_inductive_body σ m :=
  map_mutual_inductive_body (fun i => inst (⇑^i σ)) m.

Lemma inst_declared_minductive :
  forall Σ cst decl σ,
    wf Σ ->
    declared_minductive Σ cst decl ->
    inst_mutual_inductive_body σ decl = decl.
Proof.
  unfold declared_minductive.
  intros Σ cst decl σ hΣ h.
  eapply lookup_on_global_env in h ; eauto. simpl in h.
  destruct h as [Σ' [hΣ' decl']].
  destruct decl as [fi npars params bodies univs]. simpl. f_equal.
  - eapply inst_wf_local. all: eauto.
    eapply onParams in decl'. auto.
  - apply onInductives in decl'.
    revert decl'. generalize bodies at 2 4 5. intros bodies' decl'.
    eapply Alli_mapi_id in decl'. all: eauto.
    clear decl'. intros n [na ty ke ct pr] hb. simpl.
    destruct (decompose_prod_assum [] ty) as [c t] eqn:e1.
    destruct (decompose_prod_assum [] ty.[⇑^0 σ]) as [c' t'] eqn:e2.
    destruct hb as [indices s arity_eq onAr onConstr onProj sorts].
    simpl in *.
    assert (e : ty.[⇑^0 σ] = ty).
    { destruct onAr as [s' h'].
      eapply typed_inst in h' as [_ ?]. all: eauto.
    }
    rewrite e in e2. rewrite e1 in e2.
    revert e2. intros [= <- <-].
    rewrite e. f_equal.
    + apply (Alli_map_id onConstr).
      intros n1 [[x p] n'] [[s' hty] _].
      unfold on_pi2. simpl. f_equal. f_equal.
      eapply typed_inst. all: eauto.
    + destruct (eq_dec pr []) as [hp | hp]. all: subst. all: auto.
      specialize (onProj hp).
      apply on_projs in onProj.
      apply (Alli_map_id onProj).
      intros n1 [x p]. unfold on_projection. simpl.
      intros [? hty].
      unfold on_snd. simpl. f_equal.
      eapply typed_inst. all: eauto.
      simpl.
      rewrite smash_context_length context_assumptions_fold.
      simpl. auto.
Qed.

Lemma inst_declared_inductive :
  forall Σ ind mdecl idecl σ,
    wf Σ ->
    declared_inductive Σ mdecl ind idecl ->
    map_one_inductive_body
      (context_assumptions mdecl.(ind_params))
      #|arities_context mdecl.(ind_bodies)|
      (fun i => inst (⇑^i σ))
      ind.(inductive_ind)
      idecl
    = idecl.
Proof.
  intros Σ ind mdecl idecl σ hΣ [hmdecl hidecl].
  eapply inst_declared_minductive with (σ := σ) in hmdecl. all: auto.
  unfold inst_mutual_inductive_body in hmdecl.
  destruct mdecl as [fi npars params bodies univs]. simpl in *.
  injection hmdecl. intro e. clear hmdecl.
  pose proof hidecl as hidecl'.
  rewrite <- e in hidecl'.
  rewrite nth_error_mapi in hidecl'.
  clear e.
  unfold option_map in hidecl'. rewrite hidecl in hidecl'.
  congruence.
Qed.

Lemma inst_destArity :
  forall ctx t σ args s,
    destArity ctx t = Some (args, s) ->
    destArity (inst_context σ ctx) t.[⇑^#|ctx| σ] =
    Some (inst_context σ args, s).
Proof.
  intros ctx t σ args s h.
  induction t in ctx, σ, args, s, h |- * using term_forall_list_ind.
  all: simpl in *. all: try discriminate.
  - inversion h. reflexivity.
  - erewrite <- IHt2 ; try eassumption.
    simpl. autorewrite with sigma. reflexivity.
  - erewrite <- IHt3. all: try eassumption.
    simpl. autorewrite with sigma. reflexivity.
Qed.

Lemma shift_subst_instance_constr :
  forall u t k,
    (subst_instance_constr u t).[⇑^k ↑] = subst_instance_constr u t.[⇑^k ↑].
Proof.
  intros u t k.
  induction t in k |- * using term_forall_list_ind.
  all: simpl. all: auto.
  all: autorewrite with sigma.
  all: rewrite ?map_map_compose ?compose_on_snd ?compose_map_def ?map_lenght.
  all: try solve [ f_equal ; eauto ; solve_all ; eauto ].
  - unfold Upn, shift, subst_compose, subst_consn.
    destruct (Nat.ltb_spec0 n k).
    + rewrite nth_error_idsn_Some. 1: assumption.
      reflexivity.
    + rewrite nth_error_idsn_None. 1: lia.
      reflexivity.
  - rewrite IHt1. specialize (IHt2 (S k)). autorewrite with sigma in IHt2.
    rewrite IHt2. reflexivity.
  - rewrite IHt1. specialize (IHt2 (S k)). autorewrite with sigma in IHt2.
    rewrite IHt2. reflexivity.
  - rewrite IHt1 IHt2. specialize (IHt3 (S k)). autorewrite with sigma in IHt3.
    rewrite IHt3. reflexivity.
  - f_equal.
    (* induction X in k |- *. *)
    (* + simpl. reflexivity. *)
    (* + simpl. intuition eauto. *)
    (*   f_equal. *)
    (*   * unfold map_def. unfold compose. rewrite a. *)
    (*     rewrite map_length. autorewrite with sigma. *)
    (*     specialize (b (S (#|l| + k))). autorewrite with sigma in b. *)
    (*     rewrite b. reflexivity. *)
    (*   * rewrite map_length. rewrite map_length in IHX. *)
    admit.
  - admit.
Admitted.

Lemma inst_subst_instance_constr :
  forall u t σ,
    (subst_instance_constr u t).[(subst_instance_constr u ∘ σ)%prog] =
    subst_instance_constr u t.[σ].
Proof.
  intros u t σ.
  induction t in σ |- * using term_forall_list_ind.
  all: simpl. all: auto.
  all: autorewrite with sigma.
  all: rewrite ?map_map_compose ?compose_on_snd ?compose_map_def ?map_lenght.
  all: try solve [ f_equal ; eauto ; solve_all ; eauto ].
  - rewrite IHt1. f_equal. rewrite <- IHt2.
    eapply inst_ext. intro i.
    unfold compose, Up, subst_compose, subst_cons.
    destruct i.
    + reflexivity.
    + pose proof (shift_subst_instance_constr u (σ i) 0) as e.
      autorewrite with sigma in e. rewrite e. reflexivity.
  -
Admitted.

Lemma build_branches_type_inst :
  forall ind mdecl idecl args u p brs σ,
    closed_ctx (ind_params mdecl) ->
    map_option_out (build_branches_type ind mdecl idecl args u p) = Some brs ->
    map_option_out (
        build_branches_type
          ind
          mdecl
          (map_one_inductive_body
             (context_assumptions (ind_params mdecl))
             #|arities_context (ind_bodies mdecl)|
             (fun i : nat => inst (⇑^i σ))
             (inductive_ind ind)
             idecl
          )
          (map (inst σ) args)
          u
          p.[σ]
    ) = Some (map (on_snd (inst σ)) brs).
Proof.
  intros ind mdecl idecl args u p brs σ hcl.
  unfold build_branches_type.
  destruct idecl as [ina ity ike ict ipr]. simpl.
  unfold mapi.
  generalize 0 at 3 6.
  intros n h.
  induction ict in brs, n, h, σ |- *.
  - cbn in *. inversion h. reflexivity.
  - cbn. cbn in h.
    lazymatch type of h with
    | match ?t with _ => _ end = _ =>
      case_eq (t) ;
        try (intro bot ; rewrite bot in h ; discriminate h)
    end.
    intros [m t] e'. rewrite e' in h.
    destruct a as [[na ta] ar].
    lazymatch type of e' with
    | match ?expr with _ => _ end = _ =>
      case_eq (expr) ;
        try (intro bot ; rewrite bot in e' ; discriminate e')
    end.
    intros ty ety. rewrite ety in e'.
    eapply instantiate_params_inst with (σ := σ) in ety as ety'. 2: assumption.
    autorewrite with sigma. simpl.
    autorewrite with sigma in ety'.
    rewrite <- inst_subst_instance_constr.
    autorewrite with sigma.
    match goal with
    | |- context [ instantiate_params _ _ ?t.[?σ] ] =>
      match type of ety' with
      | instantiate_params _ _ ?t'.[?σ'] = _ =>
        replace t.[σ] with t'.[σ'] ; revgoals
      end
    end.
    { eapply inst_ext. intro i.
      unfold Upn, compose, subst_compose, subst_consn.
      rewrite arities_context_length.
      case_eq (nth_error (inds (inductive_mind ind) u (ind_bodies mdecl)) i).
      - intros t' e.
        rewrite nth_error_idsn_Some.
        { eapply nth_error_Some_length in e.
          rewrite inds_length in e. assumption.
        }
        simpl. rewrite e.
        give_up.
      - intro neq. simpl. rewrite inds_length idsn_length.
        rewrite nth_error_idsn_None.
        { eapply nth_error_None in neq. rewrite inds_length in neq. lia. }
        give_up.
    }
    rewrite ety'.
    case_eq (decompose_prod_assum [] ty). intros sign ccl edty.
    rewrite edty in e'.
    (* TODO inst edty *)
    case_eq (chop (ind_npars mdecl) (snd (decompose_app ccl))).
    intros paramrels args' ech. rewrite ech in e'.
    (* TODO inst ech *)
    inversion e'. subst. clear e'.
    lazymatch type of h with
    | match ?t with _ => _ end = _ =>
      case_eq (t) ;
        try (intro bot ; rewrite bot in h ; discriminate h)
    end.
    intros tl etl. rewrite etl in h.
    (* TODO inst etl *)
    inversion h. subst. clear h.
    (* edestruct IHict as [brtys' [eq' he]]. *)
    (* + eauto. *)
    (* + eexists. rewrite eq'. split. *)
    (*   * reflexivity. *)
    (*   * constructor ; auto. *)
    (*     simpl. split ; auto. *)
    (*     eapply eq_term_upto_univ_it_mkProd_or_LetIn ; auto. *)
    (*     eapply eq_term_upto_univ_mkApps. *)
    (*     -- eapply eq_term_upto_univ_lift. assumption. *)
    (*     -- apply All2_same. intro. apply eq_term_upto_univ_refl ; auto. *)
Admitted.

Lemma types_of_case_inst :
  forall Σ ind mdecl idecl npar args u p pty indctx pctx ps btys σ,
    wf Σ ->
    declared_inductive Σ mdecl ind idecl ->
    types_of_case ind mdecl idecl (firstn npar args) u p pty =
    Some (indctx, pctx, ps, btys) ->
    types_of_case ind mdecl idecl (firstn npar (map (inst σ) args)) u p.[σ] pty.[σ] =
    Some (inst_context σ indctx, inst_context σ pctx, ps, map (on_snd (inst σ)) btys).
Proof.
  intros Σ ind mdecl idecl npar args u p pty indctx pctx ps btys σ hΣ hdecl h.
  unfold types_of_case in *.
  case_eq (instantiate_params (ind_params mdecl) (firstn npar args) (ind_type idecl)) ;
    try solve [ intro bot ; rewrite bot in h ; discriminate h ].
  intros ity eity. rewrite eity in h.
  pose proof (on_declared_inductive hΣ hdecl) as [onmind onind].
  apply onParams in onmind as Hparams.
  assert (closedparams : closed_ctx (ind_params mdecl)).
  { eapply PCUICWeakening.closed_wf_local. all: eauto. eauto. }
  epose proof (inst_declared_inductive _ ind mdecl idecl σ hΣ) as hi.
  forward hi by assumption. rewrite <- hi.
  eapply instantiate_params_inst with (σ := σ) in eity ; auto.
  rewrite -> ind_type_map.
  rewrite firstn_map.
  autorewrite with sigma.
  rewrite eity.
  case_eq (destArity [] ity) ;
    try solve [ intro bot ; rewrite bot in h ; discriminate h ].
  intros [args0 ?] ear. rewrite ear in h.
  eapply inst_destArity with (σ := σ) in ear as ear'.
  simpl in ear'. autorewrite with sigma in ear'.
  rewrite ear'.
  case_eq (destArity [] pty) ;
    try solve [ intro bot ; rewrite bot in h ; discriminate h ].
  intros [args' s'] epty. rewrite epty in h.
  eapply inst_destArity with (σ := σ) in epty as epty'.
  simpl in epty'. autorewrite with sigma in epty'.
  rewrite epty'.
  case_eq (map_option_out (build_branches_type ind mdecl idecl (firstn npar args) u p)) ;
    try solve [ intro bot ; rewrite bot in h ; discriminate h ].
  intros brtys ebrtys. rewrite ebrtys in h.
  inversion h. subst. clear h.
  eapply build_branches_type_inst with (σ := σ) in ebrtys as ebrtys'.
  2: assumption.
  rewrite ebrtys'. reflexivity.
Qed.

Lemma type_inst :
  forall Σ Γ Δ σ t A,
    wf Σ.1 ->
    wf_local Σ Γ ->
    wf_local Σ Δ ->
    Σ ;;; Δ ⊢ σ : Γ ->
    Σ ;;; Γ |- t : A ->
    Σ ;;; Δ |- t.[σ] : A.[σ].
Proof.
  intros Σ Γ Δ σ t A hΣ hΓ hΔ hσ h.
  revert Σ hΣ Γ hΓ t A h Δ σ hΔ hσ.
  apply (typing_ind_env (fun Σ Γ t T => forall Δ σ,
    wf_local Σ Δ ->
    Σ ;;; Δ ⊢ σ : Γ ->
    Σ ;;; Δ |- t.[σ] : T.[σ]
  )).
  - intros Σ wfΣ Γ wfΓ n decl e X Δ σ hΔ hσ. simpl.
    eapply hσ. assumption.
  - intros Σ wfΣ Γ wfΓ l X H0 Δ σ hΔ hσ. simpl.
    econstructor. all: assumption.
  - intros Σ wfΣ Γ wfΓ na A B s1 s2 X hA ihA hB ihB Δ σ hΔ hσ.
    autorewrite with sigma. simpl.
    econstructor.
    + eapply ihA ; auto.
    + eapply ihB.
      * econstructor ; auto.
        eexists. eapply ihA ; auto.
      * eapply well_subst_Up. 2: assumption.
        econstructor ; auto.
        eexists. eapply ihA. all: auto.
  - intros Σ wfΣ Γ wfΓ na A t s1 bty X hA ihA ht iht Δ σ hΔ hσ.
    autorewrite with sigma.
    econstructor.
    + eapply ihA ; auto.
    + eapply iht.
      * econstructor ; auto.
        eexists. eapply ihA ; auto.
      * eapply well_subst_Up. 2: assumption.
        constructor. 1: assumption.
        eexists. eapply ihA. all: auto.
  - intros Σ wfΣ Γ wfΓ na b B t s1 A X hB ihB hb ihb ht iht Δ σ hΔ hσ.
    autorewrite with sigma.
    econstructor.
    + eapply ihB. all: auto.
    + eapply ihb. all: auto.
    + eapply iht.
      * econstructor. all: auto.
        -- eexists. eapply ihB. all: auto.
        -- simpl. eapply ihb. all: auto.
      * eapply well_subst_Up'. assumption.
  - intros Σ wfΣ Γ wfΓ t na A B u X ht iht hu ihu Δ σ hΔ hσ.
    autorewrite with sigma.
    (* NEED Relation between inst and subst *)
    admit.
  - intros Σ wfΣ Γ wfΓ cst u decl X X0 isdecl hconst Δ σ hΔ hσ.
    (* autorewrite with sigma. *) simpl.
    (* NEED Commutation *)
    admit.
  - intros Σ wfΣ Γ wfΓ ind u mdecl idecl isdecl X X0 hconst Δ σ hΔ hσ.
    (* autorewrite with sigma. *) simpl.
    (* NEED Commutation *)
    admit.
  - intros Σ wfΣ Γ wfΓ ind i u mdecl idecl cdecl isdecl X X0 hconst Δ σ hΔ hσ.
    (* autorewrite with sigma. *) simpl.
    (* NEED Commutation *)
    admit.
  - intros Σ wfΣ Γ wfΓ ind u npar p c brs args mdecl idecl isdecl X X0 e pars
           pty hp indctx pctx ps btys htoc hca hel ihp hc ihc hbrs Δ σ hΔ hσ.
    autorewrite with sigma. simpl.
    rewrite map_app. simpl.
    rewrite map_skipn.
    eapply types_of_case_inst with (σ := σ) in htoc. all: try eassumption.
    eapply type_Case.
    + eassumption.
    + assumption.
    + eapply ihp. all: auto.
    + eassumption.
    + admit.
    + assumption.
    + specialize (ihc _ _ hΔ hσ). autorewrite with sigma in ihc.
      eapply ihc.
    + admit.
  - intros Σ wfΣ Γ wfΓ p c u mdecl idecl pdecl isdecl args X X0 hc ihc e ty
           Δ σ hΔ hσ.
    autorewrite with sigma. simpl.
    admit.
  - intros Σ wfΣ Γ wfΓ mfix n decl types H0 H1 X ihmfix Δ σ hΔ hσ.
    autorewrite with sigma.
    admit.
  - intros Σ wfΣ Γ wfΓ mfix n decl types H0 X X0 ihmfix Δ σ hΔ hσ.
    autorewrite with sigma.
    admit.
  - intros Σ wfΣ Γ wfΓ t A B X ht iht hwf hcu Δ σ hΔ hσ.
    eapply type_Cumul.
    + eapply iht. all: auto.
    + destruct hwf as [[[ctx [s [? ?]]] ?] | [s [? ihB]]].
      * left. eexists _,_. split.
        -- admit.
        -- admit.
      * right. eexists. eapply ihB. all: auto.
    + admit.
Admitted.

End Sigma.