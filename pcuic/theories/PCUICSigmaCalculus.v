(* Distributed under the terms of the MIT license.   *)
From Equations Require Import Equations.
From Coq Require Import Bool String List BinPos Compare_dec Omega Lia.
Require Import Coq.Program.Syntax Coq.Program.Basics.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICUnivSubst
     PCUICTyping PCUICWeakeningEnv PCUICClosed PCUICReduction.
Require Import ssreflect ssrbool.

(** * Type preservation for σ-calculus *)

Set Asymmetric Patterns.

Section Sigma.

Context `{checker_flags}.

Open Scope sigma_scope.

(* Well-typedness of a substitution *)

Definition well_subst Σ (Γ : context) σ (Δ : context) :=
  forall x decl,
    nth_error Γ x = Some decl ->
    Σ ;;; Δ |- σ x : ((lift0 (S x)) (decl_type decl)).[ σ ].

Notation "Σ ;;; Δ ⊢ σ : Γ" :=
  (well_subst Σ Γ σ Δ) (at level 50, Δ, σ, Γ at next level).

Lemma well_subst_Up :
  forall Σ Γ Δ σ na A,
    Σ ;;; Δ ⊢ σ : Γ ->
    Σ ;;; Δ ,, vass na A.[σ] ⊢ ⇑ σ : Γ ,, vass na A.
Proof.
  intros Σ Γ Δ σ na A h [|n] decl e.
  - simpl in *. inversion e. subst. clear e. simpl.
    (* NEED commutation lemma between lift and inst *)
    admit.
  - simpl in *.
    specialize (h _ _ e).
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

Lemma instantiate_params_subst_inst :
  forall params pars s t σ s' t',
    instantiate_params_subst params pars s t = Some (s', t') ->
    instantiate_params_subst
      (mapi_rec (fun i decl => map_decl (inst (⇑^i σ)) decl) params #|s|)
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
    map_decl (inst (⇑^k σ)) d = d.
Proof.
  intros σ k d.
  case: d => na [body|] ty. all: rewrite /closed_decl /map_decl /=.
  - move /andP => [cb cty]. rewrite !inst_closed //.
  - move => cty. rewrite !inst_closed //.
Qed.

Lemma closed_tele_inst :
  forall σ ctx,
    closed_ctx ctx ->
    mapi (fun i decl => map_decl (inst (⇑^i σ)) decl) (List.rev ctx) =
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

Definition inst_context σ (Γ : context) : context :=
  fold_context (fun i => inst (⇑^i σ)) Γ.

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

(* Maybe remove later? *)
Require PCUICWeakening.

Lemma types_of_case_inst :
  forall Σ ind mdecl idecl npar args u p pty indctx pctx ps btys σ,
    wf Σ ->
    declared_inductive Σ mdecl ind idecl ->
    types_of_case ind mdecl idecl (firstn npar args) u p pty =
    Some (indctx, pctx, ps, btys) ->
    types_of_case ind mdecl idecl (firstn npar (map (inst σ) args)) u p.[σ] pty.[σ] =
    Some (indctx, pctx, ps, btys).
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
  (* eapply instantiate_params_inst with (σ := σ) in eity. *)


  (* rewrite firstn_map. *)


(* ind_type_map *)

  (* case_eq (destArity [] ity) ; *)
  (*   try solve [ intro bot ; rewrite bot in h ; discriminate h ]. *)
  (* intros [args0 ?] ear. rewrite ear in h. *)
  (* case_eq (destArity [] pty) ; *)
  (*   try solve [ intro bot ; rewrite bot in h ; discriminate h ]. *)
  (* intros [args' s'] ear'. rewrite ear' in h. *)
  (* case_eq (map_option_out (build_branches_type ind mdecl idecl (firstn npar args) u p)) ; *)
  (*   try solve [ intro bot ; rewrite bot in h ; discriminate h ]. *)
  (* intros brtys ebrtys. rewrite ebrtys in h. *)
  (* eapply build_branches_type_eq_term in ebrtys as [brtys' [ebrtys' he]] ; eauto. *)
  (* inversion htc. subst. clear htc. *)
  (* rewrite ebrtys'. intuition eauto. *)
Abort.

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
      * eapply well_subst_Up. assumption.
  - intros Σ wfΣ Γ wfΓ na A t s1 bty X hA ihA ht iht Δ σ hΔ hσ.
    autorewrite with sigma.
    econstructor.
    + eapply ihA ; auto.
    + eapply iht.
      * econstructor ; auto.
        eexists. eapply ihA ; auto.
      * eapply well_subst_Up. assumption.
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
    eapply type_Case.
    + eassumption.
    + assumption.
    + eapply ihp. all: auto.
    + admit.
    + admit.
    + admit.
    + admit.
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