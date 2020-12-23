(* From PCUICSigmaCalculus *)
(*
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
    f_equal. f_equal. f_equal. f_equal. lia.
  - simpl in *. destruct (decl_body a).
    + simpl. destruct t. all: try discriminate.
      simpl. eapply IHparams with (σ := σ) in h.
      simpl in h.
      replace (#|s| + S #|params|)
        with (S (#|s| + #|params|))
        by lia.
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
              replace (#|s| + j - #|s|) with j by lia.
              rewrite nth_error_map.
              erewrite (iffRL (nth_error_None _ _)) by lia.
              simpl. reflexivity.
      * autorewrite with sigma. reflexivity.
    + simpl. destruct t. all: try discriminate.
      simpl. destruct pars. 1: discriminate.
      simpl. eapply IHparams with (σ := σ) in h. simpl in h.
      replace (#|s| + S #|params|)
        with (S (#|s| + #|params|))
        by lia.
      rewrite <- h.
      f_equal. autorewrite with sigma. reflexivity.
Qed. *)

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
  replace (#|s'| + j - #|s'|) with j by lia.
  rewrite nth_error_map.
  erewrite (iffRL (nth_error_None _ _)) by lia.
  simpl. reflexivity.
Qed.

Corollary instantiate_params_rename :
forall params pars T f T',
  closed_ctx params ->
  instantiate_params params pars T = Some T' ->
  instantiate_params params (map (rename f) pars) (rename f T) =
  Some (rename f T').
Proof.
intros params pars T f T' hcl e.
eapply instantiate_params_inst with (σ := ren f) in e. 2: auto.
autorewrite with sigma. rewrite <- e. f_equal.
Qed.

Lemma build_branches_type_rename :
forall ind mdecl idecl args u p brs f,
  closed_ctx (subst_instance_context u (ind_params mdecl)) ->
  map_option_out (build_branches_type ind mdecl idecl args u p) = Some brs ->
  map_option_out (
      build_branches_type
        ind
        mdecl
        (map_one_inductive_body
           (context_assumptions (ind_params mdecl))
           #|arities_context (ind_bodies mdecl)|
           (fun i : nat => rename (shiftn i f))
           (inductive_ind ind)
           idecl
        )
        (map (rename f) args)
        u
        (rename f p)
  ) = Some (map (on_snd (rename f)) brs).
Proof.
intros ind mdecl idecl args u p brs f hcl.
unfold build_branches_type.
destruct idecl as [ina ity ike ict ipr]. simpl.
unfold mapi.
generalize 0 at 3 6.
intros n h.
induction ict in brs, n, h, f |- *.
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
  eapply instantiate_params_rename with (f := f) in ety as ety'.
  2: assumption.
  simpl.
  match goal with
  | |- context [ instantiate_params _ _ ?t ] =>
    match type of ety' with
    | instantiate_params _ _ ?t' = _ =>
      replace t with t' ; revgoals
    end
  end.
  { clear e' ety h IHict ety'.
    rewrite <- rename_subst_instance_constr.
    rewrite arities_context_length.
    autorewrite with sigma.
    eapply inst_ext. intro i.
    unfold shiftn, ren, subst_compose, subst_consn. simpl.
    case_eq (nth_error (inds (inductive_mind ind) u (ind_bodies mdecl)) i).
    + intros t' e.
      eapply nth_error_Some_length in e as hl.
      rewrite inds_length in hl.
      destruct (Nat.ltb_spec i #|ind_bodies mdecl|) ; try lia.
      rewrite e.
      give_up.
    + intro neq.
      eapply nth_error_None in neq as hl.
      rewrite inds_length in hl.
      rewrite inds_length.
      destruct (Nat.ltb_spec i #|ind_bodies mdecl|) ; try lia.
      unfold ids. simpl.
      rewrite (iffRL (nth_error_None _ _)).
      { rewrite inds_length. lia. }
      f_equal. lia.
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


Lemma build_branches_type_inst :
  forall ind mdecl idecl args u p brs σ,
    closed_ctx (subst_instance_context u (ind_params mdecl)) ->
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
      unfold Upn, subst_compose, subst_consn.
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

(* Lemma types_of_case_inst : *)
(*   forall Σ ind mdecl idecl npar args u p pty indctx pctx ps btys σ, *)
(*     wf Σ -> *)
(*     declared_inductive Σ ind mdecl idecl -> *)
(*     types_of_case ind mdecl idecl (firstn npar args) u p pty = *)
(*     Some (indctx, pctx, ps, btys) -> *)
(*     types_of_case ind mdecl idecl (firstn npar (map (inst σ) args)) u p.[σ] pty.[σ] = *)
(*     Some (inst_context σ indctx, inst_context σ pctx, ps, map (on_snd (inst σ)) btys). *)
(* Proof. *)
(*   intros Σ ind mdecl idecl npar args u p pty indctx pctx ps btys σ hΣ hdecl h. *)
(*   unfold types_of_case in *. *)
(*   case_eq (instantiate_params (subst_instance_context u (ind_params mdecl)) (firstn npar args) (subst_instance_constr u (ind_type idecl))) ; *)
(*     try solve [ intro bot ; rewrite bot in h ; discriminate h ]. *)
(*   intros ity eity. rewrite eity in h. *)
(*   pose proof (on_declared_inductive hΣ as hdecl) [onmind onind]. *)
(*   apply onParams in onmind as Hparams. *)
(*   assert (closedparams : closed_ctx (subst_instance_context u (ind_params mdecl))). *)
(*   { rewrite closedn_subst_instance_context. *)
(*     eapply PCUICWeakening.closed_wf_local. all: eauto. eauto. } *)
(*   epose proof (inst_declared_inductive _ mdecl ind idecl σ hΣ) as hi. *)
(*   forward hi by assumption. rewrite <- hi. *)
(*   eapply instantiate_params_inst with (σ := σ) in eity ; auto. *)
(*   rewrite -> ind_type_map. *)
(*   rewrite firstn_map. *)
(*   autorewrite with sigma. *)
(* (*   rewrite eity. *) *)
(* (*   case_eq (destArity [] ity) ; *) *)
(* (*     try solve [ intro bot ; rewrite bot in h ; discriminate h ]. *) *)
(* (*   intros [args0 ?] ear. rewrite ear in h. *) *)
(* (*   eapply inst_destArity with (σ := σ) in ear as ear'. *) *)
(* (*   simpl in ear'. autorewrite with sigma in ear'. *) *)
(* (*   rewrite ear'. *) *)
(* (*   case_eq (destArity [] pty) ; *) *)
(* (*     try solve [ intro bot ; rewrite bot in h ; discriminate h ]. *) *)
(* (*   intros [args' s'] epty. rewrite epty in h. *) *)
(* (*   eapply inst_destArity with (σ := σ) in epty as epty'. *) *)
(* (*   simpl in epty'. autorewrite with sigma in epty'. *) *)
(* (*   rewrite epty'. *) *)
(* (*   case_eq (map_option_out (build_branches_type ind mdecl idecl (firstn npar args) u p)) ; *) *)
(* (*     try solve [ intro bot ; rewrite bot in h ; discriminate h ]. *) *)
(* (*   intros brtys ebrtys. rewrite ebrtys in h. *) *)
(* (*   inversion h. subst. clear h. *) *)
(* (*   eapply build_branches_type_inst with (σ := σ) in ebrtys as ebrtys'. *) *)
(* (*   2: assumption. *) *)
(* (*   rewrite ebrtys'. reflexivity. *) *)
(* (* Qed. *) *)
(* Admitted. *)
