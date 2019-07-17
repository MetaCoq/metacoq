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

(* TODO DUPLICATE MOVE *)
Definition on_pair {A B C D} (f : A -> B) (g : C -> D) (x : A * C) :=
  (f (fst x), g (snd x)).

Lemma instantiate_params_subst_inst :
  forall params pars s ty σ,
    instantiate_params_subst
      (mapi_rec (fun i decl => map_decl (inst (⇑^i σ)) decl) params #|s|)
      (map (inst σ) pars)
      (map (inst σ) s)
      ty.[⇑^#|s| σ]
    =
    option_map
      (on_pair (map (inst σ)) (inst (⇑^(#|s| + #|params|) σ)))
      (instantiate_params_subst params pars s ty).
Proof.
  intros params pars s ty σ.
  induction params in pars, s, ty, σ |- *.
  - simpl. destruct pars. 2: reflexivity.
    simpl. unfold on_pair. simpl. f_equal. f_equal. f_equal. f_equal. omega.
  - simpl. destruct (decl_body a).
    + simpl. destruct ty. all: try reflexivity.
      * simpl. admit.
      * simpl. specialize (IHparams pars ((subst0 s) t :: s)).
        simpl in IHparams.
        replace (#|s| + S #|params|)
          with (S (#|s| + #|params|))
          by omega.
        rewrite <- IHparams. f_equal.
        -- f_equal. autorewrite with sigma.
           eapply inst_ext. intro i.
           unfold Upn, subst_consn, subst_compose.

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

           case_eq (nth_error s i).
           ++ intros t' e.
              rewrite nth_error_idsn_Some.
              ** eapply nth_error_Some_length. eassumption.
              ** simpl.
                 rewrite nth_error_map. rewrite e. simpl.
                 reflexivity.
           ++ intro neq.

Lemma nth_error_idsn_None :
  forall n k,
    k >= n ->
    nth_error (idsn n) k = None.
Proof.
  intros n k h.
  eapply nth_error_None.
  rewrite idsn_length. auto.
Qed.

              rewrite nth_error_idsn_None.
              ** eapply nth_error_None. assumption.
              ** simpl. rewrite idsn_length.
                 autorewrite with sigma.



(*     instantiate_params_subst params pars s ty = Some (s', T) -> *)
(*     instantiate_params_subst params (map (inst σ) pars) (map (inst σ) s) ty = *)
(*     Some (map (inst σ) s', T). *)
(* Proof. *)
(*   intros params pars s ty σ s' T e. *)
(*   induction params in pars, s, ty, σ, s', T, e |- *. *)
(*   - simpl in *. destruct pars ; try discriminate. *)
(*     inversion e. subst. clear e. *)
(*     simpl. reflexivity. *)
(*   - simpl in *. *)
(*     destruct (decl_body a). *)
(*     + destruct ty. all: try discriminate e. *)
(*       eapply IHparams with (σ := σ) in e as ih. simpl in ih. *)
(*       rewrite <- ih. f_equal. f_equal. *)
(*       autorewrite with sigma. *)
(*       eapply inst_ext. intro i. *)
(*       unfold subst_consn, subst_compose. *)
(*       rewrite nth_error_map. *)
(*       destruct (nth_error s i). *)
(*       * simpl. reflexivity. *)
(*       * simpl. give_up. *)
Abort.

Lemma instantiate_params_inst :
  forall params pars T σ T',
    instantiate_params params pars T = Some T' ->
    instantiate_params params (map (inst σ) pars) T = Some T'.[σ].
Proof.
  intros params pars T σ T'.
  unfold instantiate_params.
  change (@nil term) with (map (inst σ) []) at 2.
  generalize (@nil term).
  generalize (List.rev params). clear params.
  intros params s e.
  case_eq (instantiate_params_subst params pars s T) ;
    try solve [ intro bot ; rewrite bot in e ; discriminate e ].
  intros [s' ty] e'. rewrite e' in e. inversion e. subst. clear e.
  induction params in σ, pars, s, T, s', ty, e' |- *.
  - simpl in e'. simpl. destruct pars. all: try discriminate e'.
    inversion e'. subst. clear e'.
    simpl. autorewrite with sigma.
    (* TODO LEMMA *)
    f_equal. eapply inst_ext.
    intro i. unfold subst_consn. unfold subst_compose.
    rewrite nth_error_map.
    destruct (nth_error s' i).
    + simpl. reflexivity.
    + simpl. rewrite map_length.
      (* There is something wrong *)
      give_up.
  - simpl in e'. simpl.
    case_eq (decl_body a).
    + intros t e. rewrite e in e'.
      destruct T. all: try discriminate e'.
      eapply IHparams with (σ := σ) in e'.
      simpl in e'.
      autorewrite with sigma.
      autorewrite with sigma in e'.
(* eassumption. *) give_up.
    + intro neq. rewrite neq in e'.
      destruct T. all: try discriminate e'.
      destruct pars. all: try discriminate.
      simpl. (* eapply IHparams. *)
Abort.

Lemma types_of_case_inst :
  forall ind mdecl idecl npar args u p pty indctx pctx ps btys σ,
    types_of_case ind mdecl idecl (firstn npar args) u p pty =
    Some (indctx, pctx, ps, btys) ->
    types_of_case ind mdecl idecl (firstn npar (map (inst σ) args)) u p.[σ] pty.[σ] =
    Some (indctx, pctx, ps, btys).
Proof.
  intros ind mdecl idecl npar args u p pty indctx pctx ps btys σ h.
  unfold types_of_case in *.
  case_eq (instantiate_params (ind_params mdecl) (firstn npar args) (ind_type idecl)) ;
    try solve [ intro bot ; rewrite bot in h ; discriminate h ].
  intros ity eity. rewrite eity in h.

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