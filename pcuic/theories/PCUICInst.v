
(* Distributed under the terms of the MIT license. *)
From Coq Require Import Morphisms.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICClosed PCUICEquality PCUICWeakeningEnv
  PCUICRename.

Require Import ssreflect ssrbool.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Set Equations With UIP.
Set Keyed Unification.
Set Default Goal Selector "!".

(** * Type preservation for σ-calculus instantiation *)

Open Scope sigma_scope.

Definition inst_context σ (Γ : context) : context :=
  fold_context (fun i => inst (⇑^i σ)) Γ.
  
Definition inst_decl σ d := map_decl (inst σ) d.

Definition inst_context_snoc0 s Γ d :
  inst_context s (d :: Γ) =
  inst_context s Γ ,, map_decl (inst (⇑^#|Γ| s)) d.
Proof. unfold inst_context. now rewrite fold_context_snoc0. Qed.
Hint Rewrite inst_context_snoc0 : sigma.

Lemma inst_context_snoc s Γ d : inst_context s (Γ ,, d) = inst_context s Γ ,, map_decl (inst (⇑^#|Γ| s)) d.
Proof.
  unfold snoc. apply inst_context_snoc0.
Qed.
Hint Rewrite inst_context_snoc : sigma.

Lemma inst_context_alt s Γ :
  inst_context s Γ =
  mapi (fun k' d => map_decl (inst (⇑^(Nat.pred #|Γ| - k') s)) d) Γ.
Proof.
  unfold inst_context. apply fold_context_alt.
Qed.

Lemma inst_context_length s Γ : #|inst_context s Γ| = #|Γ|.
Proof. apply fold_context_length. Qed.
Hint Rewrite inst_context_length : sigma wf.

Lemma inst_mkApps f l σ : (mkApps f l).[σ] = mkApps f.[σ] (map (inst σ) l).
Proof.
  induction l in f |- *; simpl; auto. rewrite IHl.
  now autorewrite with sigma.
Qed.
Hint Rewrite inst_mkApps : sigma.

Lemma lift0_inst n t : lift0 n t = t.[↑^n].
Proof. by rewrite lift_rename rename_inst lift_renaming_0 -ren_shiftk. Qed.
Hint Rewrite lift0_inst : sigma.

Lemma rename_decl_inst_decl :
  forall f d,
    rename_decl f d = inst_decl (ren f) d.
Proof.
  intros f d.
  unfold rename_decl, inst_decl.
  destruct d. unfold map_decl.
  autorewrite with sigma.
  f_equal.
  simpl. destruct decl_body.
  - simpl. f_equal. autorewrite with sigma. reflexivity.
  - reflexivity.
Qed.
Hint Rewrite rename_decl_inst_decl : sigma.

Lemma rename_context_inst_context :
  forall f Γ,
    rename_context f Γ = inst_context (ren f) Γ.
Proof.
  intros f Γ.
  induction Γ.
  - reflexivity.
  - autorewrite with sigma. rewrite IHΓ. f_equal.
    destruct a. unfold inst_decl. unfold map_decl. simpl.
    f_equal.
    + destruct decl_body. 2: reflexivity.
      simpl. f_equal. autorewrite with sigma.
      now rewrite -up_Upn ren_shiftn.
    + autorewrite with sigma.
      now rewrite -up_Upn ren_shiftn.
Qed.
Hint Rewrite rename_context_inst_context : sigma.

Lemma subst10_inst a b τ : b {0 := a}.[τ] = (b.[⇑ τ] {0 := a.[τ]}).
Proof.
  unfold subst10. simpl. rewrite !subst_inst.
  now unfold Upn, Up; autorewrite with sigma.
Qed.
Hint Rewrite subst10_inst : sigma.

Lemma inst_closed0 σ t : closedn 0 t -> t.[σ] = t.
Proof. intros. rewrite -{2}[t](inst_closed σ 0) //. now sigma. Qed.

Lemma inst_ext_closed s s' k t : 
  closedn k t -> 
  (forall x, x < k -> s x = s' x) -> 
  inst s t = inst s' t.
Proof.
  clear.
  intros clt Hs. revert k clt s s' Hs.
  elim t using PCUICInduction.term_forall_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try solve [f_equal; solve_all].
  - apply Hs. now eapply Nat.ltb_lt. 
  - move/andb_and: clt => []. intros. f_equal; eauto.
    eapply H0; eauto. intros. eapply up_ext_closed; eauto.
  - move/andb_and: clt => []. intros. f_equal; eauto. now eapply H0, up_ext_closed.
  - move/andb_and: clt => [] /andb_and[] ?. intros. f_equal; eauto.
    now eapply H1, up_ext_closed.
  - move/andb_and: clt => [] ? ?. f_equal; eauto.
  - move/andb_and: clt => [] /andb_and[] /andP /= [ppars pret] cc b1.
    red in X. f_equal; eauto.
    * unfold test_predicate in *. simpl in *. destruct X. solve_all.
      eapply e; eauto. intros. eapply up_ext_closed; eauto.
    * eapply All_map_eq. red in X0. solve_all.
      unfold map_branch. f_equal. now eapply a0, up_ext_closed.
  - f_equal; eauto. red in X. solve_all.
    move/andb_and: b => []. eauto. intros.
    apply map_def_eq_spec; eauto.
    eapply b0; eauto. now apply up_ext_closed.
  - f_equal; eauto. red in X. solve_all.
    move/andb_and: b => []. eauto. intros.
    apply map_def_eq_spec; eauto.
    eapply b0; eauto. now apply up_ext_closed.
Qed.

Lemma subst_id s Γ t : 
  closedn #|s| t ->
  assumption_context Γ ->
  s = List.rev (to_extended_list Γ) ->
  subst s 0 t = t.
Proof.
  intros cl ass eq.
  autorewrite with sigma.
  rewrite -{2}(subst_ids t).
  eapply inst_ext_closed; eauto.
  intros.
  unfold ids, subst_consn. simpl.
  destruct (snd (nth_error_Some' s x) H). rewrite e.
  subst s.
  rewrite /to_extended_list /to_extended_list_k in e.
  rewrite List.rev_length in cl, H. autorewrite with len in *.
  rewrite reln_alt_eq in e.
  rewrite app_nil_r List.rev_involutive in e.
  clear -ass e. revert e.
  rewrite -{2}(Nat.add_0_r x).
  generalize 0.
  induction Γ in x, ass, x0 |- * => n. 
  - simpl in *. rewrite nth_error_nil => //.
  - depelim ass; simpl.
    destruct x; simpl in *; try congruence.
    move=> e; specialize (IHΓ ass); simpl in e.
    specialize (IHΓ _ _ _ e). subst x0. f_equal. lia.
Qed.

Lemma map_inst_idsn l l' n :
  #|l| = n ->
  map (inst (l ⋅n l')) (idsn n) = l.
Proof.
  induction n in l, l' |- *.
  - destruct l => //.
  - destruct l as [|l a] using rev_case => // /=.
    rewrite app_length /= Nat.add_1_r => [=].
    intros; subst n.
    simpl. rewrite map_app.
    f_equal; auto.
    + rewrite subst_consn_app.
      now apply IHn.
    + simpl.
      destruct (@subst_consn_lt _ (l ++ [a]) #|l|) as [a' [hnth heq]].
      * rewrite app_length. simpl; lia.
      * rewrite heq. rewrite nth_error_app_ge in hnth; auto.
        rewrite Nat.sub_diag in hnth. simpl in hnth. congruence.
Qed.


Lemma inst_decl_closed :
  forall σ k d,
    closed_decl k d ->
    inst_decl (⇑^k σ) d = d.
Proof.
  intros σ k d.
  case: d => na [body|] ty. all: rewrite /closed_decl /inst_decl /map_decl /=.
  - move /andb_and => [cb cty]. rewrite !inst_closed //.
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
  move /andb_and => [closedx Hctx].
  rewrite inst_decl_closed //.
  f_equal. now rewrite IHctx.
Qed.

Lemma inst_closedn_ctx f n Γ : 
  closedn_ctx n Γ -> 
  inst_context (⇑^n f) Γ = Γ.
Proof.
  unfold closedn_ctx, rename_context.
  apply alli_fold_context.
  intros. rewrite -Upn_Upn Nat.add_comm.
  now rewrite [map_decl _ _]inst_decl_closed.
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
  destruct h as [_ [hclΓ hcl]].
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
Admitted.
(*
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
    destruct hb as [indices s arity_eq onAr csorts onConstr onProj sorts].
    simpl in *.
    assert (e : ty.[⇑^0 σ] = ty).
    { destruct onAr as [s' h'].
      eapply typed_inst in h' as [_ ?]. all: eauto.
    }
    rewrite e in e2. rewrite e1 in e2.
    revert e2. intros [= <- <-].
    rewrite e. f_equal.
    + eapply All_map_id. eapply All2_All_left; tea.
      intros [[x p] n'] y [[?s Hty] [cs Hargs]].
      unfold on_pi2; cbn; f_equal; f_equal.
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
Qed.*)

Lemma inst_declared_inductive :
  forall Σ ind mdecl idecl σ,
    wf Σ ->
    declared_inductive Σ ind mdecl idecl ->
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


(* Lemma types_of_case_rename : *)
(*   forall Σ ind mdecl idecl npar args u p pty indctx pctx ps btys f, *)
(*     wf Σ -> *)
(*     declared_inductive Σ ind mdecl idecl -> *)
(*     types_of_case ind mdecl idecl (firstn npar args) u p pty = *)
(*     Some (indctx, pctx, ps, btys) -> *)
(*     types_of_case *)
(*       ind mdecl idecl *)
(*       (firstn npar (map (rename f) args)) u (rename f p) (rename f pty) *)
(*     = *)
(*     Some ( *)
(*         rename_context f indctx, *)
(*         rename_context f pctx, *)
(*         ps, *)
(*         map (on_snd (rename f)) btys *)
(*     ). *)
(* Proof. *)
(*   intros Σ ind mdecl idecl npar args u p pty indctx pctx ps btys f hΣ hdecl h. *)
(*   unfold types_of_case in *. *)
(*   case_eq (instantiate_params (subst_instance_context u (ind_params mdecl)) (firstn npar args) (subst_instance_constr u (ind_type idecl))) ; *)
(*     try solve [ intro bot ; rewrite bot in h ; discriminate h ]. *)
(*   intros ity eity. rewrite eity in h. *)
(*   pose proof (on_declared_inductive hΣ as hdecl) [onmind onind]. *)
(*   apply onParams in onmind as Hparams. *)
(*   assert (closedparams : closed_ctx (subst_instance_context u (ind_params mdecl))). *)
(*   { rewrite closedn_subst_instance_context. *)
(*     eapply PCUICWeakening.closed_wf_local. all: eauto. eauto. } *)
(*   epose proof (inst_declared_inductive _ mdecl ind idecl (ren f) hΣ) as hi. *)
(*   forward hi by assumption. rewrite <- hi. *)
(*   eapply instantiate_params_rename with (f := f) in eity ; auto. *)
(*   rewrite -> ind_type_map. *)
(*   rewrite firstn_map. *)
(*   lazymatch type of eity with *)
(*   | ?t = _ => *)
(*     lazymatch goal with *)
(*     | |- match ?t' with _ => _ end = _ => *)
(*       replace t' with t ; revgoals *)
(*     end *)
(*   end. *)
(*   { autorewrite with sigma. *)
(*     rewrite <- !rename_inst. *)
(*     now rewrite rename_subst_instance_constr. } *)
(*   rewrite eity. *)
(*   case_eq (destArity [] ity) ; *)
(*     try solve [ intro bot ; rewrite bot in h ; discriminate h ]. *)
(*   intros [args0 ?] ear. rewrite ear in h. *)
(*   eapply inst_destArity with (σ := ren f) in ear as ear'. *)
(*   simpl in ear'. *)
(*   lazymatch type of ear' with *)
(*   | ?t = _ => *)
(*     lazymatch goal with *)
(*     | |- match ?t' with _ => _ end = _ => *)
(*       replace t' with t ; revgoals *)
(*     end *)
(*   end. *)
(*   { autorewrite with sigma. reflexivity. } *)
(*   rewrite ear'. *)
(*   case_eq (destArity [] pty) ; *)
(*     try solve [ intro bot ; rewrite bot in h ; discriminate h ]. *)
(*   intros [args' s'] epty. rewrite epty in h. *)
(*   eapply inst_destArity with (σ := ren f) in epty as epty'. *)
(*   simpl in epty'. *)
(*   lazymatch type of epty' with *)
(*   | ?t = _ => *)
(*     lazymatch goal with *)
(*     | |- match ?t' with _ => _ end = _ => *)
(*       replace t' with t ; revgoals *)
(*     end *)
(*   end. *)
(*   { autorewrite with sigma. reflexivity. } *)
(*   rewrite epty'. *)
(*   case_eq (map_option_out (build_branches_type ind mdecl idecl (firstn npar args) u p)) ; *)
(*     try solve [ intro bot ; rewrite bot in h ; discriminate h ]. *)
(*   intros brtys ebrtys. rewrite ebrtys in h. *)
(*   inversion h. subst. clear h. *)
(*   eapply build_branches_type_rename with (f := f) in ebrtys as ebrtys'. *)
(*   2: assumption. *)
(*   lazymatch type of ebrtys' with *)
(*   | ?t = _ => *)
(*     lazymatch goal with *)
(*     | |- match ?t' with _ => _ end = _ => *)
(*       replace t' with t ; revgoals *)
(*     end *)
(*   end. *)
(*   { f_equal. f_equal. unfold map_one_inductive_body. destruct idecl. *)
(*     simpl. f_equal. *)
(*     - autorewrite with sigma. *)
(*       eapply inst_ext. intro j. *)
(*       unfold ren, shiftn. simpl. *)
(*       f_equal. f_equal. lia. *)
(*     - clear. induction ind_ctors. 1: reflexivity. *)
(*       simpl. unfold on_pi2. destruct a. simpl. *)
(*       destruct p. simpl. f_equal. 2: easy. *)
(*       f_equal. f_equal. *)
(*       autorewrite with sigma. *)
(*       eapply inst_ext. intro j. *)
(*       unfold ren, Upn, shiftn, subst_consn. *)
(*       rewrite arities_context_length. *)
(*       destruct (Nat.ltb_spec j #|ind_bodies mdecl|). *)
(*       + rewrite nth_error_idsn_Some. all: easy. *)
(*       + rewrite nth_error_idsn_None. 1: auto. *)
(*         unfold subst_compose, shiftk. simpl. *)
(*         rewrite idsn_length. reflexivity. *)
(*     - clear. induction ind_projs. 1: auto. *)
(*       simpl. destruct a. unfold on_snd. simpl. *)
(*       f_equal. 2: easy. *)
(*       f_equal. autorewrite with sigma. *)
(*       eapply inst_ext. intro j. *)
(*       unfold Upn, Up, ren, shiftn, subst_cons, subst_consn, subst_compose, *)
(*       shift, shiftk. *)
(*       destruct j. *)
(*       + simpl. reflexivity. *)
(*       + simpl. *)
(*         destruct (Nat.ltb_spec (S j) (S (context_assumptions (ind_params mdecl)))). *)
(*         * rewrite nth_error_idsn_Some. 1: lia. *)
(*           simpl. reflexivity. *)
(*         * rewrite nth_error_idsn_None. 1: lia. *)
(*           simpl. rewrite idsn_length. reflexivity. *)
(*   } *)
(*   rewrite ebrtys'. autorewrite with sigma. reflexivity. *)
(* Qed. *)


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
    unfold Up, subst_compose, subst_cons.
    destruct i.
    + reflexivity.
    + pose proof (shift_subst_instance_constr u (σ i) 0) as e.
      autorewrite with sigma in e. rewrite e. reflexivity.
  -  f_equal;auto.
Admitted.

Lemma map_vass_map_def_inst g l s :
  (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d)))
        (map (map_def (inst s) g) l)) =
  (mapi (fun i d => map_decl (inst (⇑^i s)) d)
        (mapi (fun i (d : def term) => vass (dname d) (lift0 i (dtype d))) l)).
Proof.
  rewrite mapi_mapi mapi_map. apply mapi_ext.
  intros. unfold map_decl, vass; simpl; f_equal.
  rewrite !lift0_inst.
  autorewrite with sigma.
  rewrite shiftn_consn_idsn. reflexivity.
Qed.

Lemma inst_fix_context:
  forall (mfix : list (def term)) s,
    fix_context (map (map_def (inst s) (inst (⇑^#|mfix| s))) mfix) =
    inst_context s (fix_context mfix).
Proof.
  intros mfix s. unfold fix_context.
  rewrite map_vass_map_def_inst rev_mapi.
  fold (fix_context mfix).
  rewrite (inst_context_alt s (fix_context mfix)).
   now rewrite mapi_length fix_context_length.
Qed.

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
      * simpl.
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
    wf_local Σ (Δ ,, vdef na t.[σ] A.[σ]) ->
    Σ ;;; Δ ⊢ σ : Γ ->
    Σ ;;; Δ ,, vdef na t.[σ] A.[σ] ⊢ ⇑ σ : Γ ,, vdef na t A.
Proof.
  intros Σ Γ Δ σ na t A wf h [|n] decl e.
  - simpl in *. inversion e. subst. clear e. simpl.
    rewrite lift_rename. rewrite rename_inst.
    autorewrite with sigma.
    split.
    + eapply meta_conv.
      * econstructor; auto; reflexivity.
      * rewrite lift0_inst /=.
        now autorewrite with sigma.
    + intros b [= ->].
      (* well-subst is ill-definied it should allow  let-preservation *)
      admit.

  - simpl in *.
    specialize (h _ _ e).
Admitted.

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

Lemma type_inst :
  forall Σ Γ Δ σ t A,
    wf Σ.1 ->
    wf_local Σ Δ ->
    Σ ;;; Δ ⊢ σ : Γ ->
    Σ ;;; Γ |- t : A ->
    Σ ;;; Δ |- t.[σ] : A.[σ].
Proof.
  intros Σ Γ Δ σ t A hΣ hΔ hσ h.
  revert Σ hΣ Γ t A h Δ σ hΔ hσ.
  apply (typing_ind_env (fun Σ Γ t T => forall Δ σ,
    wf_local Σ Δ ->
    Σ ;;; Δ ⊢ σ : Γ ->
    Σ ;;; Δ |- t.[σ] : T.[σ]
  ) (fun Σ Γ wfΓ => forall Δ σ, wf_local Σ Δ ->    Σ ;;; Δ ⊢ σ : Γ ->
      wf_local Σ Δ)).
  - intros Σ wfΣ Γ wfΓ. auto.
    
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
      * eapply well_subst_Up'; try assumption.
        constructor; auto.
        ** exists s1. apply ihB; auto.
        ** apply ihb; auto.  
  - intros Σ wfΣ Γ wfΓ t na A B s u X hty ihty ht iht hu ihu Δ σ hΔ hσ.
    autorewrite with sigma.
    econstructor.
    * specialize (ihty _ _ hΔ hσ).
      simpl in ihty. eapply meta_conv_term; [eapply ihty|].
      now rewrite up_Up.
    * specialize (iht _ _ hΔ hσ).
      simpl in iht. eapply meta_conv; [eapply iht|].
      now rewrite up_Up.
    * eapply ihu; auto.
  - intros Σ wfΣ Γ wfΓ cst u decl X X0 isdecl hconst Δ σ hΔ hσ.
    autorewrite with sigma. simpl.
    eapply meta_conv; [econstructor; eauto|].
    eapply declared_constant_closed_type in isdecl; eauto.
    rewrite inst_closed0; auto.
    now rewrite closedn_subst_instance_constr.
  - intros Σ wfΣ Γ wfΓ ind u mdecl idecl isdecl X X0 hconst Δ σ hΔ hσ.
    eapply meta_conv; [econstructor; eauto|].
    eapply declared_inductive_closed_type in isdecl; eauto.
    rewrite inst_closed0; auto.
    now rewrite closedn_subst_instance_constr.
  - intros Σ wfΣ Γ wfΓ ind i u mdecl idecl cdecl isdecl X X0 hconst Δ σ hΔ hσ.
    eapply meta_conv; [econstructor; eauto|].
    eapply declared_constructor_closed_type in isdecl; eauto.
    rewrite inst_closed0; eauto.
  - intros Σ wfΣ Γ wfΓ ind u npar p c brs args mdecl idecl isdecl X X0 a pars
           ps pty htoc X1 ihp H2 X3 notcoind ihc btys H3 ihbtys Δ σ hΔ hσ.
    autorewrite with sigma. simpl.
    rewrite map_app. simpl.
    rewrite map_skipn.
    (* eapply types_of_case_inst with (σ := σ) in htoc. all: try eassumption. *)
    eapply type_Case.
    + eassumption.
    + assumption.
    + admit.
    + simpl. eapply ihp. all: auto.
    + eassumption.
    + specialize (ihc _ _ hΔ hσ). autorewrite with sigma in ihc.
      eapply ihc.
    + admit.
    + admit.
    + admit. 
  - intros Σ wfΣ Γ wfΓ p c u mdecl idecl pdecl isdecl args X X0 hc ihc e ty
           Δ σ hΔ hσ.
    simpl.
    eapply meta_conv; [econstructor|].
    * eauto.
    * specialize (ihc _ _ hΔ hσ).
      rewrite inst_mkApps in ihc. eapply ihc.
    * now rewrite map_length.
    * autorewrite with sigma.
      eapply declared_projection_closed in isdecl; auto.
      admit.
  - intros Σ wfΣ Γ wfΓ mfix n decl types H0 H1 X ihmfix Δ σ hΔ hσ.
    autorewrite with sigma.
    admit.
  - intros Σ wfΣ Γ wfΓ mfix n decl types H0 X X0 ihmfix Δ σ hΔ hσ.
    autorewrite with sigma.
    admit.
  - intros Σ wfΣ Γ wfΓ t A B X hwf ht iht hB ihB hcu Δ σ hΔ hσ.
    eapply type_Cumul.
    + eapply iht. all: auto.
    + eapply ihB. all: auto.
    + admit.
Admitted.
