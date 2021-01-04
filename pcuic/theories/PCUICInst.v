(* Distributed under the terms of the MIT license. *)
From Coq Require Import Morphisms.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICClosed PCUICEquality PCUICWeakeningEnv
  PCUICSigmaCalculus PCUICRename PCUICWeakening.

Require Import ssreflect ssrbool.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Set Equations With UIP.
Set Keyed Unification.
Set Default Goal Selector "!".

Implicit Types cf : checker_flags.

(** * Type preservation for σ-calculus instantiation *)

Open Scope sigma_scope.

Definition inst_context σ (Γ : context) : context :=
  fold_context (fun i => inst (⇑^i σ)) Γ.

Instance inst_context_ext : Proper (`=1` ==> Logic.eq ==> Logic.eq) inst_context.
Proof.
  intros f g Hfg x y ->.
  apply fold_context_ext => i t.
  now rewrite Hfg.
Qed.

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

Lemma rename_decl_inst_decl : forall f d, rename_decl f d = inst_decl (ren f) d.
Proof.
  intros f d.
  unfold rename_decl, inst_decl.
  destruct d. unfold map_decl.
  autorewrite with sigma.
  f_equal.
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

Lemma typed_inst {cf} :
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

Lemma inst_wf_local {cf} :
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

Lemma Up_subst_instance_constr u σ :
  ⇑ (subst_instance_constr u ∘ σ) =1 subst_instance_constr u ∘ ⇑ σ.
Proof.
  intros i => /=.
  rewrite - !up_Up /up.
  nat_compare_specs => //.
  now rewrite rename_subst_instance_constr.
Qed.

Lemma upn_subst_instance_constr u n σ :
  up n (subst_instance_constr u ∘ σ) =1 subst_instance_constr u ∘ up n σ.
Proof.
  intros i => /=.
  rewrite /up.
  nat_compare_specs => //.
  now rewrite rename_subst_instance_constr.
Qed.

Lemma Upn_subst_instance_constr u n σ :
  ⇑^n (subst_instance_constr u ∘ σ) =1 subst_instance_constr u ∘ ⇑^n σ.
Proof.
  rewrite - !up_Upn. rewrite upn_subst_instance_constr.
  intros i. now rewrite up_Upn.
Qed.

Lemma inst_subst_instance_constr :
  forall u t σ,
    (subst_instance_constr u t).[subst_instance_constr u ∘ σ] =
    subst_instance_constr u t.[σ].
Proof.
  intros u t σ.
  induction t in σ |- * using term_forall_list_ind.
  all: try solve [
    simpl ;
    rewrite ?IHt ?IHt1 ?IHt2 ;
    easy
  ].
  all: simpl. all: auto.
  all: rewrite ?map_map_compose ?compose_on_snd ?compose_map_def ?map_length
    ?map_predicate_map_predicate ?map_branch_map_branch.
  all: try solve [ f_equal ; eauto ; solve_all ; eauto ].
  all: try now rewrite IHt1; sigma; rewrite-IHt2 -?IHt3 ?Up_subst_instance_constr.
  - f_equal; auto.
    * solve_all. 
      now rewrite upn_subst_instance_constr e.
    * solve_all. rewrite !map_branch_map_branch; solve_all.
      apply map_branch_eq_spec.
      now rewrite upn_subst_instance_constr H.
  - f_equal. solve_all.
    apply map_def_eq_spec; auto.
    now rewrite upn_subst_instance_constr.
  - f_equal; solve_all.
    apply map_def_eq_spec; auto.
    now rewrite upn_subst_instance_constr.
Qed.

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
        (∑ x' decl', σ x = tRel x' ×
          nth_error Δ x' = Some decl' ×
          (* Γ_x', x := b : ty -> Δ_x', x' := b.[↑^S x ∘s σ]. 
             Δ |- ↑^(S x) ∘s σ : Γ_x
            *)
          option_map (rename (rshiftk (S x'))) decl'.(decl_body) = Some (b.[↑^(S x) ∘s σ])) +
        (σ x = b.[↑^(S x) ∘s ⇑ σ])).

Notation "Σ ;;; Δ ⊢ σ : Γ" :=
  (well_subst Σ Γ σ Δ) (at level 50, Δ, σ, Γ at next level).
(* 
Lemma shift_Up_comm σ : ↑ ∘s ⇑ σ =1 ⇑ (⇑ σ).
Proof.
  intros i. unfold subst_compose. simpl.
  unfold subst_compose, Up. simpl.
  destruct i.
  sigma. *)
Lemma well_subst_Up {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ σ na A} :
  wf_local Σ (Δ ,, vass na A.[σ]) ->
  Σ ;;; Δ ⊢ σ : Γ ->
  Σ ;;; Δ ,, vass na A.[σ] ⊢ ⇑ σ : Γ ,, vass na A.
Proof.
  intros hΔ h [|n] decl e.
  - simpl in *. inversion e. subst. clear e. simpl.
    split.
    + eapply meta_conv.
      * econstructor ; auto.
        reflexivity.
      * simpl.
        now autorewrite with sigma.
    + intros b e. discriminate.
  - cbn -[rshiftk] in *.
    specialize (h _ _ e) as [h1 h2].
    split.
    + sigma. sigma in h1.
      eapply meta_conv.
      * epose proof (weakening_rename_typing (Γ' := []) (Γ'' := [_]) hΔ h1).
        simpl in X.
        sigma in X. eapply X.
      * eapply inst_ext. rewrite ren_lift_renaming.
        now sigma.
    + intros b hb.
      specialize (h2 _ hb) as [[x' [decl' [hrel [hnth hdecl]]]]|].
      * left. exists (S x'), decl'.
        split.
        ** unfold subst_compose at 1. now rewrite hrel.
        ** cbn -[rshiftk]. split; auto.
           destruct (decl_body decl') => //. cbn -[rshiftk] in hdecl |- *.
           noconf hdecl. f_equal.
           replace (S (S n)) with (S n + 1) by lia.
           rewrite -shiftk_compose subst_compose_assoc.
           rewrite -Upn_1_Up (shiftn_consn_idsn 1) -subst_compose_assoc -inst_assoc -H0.
           sigma. now rewrite ren_shift compose_ren.
      * right.
        unfold subst_compose at 1. rewrite e0.
        now rewrite inst_assoc.
Qed.

Lemma well_subst_Up' {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ σ na t A} :
  wf_local Σ (Δ ,, vdef na t.[σ] A.[σ]) ->
  Σ ;;; Δ ⊢ σ : Γ ->
  Σ ;;; Δ ,, vdef na t.[σ] A.[σ] ⊢ ⇑ σ : Γ ,, vdef na t A.
Proof.
  intros wf h [|n] decl e.
  - simpl in *. inversion e. subst. clear e. simpl.
    rewrite lift_rename. rewrite rename_inst.
    autorewrite with sigma.
    split.
    + eapply meta_conv.
      * econstructor; auto; reflexivity.
      * rewrite lift0_inst /=.
        now autorewrite with sigma.
    + intros b [= ->].
      left. exists 0. eexists _; intuition eauto.
      simpl. sigma. reflexivity.
  - cbn -[rshiftk] in *.
    specialize (h _ _ e) as [h1 h2].
    split.
    + sigma. sigma in h1.
      eapply meta_conv.
      * epose proof (weakening_rename_typing (Γ' := []) (Γ'' := [_]) wf h1).
        simpl in X.
        sigma in X. eapply X.
      * eapply inst_ext. rewrite ren_lift_renaming.
        now sigma.
    + intros b hb.
      specialize (h2 _ hb) as [[x' [decl' [hrel [hnth hdecl]]]]|].
      * left. exists (S x'), decl'.
        split.
        ** unfold subst_compose at 1. now rewrite hrel.
        ** cbn -[rshiftk]. split; auto.
          destruct (decl_body decl') => //. cbn -[rshiftk] in hdecl |- *.
          noconf hdecl. f_equal.
          replace (S (S n)) with (S n + 1) by lia.
          rewrite -shiftk_compose subst_compose_assoc.
          rewrite -Upn_1_Up (shiftn_consn_idsn 1) -subst_compose_assoc -inst_assoc -H0.
          sigma. now rewrite ren_shift compose_ren.
      * right.
        unfold subst_compose at 1. rewrite e0.
        now rewrite inst_assoc.
Qed.

Lemma well_subst_ext Σ Δ σ σ' Γ : 
  Σ ;;; Δ ⊢ σ : Γ ->
  σ =1 σ' ->
  Σ ;;; Δ ⊢ σ' : Γ.
Proof.
  intros Hσ eq n decl hnth.
  specialize (Hσ n decl hnth) as [hσ hb].
  split.
  - rewrite -(eq n).
    eapply meta_conv. 2:now rewrite -eq. assumption.
  - intros b hd. specialize (hb b hd).
    destruct hb as [[x' [decl' [eqn [hnth' hsome]]]]|h].
    * left; exists x', decl'. rewrite -(eq n). repeat split; auto.
      now rewrite -eq.
    * right. now rewrite -(eq n) -eq.
Qed.

Lemma well_subst_app {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ σ Δ'} :
  wf_local Σ (Δ ,,, inst_context σ Δ') ->
  Σ ;;; Δ ⊢ σ : Γ ->
  Σ ;;; Δ ,,, inst_context σ Δ' ⊢ ⇑^#|Δ'| σ : Γ ,,, Δ'.
Proof.
  induction Δ' as [|[na [b|] ty] Δ']; simpl => hwf hsub.
  - eapply well_subst_ext; eauto.
    now rewrite Upn_0.
  - rewrite inst_context_snoc.
    eapply well_subst_ext.
    2:now rewrite Upn_S. simpl.
    apply well_subst_Up'.
    * rewrite inst_context_snoc in hwf.
      apply hwf.
    * rewrite inst_context_snoc in hwf.
      depelim hwf. apply IHΔ' => //.
  - rewrite inst_context_snoc.
    eapply well_subst_ext.
    2:now rewrite Upn_S. simpl.
    apply well_subst_Up.
    * rewrite inst_context_snoc in hwf.
      apply hwf.
    * rewrite inst_context_snoc in hwf.
      depelim hwf. apply IHΔ' => //.
Qed.

Lemma well_subst_app_up {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ σ Δ'} :
  wf_local Σ (Δ ,,, inst_context σ Δ') ->
  Σ ;;; Δ ⊢ σ : Γ ->
  Σ ;;; Δ ,,, inst_context σ Δ' ⊢ up #|Δ'| σ : Γ ,,, Δ'.
Proof.
  intros wf Hσ.
  eapply well_subst_ext.
  2:now rewrite up_Upn.
  now apply well_subst_app.
Qed.

Notation inst_predicate f p :=
  (map_predicate id (inst f) (inst (up #|pcontext p| f)) p).

Lemma inst_predicate_preturn f p :
  inst (⇑^#|p.(pcontext)| f) (preturn p) =
  preturn (inst_predicate f p).
Proof. rewrite -up_Upn. reflexivity. Qed.

Lemma inst_mkLambda_or_LetIn f d t : 
  inst f (mkLambda_or_LetIn d t) =
  mkLambda_or_LetIn (inst_decl f d) (inst (⇑ f) t).
Proof.
  destruct d as [na [] ty]; rewrite /= /mkLambda_or_LetIn /=; f_equal; now rewrite up_Up.
Qed.

Lemma inst_it_mkLambda_or_LetIn f ctx t : 
  inst f (it_mkLambda_or_LetIn ctx t) =
  it_mkLambda_or_LetIn (inst_context f ctx) (inst (⇑^#|ctx| f) t).
Proof.
  move: t.
  induction ctx; simpl => t.
  - now rewrite Upn_0.
  - rewrite /= IHctx inst_context_snoc /snoc /=. f_equal.
    now rewrite inst_mkLambda_or_LetIn /=; sigma.
Qed.

Lemma inst_reln f ctx n acc :
  forallb (closedn (n + #|ctx|)) acc ->
  map (inst (⇑^(n + #|ctx|) f)) (reln acc n ctx) = 
  reln acc n ctx.
Proof.
  induction ctx in n, acc |- *; simpl; auto.
  - intros clacc. solve_all. 
    now rewrite inst_closed.
  - intros clacc.
    destruct a as [? [] ?].
    * rewrite Nat.add_succ_r.
      change (S (n + #|ctx|)) with (S n + #|ctx|).
      rewrite Nat.add_1_r IHctx // /= -Nat.add_succ_r //.
    * rewrite Nat.add_succ_r Nat.add_1_r. rewrite (IHctx (S n)) /= // -Nat.add_succ_r //.
      simpl. rewrite clacc andb_true_r.
      eapply Nat.ltb_lt. lia.
Qed.

Lemma inst_to_extended_list f ctx :
  map (inst (⇑^#|ctx| f)) (to_extended_list ctx) = to_extended_list ctx.
Proof.
  unfold to_extended_list, to_extended_list_k.
  now apply (inst_reln _ _ 0).
Qed.

Lemma inst_subst :
  forall f s n t,
    inst (⇑^n f) (subst s n t) =
    subst (map (inst f) s) n (inst (⇑^n (⇑^#|s| f)) t).
Proof.
  intros f s n t.
  autorewrite with sigma.
  eapply inst_ext. intro i. unfold Upn.
  unfold subst_consn, shiftk, subst_compose. simpl.
  destruct (Nat.ltb_spec i n).
  - rewrite idsn_lt //. simpl.
    rewrite idsn_lt //.
  - rewrite nth_error_idsn_None //. len.
    rewrite !inst_assoc. unfold subst_compose. simpl.
    destruct (Nat.ltb_spec (i - n) #|s|).
    * rewrite idsn_lt //. simpl.
      rewrite nth_error_idsn_None //; try lia.
      rewrite nth_error_map.
      replace (n + (i - n) - n) with (i - n) by lia.
      destruct nth_error eqn:hnth => /=.
      ** sigma. apply inst_ext.
        intros k. cbn.
        elim: (Nat.ltb_spec (n + k) n); try lia.
        intros. eapply nth_error_Some_length in hnth.
        rewrite nth_error_idsn_None //. unfold subst_compose.
        lia_f_equal.
      ** eapply nth_error_None in hnth. lia.
    * len.
      rewrite nth_error_idsn_None; try lia.
      rewrite inst_assoc. simpl.
      destruct nth_error eqn:hnth.
      ** eapply nth_error_Some_length in hnth. lia.
      ** simpl.
        eapply nth_error_None in hnth.
        rewrite nth_error_idsn_None; try lia.
        unfold subst_compose. simpl.
        assert (n + (i - n - #|s|) - n = (i - n - #|s|)) as -> by lia.
        apply inst_ext => k.
        rewrite nth_error_idsn_None //; try lia.
        destruct nth_error eqn:hnth'.
        + eapply nth_error_Some_length in hnth'. len in hnth'. lia.
        + simpl. lia_f_equal.
Qed.

Lemma inst_context_subst_k f s k Γ : 
  inst_context (up k f) (subst_context s k Γ) =
  subst_context (map (inst f) s) k (inst_context (⇑^(k + #|s|) f) Γ).
Proof.
  rewrite !inst_context_alt !subst_context_alt.
  rewrite !mapi_mapi. apply mapi_ext => i x.
  rewrite /subst_decl !compose_map_decl.
  apply map_decl_ext => t.
  len.
  generalize (Nat.pred #|Γ| - i).
  intros. rewrite up_Upn -Upn_Upn inst_subst.
  now sigma.
Qed.

Lemma inst_context_subst f s Γ : 
  inst_context f (subst_context s 0 Γ) =
  subst_context (map (inst f) s) 0 (inst_context (⇑^#|s| f) Γ).
Proof.
  now rewrite -inst_context_subst_k up_Upn Upn_0.
Qed.

Lemma inst_case_predicate_context {Σ} {wfΣ : wf Σ} {ind mdecl idecl f p} :
  declared_inductive Σ ind mdecl idecl ->
  wf_predicate mdecl idecl p ->
  inst_context f (case_predicate_context ind mdecl idecl p) =
  case_predicate_context ind mdecl idecl (inst_predicate f p).
Proof.
  intros decli wfp.
  unfold case_predicate_context. simpl.
  unfold id. unfold case_predicate_context_gen.
  rewrite /inst_context.
  rewrite -map2_set_binder_name_fold //.
  - len. len. 
    now rewrite -(wf_predicate_length_pcontext wfp).
  - f_equal. rewrite fold_context_snoc0 /= /snoc.
    f_equal.
    * rewrite /map_decl /=. f_equal.
      len. rewrite inst_mkApps /=. f_equal.
      rewrite !map_app !map_map_compose. f_equal.
      + solve_all.
        eapply All_refl => x.
        sigma. now rewrite shiftn_consn_idsn.
      + now rewrite inst_to_extended_list.
    * rewrite -/(inst_context f _).
      rewrite inst_context_subst.
      f_equal.
      rewrite inst_closedn_ctx //.
      pose proof (closedn_ctx_expand_lets (ind_params mdecl) (ind_indices idecl)
        (declared_inductive_closed_pars_indices _ decli)).
      rewrite (wf_predicate_length_pars wfp).
      rewrite (declared_minductive_ind_npars decli).
      now rewrite closedn_subst_instance_context.
Qed.

Lemma inst_wf_predicate mdecl idecl f p :
  wf_predicate mdecl idecl p ->
  wf_predicate mdecl idecl (inst_predicate f p).
Proof.
  intros []. split.
  - now len.
  - assumption.
Qed.

Lemma inst_wf_branch cdecl f br :
  wf_branch cdecl br ->
  wf_branch cdecl (map_branch (inst (up #|br.(bcontext)| f)) br).
Proof.
  unfold wf_branch, wf_branch_gen. now simpl.
Qed.

Lemma inst_wf_branches cdecl f brs :
  wf_branches cdecl brs ->
  wf_branches cdecl (map (fun br => map_branch (inst (up #|br.(bcontext)| f)) br) brs).
Proof.
  unfold wf_branches, wf_branches_gen.
  intros h. solve_all. eapply Forall2_map_right.
  solve_all.
Qed.
 
Lemma wf_local_app_inst (Σ : global_env_ext) {wfΣ : wf Σ} Γ Δ : 
  All_local_env (lift_typing (fun (Σ : global_env_ext) (Γ' : context) (t T : term) =>
    forall Δ σ,
    wf_local Σ Δ ->
    Σ ;;; Δ ⊢ σ : (Γ ,,, Γ') ->
    Σ ;;; Δ |- t.[σ] : T.[σ]) Σ) Δ ->
  forall Δ' σ,
  Σ ;;; Δ' ⊢ σ : Γ ->
  wf_local Σ Δ' ->
  wf_local Σ (Δ' ,,, inst_context σ Δ).
Proof.
  intros.
  induction X.
  - now simpl.
  - simpl. destruct t0 as [s Hs].
    rewrite inst_context_snoc /=. constructor; auto.
    red. simpl. exists s.
    eapply (Hs (Δ' ,,, inst_context σ Γ0) (⇑^#|Γ0| σ)) => //.
    eapply well_subst_app; auto.
  - simpl. destruct t0 as [s Hs]. simpl in t1.
    rewrite inst_context_snoc /=. constructor; auto.
    * simpl. exists s.
      eapply (Hs (Δ' ,,, inst_context σ Γ0) (⇑^#|Γ0| σ)) => //.
      eapply well_subst_app; auto.
    * simpl. apply t1 => //.
      eapply well_subst_app; eauto.
Qed.

Definition inst_constructor_body mdecl f c := 
  map_constructor_body #|mdecl.(ind_params)| #|mdecl.(ind_bodies)|
   (fun k => inst  (up k f)) c.

Lemma inst_closed_decl k f d : closed_decl k d -> map_decl (inst (up k f)) d = d.
Proof.
  rewrite /closed_decl /map_decl.  
  destruct d as [? [] ?] => /=.
  - move/andP=> [] clt clty.
    rewrite up_Upn !inst_closed //.
  - move=> clt. rewrite !up_Upn !inst_closed //.
Qed.

Lemma inst_closed_constructor_body mdecl cdecl f : 
  closed_constructor_body mdecl cdecl ->
  inst_constructor_body mdecl f cdecl = cdecl.
Proof.
  rewrite /closed_constructor_body /inst_constructor_body /map_constructor_body.
  move/andP=> [] /andP [] clctx clind clty.
  destruct cdecl; cbn -[fold_context] in *; f_equal.
  + move: clctx. unfold closed_ctx.
    apply alli_fold_context => i d cldecl.
    rewrite inst_closed_decl //.
    red; rewrite -cldecl; lia_f_equal.
  + solve_all. rewrite up_Upn inst_closed //.
    red. rewrite -H0. lia_f_equal.
  + now rewrite up_Upn inst_closed.
Qed.

Lemma inst_cstr_args mdecl f cdecl : 
  cstr_args (inst_constructor_body mdecl f cdecl) =
  inst_context (up (#|mdecl.(ind_params)| + #|ind_bodies mdecl|) f) (cstr_args cdecl).
Proof. 
  simpl. unfold inst_context.
  apply fold_context_ext => i t.
  now rewrite !up_Upn !Upn_Upn.
Qed.

Lemma inst_closedn_terms f n ts : 
  forallb (closedn n) ts -> map (inst (up n f)) ts = ts.
Proof.
  solve_all. 
  now rewrite up_Upn inst_closed.
Qed.

Lemma inst_closed_extended_subst f Γ : 
  closed_ctx Γ ->
  map (inst (up (context_assumptions Γ) f)) (extended_subst Γ 0) = extended_subst Γ 0. 
Proof.
  intros cl. apply inst_closedn_terms.
  now apply (closedn_extended_subst_gen Γ 0 0).
Qed.

Lemma inst_lift :
  forall f n k t,
    inst (⇑^(n + k) f) (lift n k t) = lift n k (inst (⇑^k f) t).
Proof.
  intros f n k t.
  rewrite !lift_rename.
  autorewrite with sigma.
  rewrite ren_lift_renaming.
  eapply inst_ext.
  rewrite -Upn_Upn Nat.add_comm Upn_Upn.
  rewrite !Upn_compose.
  apply Upn_ext. now rewrite shiftn_consn_idsn.
Qed.

Lemma inst_context_lift f n k Γ : 
  inst_context (up (n + k) f) (lift_context n k Γ) =
  lift_context n k (inst_context (up k f) Γ).
Proof.
  rewrite !inst_context_alt !lift_context_alt.
  rewrite !mapi_mapi. apply mapi_ext => i x.
  rewrite /lift_decl !compose_map_decl.
  apply map_decl_ext => t; len.
  generalize (Nat.pred #|Γ| - i).
  intros.
  rewrite !up_Upn -Upn_Upn.
  rewrite (Nat.add_comm n k) Nat.add_assoc Nat.add_comm.
  now rewrite inst_lift Upn_Upn.
Qed.

Lemma inst_inds f ind pu bodies : map (inst f) (inds ind pu bodies) = inds ind pu bodies.
Proof.
  unfold inds.
  induction #|bodies|; simpl; auto. f_equal.
  apply IHn.
Qed.

Lemma closed_ctx_args n bctx ctx : 
  #|bctx| = #|ctx| ->
  closedn_ctx n ctx ->
  closedn_ctx n (map2 set_binder_name bctx ctx).
Proof.
  induction ctx in bctx |- *; destruct bctx; simpl; auto.
  rewrite !closedn_ctx_cons => [=] hlen.
  move/andP=> [cla clctx].
  rewrite IHctx // /=.
  rewrite map2_length //.
  rewrite /closed_decl /= in clctx *. now rewrite hlen.
Qed.

Lemma inst_case_branch_context_gen ind mdecl f p bctx cdecl :
  closedn_ctx (#|ind_params mdecl| + #|ind_bodies mdecl|)
    (cstr_args cdecl) ->
  closed_ctx (ind_params mdecl) ->
  #|bctx| = #|cstr_args cdecl| ->
  #|pparams p| = context_assumptions (ind_params mdecl) ->
  inst_context f (case_branch_context ind mdecl p bctx cdecl) = 
  case_branch_context ind mdecl (inst_predicate f p) bctx 
    (inst_constructor_body mdecl f cdecl).
Proof.
  intros clargs clpars. unfold case_branch_context, case_branch_context_gen.
  rewrite inst_cstr_args.
  cbn -[fold_context].
  intros hlen hlen'.
  rewrite map2_set_binder_name_fold //.
  change (fold_context
  (fun i : nat => inst (up i (up (ind_npars mdecl + #|ind_bodies mdecl|) f)))) with
    (inst_context (up (ind_npars mdecl + #|ind_bodies mdecl|) f)).
  rewrite inst_context_subst. f_equal.
  unfold id.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  simpl. len.
  rewrite inst_context_subst; len.
  rewrite hlen'.
  rewrite -{1}(context_assumptions_subst_instance_context (puinst p)).
  rewrite -up_Upn.
  rewrite inst_closed_extended_subst.
  { now rewrite closedn_subst_instance_context. }
  f_equal.
  rewrite -Upn_Upn -up_Upn Nat.add_comm.
  rewrite inst_context_lift. f_equal.
  rewrite inst_context_subst_k inst_inds. len.
  f_equal.
  rewrite inst_closedn_ctx //.
  * rewrite closedn_subst_instance_context.
    now rewrite closed_ctx_args.
  * rewrite -/(inst_context (up (#|ind_params mdecl| + #|ind_bodies mdecl|) f)
      (map2 set_binder_name bctx (cstr_args cdecl))).
    rewrite up_Upn inst_closedn_ctx //.
    now rewrite closed_ctx_args.
Qed.

Lemma forallb_map_spec {A B : Type} {p : A -> bool}
      {l : list A} {f g : A -> B} :
  (forall x : A, p x -> f x = g x) -> 
  forallb p l ->
  map f l = map g l.
Proof.
  induction l; simpl; trivial.
  rewrite andb_and. intros Hx [px pl].
  f_equal. - now apply Hx. - now apply IHl.
Qed.

Lemma inst_case_branch_type {Σ} {wfΣ : wf Σ} f (ci : case_info) i mdecl idecl p br cdecl : 
  declared_constructor Σ (ci.(ci_ind), i) mdecl idecl cdecl ->
  wf_predicate mdecl idecl p ->
  wf_branch cdecl br ->
  let ptm := 
    it_mkLambda_or_LetIn (case_predicate_context ci mdecl idecl p) (preturn p) 
  in
  let p' := inst_predicate f p in
  let ptm' :=
    it_mkLambda_or_LetIn
      (case_predicate_context ci mdecl idecl p')
      (preturn p') in
  case_branch_type ci mdecl idecl
     (inst_predicate f p) 
     (map_branch (inst (up #|bcontext br| f)) br) 
     ptm' i (inst_constructor_body mdecl f cdecl) =
  map_pair (inst_context f) (inst (up #|bcontext br| f)) 
  (case_branch_type ci mdecl idecl p br ptm i cdecl).
Proof.
  intros decli wfp wfb ptm p' ptm'.
  rewrite /case_branch_type /case_branch_type_gen /map_pair /=.
  rewrite inst_case_branch_context_gen //.
  { epose proof (declared_constructor_closed_args decli). now rewrite Nat.add_comm. }
  { eapply (declared_inductive_closed_params decli). }
  { now apply wf_branch_length. }
  { rewrite -(declared_minductive_ind_npars decli).
    apply (wf_predicate_length_pars wfp). }
  f_equal.
  rewrite inst_mkApps map_app map_map_compose.
  rewrite (wf_branch_length wfb).
  f_equal.
  * rewrite /ptm' /ptm !lift_it_mkLambda_or_LetIn !inst_it_mkLambda_or_LetIn.
    rewrite !lift_rename. f_equal.
    ++ rewrite /p'.
      rewrite -(inst_case_predicate_context decli) //.
      epose proof (inst_context_lift f #|cstr_args cdecl| 0).
      rewrite Nat.add_0_r in H0.
      rewrite H0. len. now rewrite up_Upn Upn_0.
    ++ rewrite /p'. rewrite Nat.add_0_r. simpl.
      rewrite case_predicate_context_length //.
      { now apply inst_wf_predicate. }
      rewrite !case_predicate_context_length // Nat.add_0_r; len.
      rewrite case_predicate_context_length //.
      rewrite !up_Upn -Upn_Upn. rewrite - !lift_rename.
      now rewrite Nat.add_comm inst_lift.
  * rewrite /= inst_mkApps /=. f_equal.
    ++ rewrite !map_map_compose /id.
      generalize (declared_constructor_closed_indicess decli).
      apply forallb_map_spec => t clt.
      rewrite !up_Upn.
      rewrite /expand_lets /expand_lets_k.
      rewrite -inst_subst_instance_constr. len.
      rewrite inst_subst. f_equal.
      rewrite inst_subst. rewrite (wf_predicate_length_pars wfp).
      rewrite (declared_minductive_ind_npars decli).
      rewrite -{2}(context_assumptions_subst_instance_context (puinst p) (ind_params mdecl)).
      setoid_rewrite <- up_Upn at 1.
      rewrite inst_closed_extended_subst.
      { rewrite closedn_subst_instance_context.
        apply (declared_inductive_closed_params decli). }
      f_equal. len. rewrite - !Upn_Upn.
      rewrite (Nat.add_comm _ (context_assumptions _)) inst_lift.
      f_equal. rewrite Nat.add_comm inst_subst.
      rewrite inst_inds. f_equal.
      rewrite - Upn_Upn. len.
      rewrite inst_closed ?closedn_subst_instance_constr //.
      { rewrite Nat.add_comm.
        now rewrite (Nat.add_comm #|cstr_args cdecl|) Nat.add_assoc. }
      rewrite inst_closed. ?closedn_subst_instance_constr //.
        { rewrite Nat.add_comm.
          now rewrite (Nat.add_comm #|cstr_args cdecl|) Nat.add_assoc. }
        
    ++ unfold id. f_equal. f_equal.
       rewrite map_app map_map_compose.
       rewrite map_map_compose.
       setoid_rewrite inst_shiftn. len. f_equal.
       rewrite inst_to_extended_list.
       now rewrite /to_extended_list /to_extended_list_k reln_fold.
Qed.

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
    Σ ;;; Δ |- t.[σ] : T.[σ])
    (fun Σ Γ => 
    All_local_env
   (lift_typing (fun (Σ : global_env_ext) (Γ : context) (t T : term)
    =>
    forall Δ σ,
    wf_local Σ Δ ->
    Σ ;;; Δ ⊢ σ : Γ ->
    Σ ;;; Δ |- t.[σ] : T.[σ]) Σ) Γ)).
  - intros Σ wfΣ Γ wfΓ. auto.
    induction 1; constructor; firstorder auto.
    
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
  - intros Σ wfΣ Γ wfΓ ci p c brs indices ps mdecl idecl isdecl HΣ
      IHΔ ci_npar predctx wfp Hpret IHpret IHpredctx isallowed
      Hc IHc iscof ptm wfbrs Hbrs Δ f HΔ Hf.
    autorewrite with sigma. simpl.
    rewrite map_app. simpl.
    rewrite /ptm. rewrite inst_it_mkLambda_or_LetIn.
    relativize #|predctx|.
    * erewrite inst_predicate_preturn.
      rewrite /predctx.
      rewrite (inst_case_predicate_context isdecl wfp).
      eapply type_Case; eauto.
      + now eapply inst_wf_predicate.
      + apply All_local_env_app_inv in IHpredctx as [].
        eapply IHpret.
        ++ rewrite -inst_case_predicate_context //.
           eapply wf_local_app_inst; eauto. apply a0.
        ++ rewrite /predctx.
           rewrite -{1}(case_predicate_context_length (ci:=ci) wfp).
           rewrite -inst_case_predicate_context //.
           eapply well_subst_app_up => //.
           eapply wf_local_app_inst; eauto. apply a0.
      + simpl. unfold id.
        specialize (IHc _ _ HΔ Hf).
        now rewrite inst_mkApps map_app in IHc.
      + now eapply inst_wf_branches.
      + eapply Forall2_All2 in wfbrs.
        eapply All2i_All2_mix_left in Hbrs; eauto.
        eapply All2i_nth_hyp in Hbrs.
        eapply All2i_map_right, (All2i_impl Hbrs) => i cdecl br.
        set (brctxty := case_branch_type _ _ _ _ _ _ _ _).
        move=> [Hnth [wfbr [[Hbr Hbrctx] [IHbr [Hbty IHbty]]]]].
        rewrite -(inst_closed_constructor_body mdecl cdecl f).
        { eapply (declared_constructor_closed (c:=(ci.(ci_ind),i))); eauto.
          split; eauto. }
        rewrite inst_case_branch_type //.
        rewrite -/brctxty. intros brctx'.
        assert (wf_local Σ (Δ,,, brctx'.1)).
        { rewrite /brctx'. cbn.
          apply All_local_env_app_inv in Hbrctx as [].
          eapply wf_local_app_renaming; tea. apply a0. }
        repeat split.
        ++ eapply IHbr. 
          split => //.
          rewrite /brctx' /brctxty; cbn.
          rewrite (wf_branch_length wfbr).
          erewrite <- case_branch_type_length; eauto.
          eapply urenaming_ext.
          { now rewrite app_context_length -shiftnP_add. }
          { reflexivity. }
          eapply urenaming_context, Hf.
        ++ eapply IHbty. split=> //.
          rewrite /brctx'; cbn.
          rewrite (wf_branch_length wfbr).
          erewrite <- case_branch_type_length; eauto.
          eapply urenaming_ext.
          { now rewrite app_context_length -shiftnP_add. }
          { reflexivity. }
          eapply urenaming_context, Hf.
    * rewrite /predctx case_predicate_context_length //.

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
