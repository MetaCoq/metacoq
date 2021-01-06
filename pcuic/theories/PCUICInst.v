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

Lemma inst_subst0 a b τ : (subst0 a b).[τ] = (subst0 (map (inst τ) a) b.[⇑^#|a| τ]).
Proof.
  simpl. rewrite !subst_inst !Upn_0. sigma.
  apply inst_ext.
  rewrite Upn_comp. 2:now len.
  rewrite subst_consn_compose. now sigma.
Qed.
Hint Rewrite inst_subst0 : sigma.

Lemma subst10_inst a b τ : b {0 := a}.[τ] = (b.[⇑ τ] {0 := a.[τ]}).
Proof.
  unfold subst10. sigma. simpl. rewrite subst_consn_tip /= //.
Qed.
Hint Rewrite subst10_inst : sigma.

Lemma inst_closed0 σ t : closedn 0 t -> t.[σ] = t.
Proof. intros. rewrite -{2}[t](inst_closed σ 0) //. now sigma. Qed.

Lemma inst_ext_closed s s' k t : 
  (forall x, x < k -> s x = s' x) -> 
  closedn k t -> 
  inst s t = inst s' t.
Proof.
  clear.
  intros Hs clt. revert k t clt s s' Hs.
  apply: term_closedn_list_ind; simpl in |- *; intros; try easy ;
    try (try rewrite H; try rewrite H0 ; try rewrite H1 ; easy);
    try solve [f_equal; solve_all].
  - f_equal; eauto.
    eapply H0; eauto. intros. eapply up_ext_closed; eauto.
  - f_equal; eauto. now eapply H0, (up_ext_closed _ 1).
  - f_equal; eauto.
    now eapply H1, (up_ext_closed _ 1).
  - destruct X as [ppars pret].
    f_equal; eauto.
    * unfold test_predicate in *. simpl in *. solve_all.
      eapply pret; eauto. intros. eapply up_ext_closed; eauto.
    * eapply All_map_eq. solve_all.
      unfold map_branch. f_equal. now eapply H0, up_ext_closed.
  - f_equal; eauto. red in X. solve_all.
    apply map_def_eq_spec; eauto.
    eapply b; eauto. len. now apply up_ext_closed.
  - f_equal; eauto. red in X. solve_all.
    apply map_def_eq_spec; eauto.
    eapply b; eauto. len; now apply up_ext_closed.
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

Lemma Up_subst_instance u σ :
  ⇑ (subst_instance u ∘ σ) =1 subst_instance u ∘ ⇑ σ.
Proof.
  intros i => /=.
  rewrite - !up_Up /up.
  nat_compare_specs => //.
  now rewrite rename_subst_instance.
Qed.

Lemma upn_subst_instance u n σ :
  up n (subst_instance u ∘ σ) =1 subst_instance u ∘ up n σ.
Proof.
  intros i => /=.
  rewrite /up.
  nat_compare_specs => //.
  now rewrite rename_subst_instance.
Qed.

Lemma Upn_subst_instance u n σ :
  ⇑^n (subst_instance u ∘ σ) =1 subst_instance u ∘ ⇑^n σ.
Proof.
  rewrite - !up_Upn. rewrite upn_subst_instance.
  intros i. now rewrite up_Upn.
Qed.

Lemma inst_subst_instance :
  forall u t σ,
    (subst_instance u t).[subst_instance u ∘ σ] =
    subst_instance u t.[σ].
Proof.
  intros u t σ.
  rewrite /subst_instance /=.
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
  all: try now rewrite IHt1; sigma; rewrite-IHt2 -?IHt3 ?Up_subst_instance.
  - f_equal; auto.
    * solve_all. 
      now rewrite upn_subst_instance e.
    * solve_all. rewrite !map_branch_map_branch; solve_all.
      apply map_branch_eq_spec.
      now rewrite upn_subst_instance H.
  - f_equal. solve_all.
    apply map_def_eq_spec; auto.
    now rewrite upn_subst_instance.
  - f_equal; solve_all.
    apply map_def_eq_spec; auto.
    now rewrite upn_subst_instance.
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

Lemma inst_fix_context_up :
  forall (mfix : list (def term)) s,
    fix_context (map (map_def (inst s) (inst (up #|mfix| s))) mfix) =
    inst_context s (fix_context mfix).
Proof.
  intros mfix s. unfold fix_context.
  rewrite map_vass_map_def_inst rev_mapi.
  fold (fix_context mfix).
  rewrite (inst_context_alt s (fix_context mfix)).
   now rewrite mapi_length fix_context_length.
Qed.

Section Sigma.

Context `{cf: checker_flags}.

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
        (σ x = b.[↑^(S x) ∘s σ])).

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
           rewrite -Upn_1_Up (shiftn_consn_idsn 1) -subst_compose_assoc -inst_assoc -H.
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
          rewrite -Upn_1_Up (shiftn_consn_idsn 1) -subst_compose_assoc -inst_assoc -H.
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
    red. rewrite -H. lia_f_equal.
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
  rewrite -{1}(context_assumptions_subst_instance (puinst p)).
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
      rewrite Nat.add_0_r in H.
      rewrite H. len. now rewrite up_Upn Upn_0.
    ++ rewrite /p'. rewrite Nat.add_0_r. simpl.
      rewrite case_predicate_context_length //.
      { now apply inst_wf_predicate. }
      rewrite !case_predicate_context_length // Nat.add_0_r; len.
      rewrite case_predicate_context_length //.
      rewrite !up_Upn -Upn_Upn. rewrite - !lift_rename.
      now rewrite Nat.add_comm inst_lift.
  * rewrite /= inst_mkApps /=. f_equal.
    ++ rewrite !map_map_compose /id.
      generalize (declared_constructor_closed_indices decli).
      apply forallb_map_spec => t clt.
      rewrite !up_Upn.
      rewrite /expand_lets /expand_lets_k.
      rewrite -inst_subst_instance. len.
      rewrite inst_subst. f_equal.
      rewrite inst_subst. rewrite (wf_predicate_length_pars wfp).
      rewrite (declared_minductive_ind_npars decli).
      rewrite -{2}(context_assumptions_subst_instance (puinst p) (ind_params mdecl)).
      setoid_rewrite <- up_Upn at 1.
      rewrite inst_closed_extended_subst.
      { rewrite closedn_subst_instance_context.
        apply (declared_inductive_closed_params decli). }
      f_equal. len. rewrite - !Upn_Upn.
      rewrite (Nat.add_comm _ (context_assumptions _)) inst_lift.
      f_equal. rewrite Nat.add_comm inst_subst.
      rewrite inst_inds. f_equal.
      rewrite - Upn_Upn. len.
      rewrite inst_closed ?closedn_subst_instance //.
      { eapply closed_upwards; tea; lia. }
      etransitivity. 
      { eapply inst_ext. intros x.
        rewrite -(Upn_subst_instance _ _ _ _). reflexivity. }
      rewrite inst_closed ?closedn_subst_instance //.
      { eapply closed_upwards; tea; lia. }
    ++ unfold id. f_equal. f_equal.
       rewrite map_app map_map_compose.
       rewrite map_map_compose.
       setoid_rewrite up_Upn. len.
       f_equal. 
       { apply map_ext. intros. rewrite !lift0_inst; sigma.
         now rewrite shiftn_consn_idsn. }
       rewrite inst_to_extended_list.
       now rewrite /to_extended_list /to_extended_list_k reln_fold.
Qed.

Lemma subst_consn_lt' (l : list term) (i : nat) σ :
  i < #|l| ->
  (l ⋅n σ) i = subst_fn l i.
Proof.
  move/subst_consn_lt => [x [hnth] hl].
  rewrite hl. unfold subst_fn. now rewrite hnth.
Qed.

Axiom fix_guard_inst : forall Σ Γ Δ mfix σ,
  Σ ;;; Γ ⊢ σ : Δ ->
  let mfix' := map (map_def (inst σ) (inst (up (List.length mfix) σ))) mfix in
  fix_guard Σ Δ mfix ->
  fix_guard Σ Γ mfix'.

Axiom cofix_guard_inst : forall Σ Γ Δ mfix σ,
  Σ ;;; Γ ⊢ σ : Δ ->
  let mfix' := map (map_def (inst σ) (inst (up (List.length mfix) σ))) mfix in
  cofix_guard Σ Δ mfix ->
  cofix_guard Σ Γ mfix'.

Instance map_def_ext {A B} : Proper (`=1` ==> `=1` ==> `=1`) (@map_def A B).
Proof.
  intros f g Hfg f' g' Hfg' x.
  unfold map_def; destruct x; simpl.
  now rewrite Hfg Hfg'.
Qed.

Lemma inst_decompose_prod_assum f Γ t :
  decompose_prod_assum (inst_context f Γ) (inst (up #|Γ| f) t)
  = let '(Γ, t) := decompose_prod_assum Γ t in 
    let '(Γ', t') := decompose_prod_assum [] (inst (up #|Γ| f) t) in
    (Γ' ++ inst_context f Γ, t').
Proof.
  induction t in Γ |- *. all: simpl; try (rewrite ?app_nil_r; reflexivity).
  - simpl.
    now rewrite decompose_prod_assum_ctx.
  - specialize (IHt2 (Γ ,, vass na t1)).
    rewrite inst_context_snoc /= in IHt2.
    rewrite <-up_Upn in IHt2.
    simpl. now rewrite up_up IHt2.
  - specialize (IHt3 (Γ ,, vdef na t1 t2)).
    rewrite inst_context_snoc /= in IHt3.
    simpl. rewrite <- up_Upn in IHt3.
    simpl. now rewrite up_up IHt3.
Qed.

Lemma decompose_prod_assum_mkApps ctx ind u args :
  decompose_prod_assum ctx (mkApps (tInd ind u) args) = (ctx, mkApps (tInd ind u) args).
Proof.
  apply (decompose_prod_assum_it_mkProd ctx []).
  now rewrite is_ind_app_head_mkApps.
Qed.

Lemma inst_app_context f Γ Δ :
  inst_context f (Γ ,,, Δ) = 
  inst_context f Γ ,,, inst_context (up #|Γ| f) Δ.
Proof.
  rewrite /inst_context fold_context_app /app_context. f_equal.
  apply fold_context_ext. intros i x. now rewrite up_Upn Nat.add_comm Upn_Upn.
Qed.

Lemma inst_smash_context f Γ Δ :
  inst_context f (smash_context Γ Δ) = 
  smash_context (inst_context (up #|Δ| f) Γ) (inst_context f Δ).
Proof.
  rewrite up_Upn.
  induction Δ as [|[na [b|] ty] Δ] in Γ |- *; simpl; auto;
    rewrite ?Upn_0 // ?inst_context_snoc IHΔ /=; len.
  - f_equal. now rewrite inst_context_subst /= -Upn_Upn.
  - f_equal. rewrite inst_app_context /map_decl /= /app_context.
    f_equal.
    * now rewrite up_Upn -Upn_Upn.
    * rewrite /inst_context fold_context_tip /map_decl /=. do 2 f_equal.
      now rewrite Upn_0.
Qed.

Lemma nth_error_inst_context f Γ n : 
  nth_error (inst_context f Γ) n = 
  option_map (map_decl (inst (up (#|Γ| - S n) f))) (nth_error Γ n).
Proof.
  induction Γ in n |- *; intros.
  - simpl. unfold inst_context, fold_context; simpl; rewrite nth_error_nil. easy.
  - simpl. destruct n; rewrite inst_context_snoc.
    + simpl. rewrite up_Upn. lia_f_equal.
    + simpl. rewrite Nat.sub_succ -IHΓ; simpl in *; (lia || congruence).
Qed.

Lemma up_0 f : up 0 f =1 f.
Proof.
  rewrite /up /=; setoid_rewrite Nat.sub_0_r.
  intros i. now rewrite rename_ren_id.
Qed.

Lemma inst_check_one_fix f (mfix : mfixpoint term) d x : 
  check_one_fix d = Some x ->
  check_one_fix (map_def (inst f) (inst (up #|mfix| f)) d) = Some x.
Proof.
  destruct d; simpl.
  move: (inst_decompose_prod_assum f [] dtype).
  rewrite up_0. intros ->.
  destruct decompose_prod_assum.
  destruct decompose_prod_assum as [Γ' t'].
  rewrite smash_context_app (smash_context_acc (inst_context _ _)).
  rewrite -(inst_smash_context f []).
  destruct nth_error eqn:hnth => //.
  have hlen := nth_error_Some_length hnth. len in hlen.
  simpl in hlen.
  destruct (nth_error (List.rev (_ ++ inst_context _ _)) _) eqn:hnth'.
  2:{ eapply nth_error_None in hnth'. len in hnth'. simpl in hnth'. lia. }
  rewrite nth_error_rev_inv in hnth; len; auto.
  len in hnth. simpl in hnth.
  rewrite nth_error_rev_inv in hnth'; len; auto; try lia.
  len in hnth'. simpl in hnth'.
  rewrite nth_error_app_ge in hnth'; len; try lia. len in hnth'.
  simpl in hnth'.
  replace (context_assumptions Γ' + context_assumptions c - S rarg - context_assumptions Γ') with
    (context_assumptions c - S rarg) in hnth' by lia.
  rewrite /= nth_error_inst_context /= hnth /= in hnth'. noconf hnth'.
  simpl.
  destruct decompose_app eqn:da. len.
  destruct t0 => /= //.
  eapply decompose_app_inv in da. rewrite da.
  rewrite inst_mkApps. simpl. rewrite decompose_app_mkApps //.
Qed.

Lemma inst_check_one_cofix f (mfix : mfixpoint term) d x : 
  check_one_cofix d = Some x ->
  check_one_cofix (map_def (inst f) (inst (up #|mfix| f)) d) = Some x.
Proof.
  destruct d; simpl.
  move: (inst_decompose_prod_assum f [] dtype).
  rewrite up_0. intros ->.
  destruct decompose_prod_assum.
  destruct decompose_prod_assum eqn:dp.
  destruct decompose_app eqn:da.
  destruct (decompose_app t0) eqn:da'.
  destruct t1 => /= //.
  eapply decompose_app_inv in da. subst t.
  simp sigma in dp. rewrite decompose_prod_assum_mkApps /= in dp.
  noconf dp. rewrite decompose_app_mkApps // in da'. noconf da' => //.
Qed.

Lemma inst_wf_fixpoint Σ f mfix :
  wf_fixpoint Σ mfix ->
  wf_fixpoint Σ (map (map_def (inst f) (inst (up #|mfix| f))) mfix).
Proof.
  unfold wf_fixpoint.
  rewrite map_map_compose.
  destruct (map_option_out (map check_one_fix mfix)) as [[]|] eqn:hmap => //.
  eapply map_option_out_impl in hmap.
  2:{ intros x y. apply (inst_check_one_fix f mfix). }
  now rewrite hmap.
Qed.

Lemma inst_wf_cofixpoint Σ f mfix :
  wf_cofixpoint Σ mfix ->
  wf_cofixpoint Σ (map (map_def (inst f) (inst (up #|mfix| f))) mfix).
Proof.
  rewrite /wf_cofixpoint map_map_compose.
  destruct (map_option_out (map check_one_cofix mfix)) as [[]|] eqn:hmap => //.
  eapply map_option_out_impl in hmap.
  2:{ intros x y. apply (inst_check_one_cofix f mfix). }
  now rewrite hmap.
Qed.

Lemma inst_extended_subst f Γ : 
  map (inst (up (context_assumptions Γ) f)) (extended_subst Γ 0) = extended_subst (inst_context f Γ) 0. 
Proof.
  induction Γ as [|[na [b|] ty] Γ]; auto; rewrite inst_context_snoc /=; len.
  - rewrite !inst_subst0.
    rewrite IHΓ. len. f_equal. f_equal.
    rewrite up_Upn -Upn_Upn Nat.add_comm.
    now rewrite inst_lift.
  - f_equal; auto.
    rewrite !(lift_extended_subst _ 1).
    rewrite map_map_compose.
    setoid_rewrite up_Upn; setoid_rewrite lift0_inst; setoid_rewrite inst_assoc.
    setoid_rewrite (Upn_Upn 1); setoid_rewrite shiftn_consn_idsn;
    setoid_rewrite <- up_Upn; setoid_rewrite <-inst_assoc.
    setoid_rewrite <- lift0_inst.
    rewrite -map_map_compose. now f_equal.
Qed.

Notation inst_branch f br := (map_branch (inst (up #|br.(bcontext)| f)) br).

Lemma inst_iota_red :
  forall f pars args bctx br,
  #|skipn pars args| = context_assumptions bctx ->
  #|bcontext br| = #|bctx| ->
  inst f (iota_red pars args bctx br) =
  iota_red pars (map (inst f) args) (inst_context f bctx) (inst_branch f br).
Proof.
  intros f pars args bctx br hlen hlen'.
  unfold iota_red.
  rewrite inst_subst0 map_skipn. f_equal.
  rewrite /expand_lets /expand_lets_k.
  rewrite !inst_subst0. len.
  rewrite -up_Upn. rewrite hlen inst_extended_subst. f_equal.
  now rewrite up_Upn -Upn_Upn Nat.add_comm inst_lift up_Upn hlen'.
Qed.

Lemma inst_unfold_fix :
  forall mfix idx narg fn f,
    unfold_fix mfix idx = Some (narg, fn) ->
    unfold_fix (map (map_def (inst f) (inst (up #|mfix| f))) mfix) idx
    = Some (narg, inst f fn).
Proof.
  intros mfix idx narg fn f h.
  unfold unfold_fix in *. rewrite nth_error_map.
  case_eq (nth_error mfix idx).
  2: intro neq ; rewrite neq in h ; discriminate.
  intros d e. rewrite e in h.
  inversion h. clear h.
  simpl.
  f_equal. f_equal.
  rewrite inst_subst0. rewrite fix_subst_length.
  f_equal.
  * unfold fix_subst. rewrite map_length.
    generalize #|mfix| at 2 3. intro n.
    induction n.
    - reflexivity.
    - simpl. f_equal. rewrite IHn. reflexivity.
  * now rewrite up_Upn.
Qed.

Lemma inst_unfold_cofix :
  forall mfix idx narg fn f,
    unfold_cofix mfix idx = Some (narg, fn) ->
    unfold_cofix (map (map_def (inst f) (inst (up #|mfix| f))) mfix) idx
    = Some (narg, inst f fn).
Proof.
  intros mfix idx narg fn f h.
  unfold unfold_cofix in *. rewrite nth_error_map.
  case_eq (nth_error mfix idx).
  2: intro neq ; rewrite neq in h ; discriminate.
  intros d e. rewrite e in h.
  inversion h.
  simpl. f_equal. f_equal.
  rewrite inst_subst0. rewrite cofix_subst_length.
  rewrite up_Upn.
  f_equal.
  unfold cofix_subst. rewrite map_length.
  generalize #|mfix| at 2 3. intro n.
  induction n.
  - reflexivity.
  - simpl. rewrite up_Upn.
    f_equal. rewrite IHn. reflexivity.
Qed.

Definition rigid_head t :=
  match t with
  | tVar _
  | tSort _
  | tConst _ _
  | tInd _ _
  | tConstruct _ _ _ => true
  | _ => false
  end.

Lemma decompose_app_inst :
  forall f t u l,
    decompose_app t = (u, l) ->
    rigid_head u ->
    decompose_app (inst f t) = (inst f u, map (inst f) l).
Proof.
  assert (aux : forall f t u l acc,
    decompose_app_rec t acc = (u, l) ->
    rigid_head u ->
    decompose_app_rec (inst f t) (map (inst f) acc) =
    (inst f u, map (inst f) l)
  ).
  { intros f t u l acc h.
    induction t in acc, h |- *.
    all: simpl in *; try solve [ inversion h ; reflexivity ].
    * noconf h => /= //.
    * simpl. intros ru. simpl in h. specialize IHt1 with (1 := h).
      now apply IHt1.
  }
  intros f t u l.
  unfold decompose_app.
  eapply aux.
Qed.

Lemma isConstruct_app_inst :
  forall t f,
    isConstruct_app t ->
    isConstruct_app (inst f t).
Proof.
  intros t f h.
  unfold isConstruct_app in *.
  case_eq (decompose_app t). intros u l e.
  apply decompose_app_inst with (f := f) in e as e'.
  * destruct (decompose_app t); simpl in *. destruct t0 => /= //. noconf e.
    now rewrite e'.
  * rewrite e in h. simpl in h.
    destruct u => //.
Qed.

Lemma is_constructor_inst :
  forall n l f,
    is_constructor n l ->
    is_constructor n (map (inst f) l).
Proof.
  intros n l f h.
  unfold is_constructor in *.
  rewrite nth_error_map.
  destruct nth_error.
  - simpl. apply isConstruct_app_inst. assumption.
  - simpl. discriminate.
Qed.

Lemma inst_predicate_set_pparams f p params :
  inst_predicate f (set_pparams p params) = 
  set_pparams (inst_predicate f p) (map (inst f) params).
Proof. reflexivity. Qed.

Lemma inst_predicate_set_preturn f p pret :
  inst_predicate f (set_preturn p pret) = 
  set_preturn (inst_predicate f p) (inst (up #|pcontext p| f) pret).
Proof. reflexivity. Qed.

(* Untyped substitution for untyped reduction / cumulativity *)
Definition usubst (Γ : context) σ (Δ : context) :=
  forall x decl,
    nth_error Γ x = Some decl ->
    (forall b,
        decl.(decl_body) = Some b ->
        (∑ x' decl', σ x = tRel x' ×
          nth_error Δ x' = Some decl' ×
          (** This is let-preservation *)
          option_map (rename (rshiftk (S x'))) decl'.(decl_body) = Some (b.[↑^(S x) ∘s σ])) +
        (* This allows to expand a let-binding everywhere *)
        (σ x = b.[↑^(S x) ∘s σ])).

Definition well_subst_usubst Σ Γ σ Δ :
  Σ ;;; Δ ⊢ σ : Γ ->
  usubst Γ σ Δ.
Proof.
  intros hσ x decl hnth b hb.
  specialize (hσ x decl hnth) as [_ h].
  now apply h.
Qed.
Coercion well_subst_usubst : well_subst >-> usubst.

Lemma usubst_Up {Γ Δ σ na A} :
  usubst Γ σ Δ ->
  usubst (Γ ,, vass na A) (⇑ σ) (Δ ,, vass na A.[σ]).
Proof.
  intros h [|n] decl e.
  - simpl in *. inversion e. subst. clear e. simpl => //.
  - cbn -[rshiftk] in *.
    specialize (h _ _ e) as h1.
    intros b hb.
    specialize (h1 _ hb) as [[x' [decl' [hrel [hnth hdecl]]]]|].
    * left. exists (S x'), decl'.
      split.
      ** unfold subst_compose at 1. now rewrite hrel.
      ** cbn -[rshiftk]. split; auto.
         destruct (decl_body decl') => //. cbn -[rshiftk] in hdecl |- *.
         noconf hdecl. f_equal.
         replace (S (S n)) with (S n + 1) by lia.
         rewrite -shiftk_compose subst_compose_assoc.
         rewrite -Upn_1_Up (shiftn_consn_idsn 1) -subst_compose_assoc -inst_assoc -H.
         sigma. now rewrite ren_shift compose_ren.
    * right.
      unfold subst_compose at 1. rewrite e0.
      now rewrite inst_assoc.
Qed.

Lemma usubst_Up' {Γ Δ σ na t A} :
  usubst Γ σ Δ ->
  usubst (Γ ,, vdef na t A) (⇑ σ) (Δ ,, vdef na t.[σ] A.[σ]).
Proof.
  intros h [|n] decl e.
  - simpl in *. inversion e. subst. clear e. simpl.
    intros b [= ->].
    left. exists 0. eexists _; intuition eauto.
    simpl. sigma. reflexivity.
  - cbn -[rshiftk] in *.
    specialize (h _ _ e) as h2.
    intros b hb.
    specialize (h2 _ hb) as [[x' [decl' [hrel [hnth hdecl]]]]|].
    * left. exists (S x'), decl'.
      split.
      ** unfold subst_compose at 1. now rewrite hrel.
      ** cbn -[rshiftk]. split; auto.
        destruct (decl_body decl') => //. cbn -[rshiftk] in hdecl |- *.
        noconf hdecl. f_equal.
        replace (S (S n)) with (S n + 1) by lia.
        rewrite -shiftk_compose subst_compose_assoc.
        rewrite -Upn_1_Up (shiftn_consn_idsn 1) -subst_compose_assoc -inst_assoc -H.
        sigma. now rewrite ren_shift compose_ren.
    * right.
      unfold subst_compose at 1. rewrite e0.
      now rewrite inst_assoc.
Qed.

Lemma usubst_ext {Δ σ σ' Γ} : 
  usubst Γ σ Δ ->
  σ =1 σ' ->
  usubst Γ σ' Δ.
Proof.
  intros Hσ eq n decl hnth.
  specialize (Hσ n decl hnth) as hb.
  intros b hd. specialize (hb b hd).
  destruct hb as [[x' [decl' [eqn [hnth' hsome]]]]|h].
  * left; exists x', decl'. rewrite -(eq n). repeat split; auto.
    now rewrite -eq.
  * right. now rewrite -(eq n) -eq.
Qed.

Lemma usubst_up_vass {Γ Δ σ na A} :
  usubst Γ σ Δ ->
  usubst (Γ ,, vass na A) (up 1 σ) (Δ ,, vass na A.[σ]).
Proof.
  intros H. 
  eapply usubst_ext; [eapply usubst_Up; tea|].
  now rewrite up_Upn; sigma.
Qed.

Lemma usubst_up_vdef {Γ Δ σ na t A} :
  usubst Γ σ Δ ->
  usubst (Γ ,, vdef na t A) (up 1 σ) (Δ ,, vdef na t.[σ] A.[σ]).
Proof.
  intros H. 
  eapply usubst_ext; [eapply usubst_Up'; tea|].
  now rewrite up_Upn; sigma.
Qed.

Lemma usubst_app {Γ Δ σ Δ'} :
  usubst Γ σ Δ ->
  usubst (Γ ,,, Δ') (⇑^#|Δ'| σ) (Δ ,,, inst_context σ Δ').
Proof.
  intros hs.
  induction Δ' as [|[na [b|] ty] Δ']; simpl.
  - eapply usubst_ext; eauto.
    now rewrite Upn_0.
  - rewrite inst_context_snoc.
    eapply usubst_ext.
    2:now rewrite Upn_S. simpl.
    now apply usubst_Up'.
  - rewrite inst_context_snoc.
    eapply usubst_ext.
    2:now rewrite Upn_S. simpl.
    now apply usubst_Up.
Qed.

Lemma usubst_app_up {Γ Δ σ Δ'} :
  usubst Γ σ Δ ->
  usubst (Γ ,,, Δ') (up #|Δ'| σ) (Δ ,,, inst_context σ Δ').
Proof.
  intros hs.
  eapply usubst_ext; [eapply usubst_app; eauto|].
  now sigma.
Qed.

Lemma All3_map_all {A B C} {A' B' C'} P (l : list A') (l' : list B') (l'' : list C')
  (f : A' -> A) (g : B' -> B) (h : C' -> C) : 
  All3 (fun x y z => P (f x) (g y) (h z)) l l' l'' ->  
  All3 P (map f l) (map g l') (map h l'').
Proof.
  induction 1; simpl; constructor; auto.
Qed.

Lemma OnOne2All_All3 {A B} P Q (l : list A) (l' : list B) (l'' : list B) :
  (forall x y z, P x y z -> Q x y z) ->
  (forall x y, Q x y y) ->
  OnOne2All P l l' l'' ->
  All3 Q l l' l''.
Proof.
  intros H1 H2.
  induction 1; simpl; constructor; auto.
  induction tl in bs, e |- *; destruct bs => //; try constructor; auto.
Qed.

Lemma red1_inst {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ u v σ} :
  usubst Γ σ Δ ->
  red1 Σ Γ u v ->
  red Σ Δ u.[σ] v.[σ].
Proof.
  intros hσ h.
  induction h using red1_ind_all in σ, Δ, hσ |- *.
  all: try solve [
    try (cbn in hav; rtoProp);
    simpl ; constructor ; eapply IHh ;
    eassumption
  ].
  - rewrite subst10_inst. sigma. do 2 constructor.
  - rewrite subst10_inst. sigma. do 2 constructor.
  - destruct (nth_error Γ i) eqn:hnth; noconf H.
    red in hσ. specialize hσ with (1 := hnth) as IH.
    specialize IH with (1:=H) as [[x' [decl' [hi [hnth' eqbod]]]]|eqr].
    * rewrite /= hi. sigma.
      destruct (decl_body decl') eqn:hdecl => //. noconf eqbod.
      rewrite -H0. sigma.
      relativize (t.[_]); [do 2 econstructor|].
      { now rewrite hnth' /= hdecl. }
      rewrite lift0_inst. now sigma.
    * rewrite /= eqr. sigma. reflexivity.
  - rename H0 into wfp. rename H1 into wfb. rename H2 into lenbrctx. simpl.
    rewrite inst_iota_red //.
    { rewrite /brctx. rewrite case_branch_context_length //. }
    subst brctx.
    rewrite inst_case_branch_context_gen.
    * rewrite Nat.add_comm. eapply (declared_constructor_closed_args isdecl).
    * eapply declared_inductive_closed_params; eauto with pcuic.
      eapply isdecl.
    * now rewrite (wf_branch_length wfb).
    * rewrite -(declared_minductive_ind_npars isdecl).
      now eapply wf_predicate_length_pars.
    * change (bcontext br) with (bcontext (inst_branch σ br)).
      epose proof (declared_constructor_closed _ isdecl).
      rewrite inst_closed_constructor_body //.
      rewrite inst_mkApps.
      do 2 econstructor; eauto.
      { now rewrite nth_error_map H /=. }
      { now apply inst_wf_predicate. }
      simpl. 
      rewrite (case_branch_context_assumptions wfb) in lenbrctx.
      rewrite case_branch_context_assumptions // -lenbrctx.
      now rewrite !List.skipn_length map_length.

  - rewrite 2!inst_mkApps. simpl.
    do 2 econstructor.
    + eapply inst_unfold_fix. eassumption.
    + eapply is_constructor_inst. assumption.
  - simpl. rewrite !inst_mkApps. simpl.
    constructor. eapply red_cofix_case.
    eapply inst_unfold_cofix. eassumption.
  - simpl. rewrite 2!inst_mkApps. simpl.
    constructor; eapply red_cofix_proj.
    eapply inst_unfold_cofix. eassumption.
  - simpl.
    rewrite inst_closed0.
    * rewrite closedn_subst_instance.
      eapply declared_constant_closed_body. all: eauto.
    * do 2 econstructor; eauto.
  - simpl. rewrite inst_mkApps. simpl.
    do 2 econstructor. rewrite nth_error_map. rewrite H. reflexivity.
  - simpl. eapply red_abs; eauto.
  - simpl; eapply red_abs; eauto.
    eapply IHh. now eapply usubst_up_vass.
  - simpl; eapply red_letin; eauto.
  - simpl; eapply red_letin; eauto.
  - simpl; pcuicfo. eapply red_letin; eauto.
    now eapply IHh, usubst_up_vdef.
  - simpl. rewrite inst_predicate_set_pparams.
    eapply red_case_pars.
    simpl. eapply All2_map.
    eapply OnOne2_All2; eauto; solve_all.
  - simpl. rewrite inst_predicate_set_preturn.
    eapply red_case_p; eauto.
    + now apply inst_wf_predicate.
    + simpl.
      erewrite <-(case_predicate_context_length (p:=inst_predicate σ p)); eauto.
      2:{ now eapply inst_wf_predicate. }
      eapply IHh; eauto.
      * rewrite <- !inst_case_predicate_context; eauto.
        rewrite inst_context_length.
        rewrite {2}(case_predicate_context_length H).
        rewrite <- inst_case_predicate_context => //.
        now eapply usubst_app_up.
  - simpl. eapply red_case_c; eauto.
  - simpl. eapply red_case_brs; eauto.
    + now eapply inst_wf_predicate.
    + now eapply inst_wf_branches.
    + red.
      replace (ind_ctors idecl) with (map (inst_constructor_body mdecl σ) (ind_ctors idecl)).
      2:{ pose proof (declared_inductive_closed_constructors isdecl).
          solve_all. now rewrite inst_closed_constructor_body. }
      eapply All3_map_all.
      red in H0.
      eapply Forall2_All2 in H0.
      eapply OnOne2All_All2_mix_left in X; eauto. clear H0.
      eapply OnOne2All_nth_error_impl in X.
      eapply OnOne2All_All3; eauto. solve_all.
      rewrite - inst_case_branch_context_gen; eauto.
      * destruct a as [ni hni].
        assert (declared_constructor Σ (ci.(ci_ind), ni) mdecl idecl x) by split => //.
        rewrite Nat.add_comm.
        eapply (declared_constructor_closed_args H0).
      * eapply (declared_inductive_closed_params isdecl).
      * now apply wf_branch_length.
      * rewrite -(declared_minductive_ind_npars isdecl).
        now apply (wf_predicate_length_pars H).
      * cbn. rewrite -b. erewrite <-! (case_branch_context_length b0).
        eapply b1.
        now eapply usubst_app_up.
  - simpl. now eapply red_proj_c.
  - simpl. now eapply red_app.
  - simpl. now eapply red_app_r.
  - simpl. now eapply red_prod.
  - simpl. now eapply red_prod_r, IHh, usubst_up_vass.
  - simpl. eapply red_evar.
    eapply All2_map. eapply OnOne2_All2; eauto; solve_all. 
  - simpl.
    eapply red_fix_one_ty.
    rewrite (OnOne2_length X).
    eapply OnOne2_map; solve_all. red. simpl.
    noconf b. rewrite H H0 H1. split; auto.
  - simpl.
    eapply red_fix_one_body.
    rewrite -(OnOne2_length X).
    eapply OnOne2_map; solve_all. red. simpl.
    noconf b. rewrite H H0 H1. split; auto.
    eapply b0.
    eapply usubst_ext. 
    * rewrite inst_fix_context_up. now eapply usubst_app_up.
    * now len.
  - simpl.
    eapply red_cofix_one_ty.
    rewrite (OnOne2_length X).
    eapply OnOne2_map; solve_all. red. simpl.
    noconf b. rewrite H H0 H1. split; auto.
  - simpl.
    eapply red_cofix_one_body.
    rewrite -(OnOne2_length X).
    eapply OnOne2_map; solve_all. red. simpl.
    noconf b. rewrite H H0 H1. split; auto.
    eapply b0.
    eapply usubst_ext. 
    * rewrite inst_fix_context_up. now eapply usubst_app_up.
    * now len.
Qed.

Lemma eq_term_upto_univ_inst Σ :
  forall Re Rle napp u v σ,
    Reflexive Re -> Reflexive Rle ->
    eq_term_upto_univ_napp Σ Re Rle napp u v ->
    eq_term_upto_univ_napp Σ Re Rle napp u.[σ] v.[σ].
Proof.
  intros Re Rle napp u v σ hRe hRle h.
  induction u in v, napp, Re, Rle, hRe, hRle, σ, h |- * using term_forall_list_ind.
  all: dependent destruction h.
  all: try solve [
    simpl ; constructor ; eauto
  ].
  - simpl. reflexivity.
  - simpl. constructor.
    induction X in a, args' |- *.
    + inversion a. constructor.
    + inversion a. subst. simpl. constructor.
      all: eauto.
  - simpl. constructor. all: eauto.
    * rewrite /rename_predicate.
      destruct X; destruct e as [? [? [ectx ?]]].
      rewrite (All2_length ectx). red.
      intuition auto; simpl; solve_all.
    * induction X0 in a, brs' |- *.
      + inversion a. constructor.
      + inversion a. subst. simpl.
        destruct X1 as [a0 e0]. rewrite (All2_length a0).
        constructor.
        ** unfold map_branch; simpl; intuition eauto.
        ** eauto.
  - simpl. constructor.
    apply All2_length in a as e. rewrite <- e.
    generalize #|m|. intro k.
    eapply All2_map. simpl. solve_all.
  - simpl. constructor.
    apply All2_length in a as e. rewrite <- e.
    generalize #|m|. intro k.
    eapply All2_map. simpl. solve_all.
Qed.

Lemma inst_cumul {Σ : global_env_ext} {wfΣ : wf Σ} Γ Δ σ A B :
  usubst Γ σ Δ ->
  Σ ;;; Γ |- A <= B ->
  Σ ;;; Δ |- A.[σ] <= B.[σ].
Proof.
  intros hσ h.
  induction h.
  - eapply cumul_refl.
    eapply eq_term_upto_univ_inst. all:try typeclasses eauto. assumption.
  - eapply red_cumul_cumul.
    + eapply red1_inst; tea.
    + apply IHh.
  - eapply red_cumul_cumul_inv.
    + eapply red1_inst; tea.
    + eapply IHh; eauto.
Qed.

Lemma type_inst : env_prop
  (fun Σ Γ t A =>
    forall Δ σ,
    wf_local Σ Δ ->
    Σ ;;; Δ ⊢ σ : Γ ->
    Σ ;;; Δ |- t.[σ] : A.[σ])
  (fun Σ Γ => 
    All_local_env
    (lift_typing (fun (Σ : global_env_ext) (Γ : context) (t T : term)
    =>
    forall Δ σ,
    wf_local Σ Δ ->
    Σ ;;; Δ ⊢ σ : Γ ->
    Σ ;;; Δ |- t.[σ] : T.[σ]) Σ) Γ).
Proof.
  apply typing_ind_env.
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
    now rewrite closedn_subst_instance.
  - intros Σ wfΣ Γ wfΓ ind u mdecl idecl isdecl X X0 hconst Δ σ hΔ hσ.
    eapply meta_conv; [econstructor; eauto|].
    eapply declared_inductive_closed_type in isdecl; eauto.
    rewrite inst_closed0; auto.
    now rewrite closedn_subst_instance.
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
          eapply wf_local_app_inst; tea. apply a0. }
        repeat split.
        ++ eapply IHbr => //. 
          rewrite /brctx' /brctxty; cbn.
          rewrite (wf_branch_length wfbr).
          erewrite <- case_branch_type_length; eauto.
          eapply well_subst_app_up => //.
        ++ eapply IHbty=> //.
          rewrite /brctx'; cbn.
          rewrite (wf_branch_length wfbr).
          erewrite <- case_branch_type_length; eauto.
          eapply well_subst_app_up => //.
    * rewrite /predctx case_predicate_context_length //.
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
      move: isdecl.
      rewrite -(closedn_subst_instance _ _ u).
      rewrite /ty.
      eapply inst_ext_closed.
      intros x Hx.
      rewrite subst_consn_lt'. all:repeat len; try lia.
      rewrite Upn_comp. 2:now repeat len.
      rewrite subst_consn_lt'. all:repeat len; try lia.
      now rewrite map_rev.
  - intros Σ wfΣ Γ wfΓ mfix n decl types hguard hnth htypes hmfix ihmfix wffix Δ σ hΔ hσ.
    simpl. eapply meta_conv; [econstructor;eauto|].
    * now eapply fix_guard_inst.
    * now rewrite nth_error_map hnth.
    * solve_all.
      destruct a as [s [Hs IH]].
      exists s; eapply IH; eauto.
    * solve_all.
      len. rewrite /types in b0. len in b0.
      pose proof (inst_fix_context mfix σ).
      setoid_rewrite <-up_Upn at 1 in H. rewrite H.
      eapply All_local_env_app_inv in htypes as [].
      eapply meta_conv; [eapply b0; eauto|].
      + eapply wf_local_app_inst; eauto. eapply a2.
      + rewrite -(fix_context_length mfix).
        eapply well_subst_app_up => //.
        eapply wf_local_app_inst; eauto. apply a2.
      + rewrite lift0_inst. sigma.
        now rewrite shiftn_consn_idsn.
    * now apply inst_wf_fixpoint.
    * reflexivity.

  - intros Σ wfΣ Γ wfΓ mfix n decl types hguard hnth htypes hmfix ihmfix wffix Δ σ hΔ hσ.
    simpl. eapply meta_conv; [econstructor;eauto|].
    * now eapply cofix_guard_inst.
    * now rewrite nth_error_map hnth.
    * solve_all.
      destruct a as [s [Hs IH]].
      exists s; eapply IH; eauto.
    * solve_all.
      len. rewrite /types in b0. len in b0.
      pose proof (inst_fix_context mfix σ).
      setoid_rewrite <-up_Upn at 1 in H. rewrite H.
      eapply All_local_env_app_inv in htypes as [].
      eapply meta_conv; [eapply b0; eauto|].
      + eapply wf_local_app_inst; eauto. eapply a2.
      + rewrite -(fix_context_length mfix).
        eapply well_subst_app_up => //.
        eapply wf_local_app_inst; eauto. apply a2.
      + rewrite lift0_inst. sigma.
        now rewrite shiftn_consn_idsn.
    * now apply inst_wf_cofixpoint.
    * reflexivity.

  - intros Σ wfΣ Γ wfΓ t A B X hwf ht iht hB ihB hcum Δ σ hΔ hσ.
    eapply type_Cumul.
    + eapply iht. all: auto.
    + eapply ihB. all: auto.
    + eapply inst_cumul => //. 
      * exact hσ.
      * apply hcum.
Qed.