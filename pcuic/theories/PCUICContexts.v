(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From Coq Require Import CRelationClasses ProofIrrelevance.
From MetaCoq.Template Require Import config Universes utils BasicAst
     AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping
     PCUICCumulativity PCUICPosition PCUICEquality PCUICNameless
     PCUICInversion PCUICCumulativity PCUICReduction
     PCUICConfluence PCUICConversion PCUICContextConversion
     PCUICParallelReductionConfluence PCUICWeakeningEnv
     PCUICClosed PCUICSubstitution PCUICUnivSubstitution PCUICSigmaCalculus
     PCUICWeakening PCUICGeneration PCUICUtils PCUICCtxShape.

From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Require Import Equations.Type.Relation_Properties.
Require Import ssreflect ssrbool.


Derive Signature for context_subst.

Hint Rewrite Nat.add_0_r : len.

Lemma smash_context_subst_empty s n Γ : 
  smash_context [] (subst_context s n Γ) =
  subst_context s n (smash_context [] Γ).
Proof. apply: (smash_context_subst []). Qed.

Lemma conv_context_smash {cf:checker_flags} Σ Γ Δ Δ' : 
  assumption_context Δ ->
  context_relation (fun Δ Δ' => conv_decls Σ (Γ ,,, Δ) (Γ ,,, Δ')) Δ Δ' ->
  assumption_context Δ'.
Proof.
  intros Hass Hconv.
  induction Hass in Δ', Hconv |- *. depelim Hconv. constructor.
  depelim Hconv; constructor; auto.
Qed.

Lemma smash_context_assumption_context {Γ Δ} : 
  assumption_context Γ ->
  assumption_context (smash_context Γ Δ).
Proof.
  induction Δ in Γ |- *; simpl; auto.
  destruct a as [? [b|] ty]; auto.
  intros.
  eapply IHΔ. clear -H.
  induction H; simpl; auto. constructor.
  rewrite subst_context_snoc. constructor; auto.
  intros.
  eapply IHΔ.
  clear -H. induction H; simpl; auto. constructor. constructor.
  constructor. auto.
Qed.
Hint Resolve smash_context_assumption_context : pcuic.

Lemma assumption_context_length ctx : assumption_context ctx ->
  context_assumptions ctx = #|ctx|.
Proof. induction 1; simpl; auto. Qed.
Hint Resolve assumption_context_length : pcuic.


Lemma map_subst_instance_constr_to_extended_list_k u ctx k :
  map (subst_instance_constr u) (to_extended_list_k ctx k)
  = to_extended_list_k ctx k.
Proof.
  pose proof (to_extended_list_k_spec ctx k).
  solve_all.
  now destruct H as [n [-> _]].
Qed.

Lemma subst_instance_to_extended_list_k u l k
  : map (subst_instance_constr u) (to_extended_list_k l k)
    = to_extended_list_k (subst_instance_context u l) k.
Proof.
  unfold to_extended_list_k.
  change [] with (map (subst_instance_constr u) []) at 2.
  generalize (@nil term). induction l as [|[aa [ab|] ac] bb] in k |- *.
  + reflexivity.
  + intros l; cbn. now rewrite IHbb.
  + intros l; cbn. now rewrite IHbb.
Qed.

Lemma context_subst_lift Γ p s n : 
  context_subst Γ p s -> 
  context_subst (lift_context n 0 Γ) (map (lift0 n) p) (map (lift0 n) s).
Proof.
  induction 1 in |- *; try constructor.
  rewrite lift_context_snoc map_app /=; constructor; auto.
  rewrite lift_context_snoc /= /lift_decl /map_decl /=.
  rewrite Nat.add_0_r.
  rewrite (context_subst_length X).
  rewrite distr_lift_subst Nat.add_0_r.
  now constructor.
Qed.

Derive Signature for subslet.

Lemma closedn_ctx_snoc k Γ d : closedn_ctx k (Γ ,, d) = closedn_ctx k Γ && closed_decl (#|Γ| + k) d.
Proof.
  rewrite /closedn_ctx !mapi_rev /= forallb_app /= /closed_decl /id /=.
  f_equal; first now rewrite mapi_rec_Sk.
  now rewrite Nat.sub_0_r Nat.add_comm andb_true_r.
Qed.

Lemma type_local_ctx_wf_local {cf:checker_flags} Σ Γ Δ s : 
  wf_local Σ Γ ->
  type_local_ctx (lift_typing typing) Σ Γ Δ s ->
  wf_local Σ (Γ ,,, Δ).
Proof.
  induction Δ; simpl; auto.
  destruct a as [na [b|] ty];
  intros wfΓ wfctx; constructor; intuition auto. exists s; auto.
Qed.

Lemma sorts_local_ctx_wf_local {cf:checker_flags} Σ Γ Δ s : 
  wf_local Σ Γ ->
  sorts_local_ctx (lift_typing typing) Σ Γ Δ s ->
  wf_local Σ (Γ ,,, Δ).
Proof.
  induction Δ in s |- *; simpl; auto.
  destruct a as [na [b|] ty];
  intros wfΓ wfctx; constructor; intuition auto. pcuic.
  destruct s => //. destruct wfctx; eauto.
  destruct s => //. destruct wfctx. exists t; auto.
Qed.

Lemma instantiate_minductive {cf:checker_flags} Σ ind mdecl u Γ t T :
  wf Σ.1 ->
  declared_minductive Σ.1 ind mdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  (Σ.1, ind_universes mdecl) ;;; Γ |- t : T ->
  Σ ;;; subst_instance_context u Γ |- subst_instance_constr u t : subst_instance_constr u T.
Proof.
  intros wfΣ isdecl Hu Ht.
  red in isdecl. eapply PCUICUnivSubstitution.typing_subst_instance_decl in isdecl; eauto.
Qed.

Lemma type_local_ctx_instantiate {cf:checker_flags} Σ ind mdecl Γ Δ u s : 
  wf Σ.1 ->
  declared_minductive Σ.1 ind mdecl ->
  type_local_ctx (lift_typing typing) (Σ.1, ind_universes mdecl) Γ Δ s ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  type_local_ctx (lift_typing typing) Σ (subst_instance_context u Γ) (subst_instance_context u Δ) (subst_instance_univ u s).
Proof.
  intros Hctx Hu.
  induction Δ; simpl in *; intuition auto.
  { destruct Σ as [Σ univs]. eapply (wf_universe_subst_instance (Σ, ind_universes mdecl)); eauto.
    simpl in *.
    assert (wg := weaken_lookup_on_global_env'' _ _ _ Hctx Hu).
    eapply sub_context_set_trans. eauto.
    eapply global_context_set_sub_ext. }
  destruct a as [na [b|] ty]; simpl; intuition auto.
  - destruct a0.
    exists (subst_instance_univ u x).
    eapply instantiate_minductive in t; eauto.
    now rewrite PCUICUnivSubstitution.subst_instance_context_app in t.
  - eapply instantiate_minductive in b1; eauto.
    now rewrite PCUICUnivSubstitution.subst_instance_context_app in b1.
  - eapply instantiate_minductive in b; eauto.
    now rewrite PCUICUnivSubstitution.subst_instance_context_app in b.
Qed.

Lemma sorts_local_ctx_instantiate {cf:checker_flags} Σ ind mdecl Γ Δ u s : 
  wf Σ.1 ->
  declared_minductive Σ.1 ind mdecl ->
  sorts_local_ctx (lift_typing typing) (Σ.1, ind_universes mdecl) Γ Δ s ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  sorts_local_ctx (lift_typing typing) Σ (subst_instance_context u Γ) (subst_instance_context u Δ) 
    (List.map (subst_instance_univ u) s).
Proof.
  intros Hctx Hu.
  induction Δ in s |- *; simpl in *; intuition auto.
  destruct s; simpl; intuition eauto.
  destruct a as [na [b|] ty]; simpl; intuition eauto.
  - destruct a0.
    exists (subst_instance_univ u x).
    eapply instantiate_minductive in t; eauto.
    now rewrite PCUICUnivSubstitution.subst_instance_context_app in t.
  - eapply instantiate_minductive in b1; eauto.
    now rewrite PCUICUnivSubstitution.subst_instance_context_app in b1.
  - destruct s; simpl; intuition eauto.
    eapply instantiate_minductive in b; eauto.
    now rewrite PCUICUnivSubstitution.subst_instance_context_app in b.
Qed.

Lemma on_udecl_on_udecl_prop {cf:checker_flags} Σ ctx : 
  on_udecl Σ (Polymorphic_ctx ctx) -> on_udecl_prop Σ (Polymorphic_ctx ctx).
Proof.
  intros [? [? [_ ?]]]. red. split; auto.
Qed.

Lemma wf_local_instantiate_poly {cf:checker_flags} Σ ctx Γ u : 
  wf_ext (Σ.1, Polymorphic_ctx ctx) ->
  consistent_instance_ext Σ (Polymorphic_ctx ctx) u ->
  wf_local (Σ.1, Polymorphic_ctx ctx) Γ -> 
  wf_local Σ (subst_instance_context u Γ).
Proof.
  intros wfΣ Huniv wf.
  epose proof (type_Sort _ _ Universes.Universe.lProp wf) as ty. forward ty.
  - now simpl.
  - eapply PCUICUnivSubstitution.typing_subst_instance_ctx in ty;   
    eauto using typing_wf_local. apply wfΣ.
    destruct wfΣ. now eapply on_udecl_on_udecl_prop.
Qed.

Lemma wf_local_instantiate {cf:checker_flags} Σ (decl : global_decl) Γ u c : 
  wf Σ.1 ->
  lookup_env Σ.1 c = Some decl ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  wf_local (Σ.1, universes_decl_of_decl decl) Γ -> 
  wf_local Σ (subst_instance_context u Γ).
Proof.
  intros wfΣ Hdecl Huniv wf.
  epose proof (type_Sort _ _ Universes.Universe.lProp wf) as ty. forward ty.
  - now simpl.
  - eapply PCUICUnivSubstitution.typing_subst_instance_decl in ty;   
    eauto using typing_wf_local.
Qed.

Lemma subst_type_local_ctx {cf:checker_flags} Σ Γ Δ Δ' s ctxs : 
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Δ) ->
  type_local_ctx (lift_typing typing) Σ (Γ ,,, Δ) Δ' ctxs ->
  subslet Σ Γ s Δ ->
  type_local_ctx (lift_typing typing) Σ Γ (subst_context s 0 Δ') ctxs.
Proof.
  induction Δ'; simpl; auto.
  destruct a as [na [b|] ty]; simpl; intuition auto.
  + destruct a0; simpl; rewrite subst_context_snoc /= /subst_decl /map_decl /= Nat.add_0_r. 
    intuition auto.
    - exists x; auto.
      eapply substitution in t; eauto.
    - eapply substitution in b1; eauto.
  + rewrite subst_context_snoc /= /subst_decl /map_decl /= Nat.add_0_r.
      intuition auto.
      eapply substitution in b; eauto.
Qed.

Lemma subst_sorts_local_ctx {cf:checker_flags} Σ Γ Δ Δ' s ctxs : 
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Δ) ->
  sorts_local_ctx (lift_typing typing) Σ (Γ ,,, Δ) Δ' ctxs ->
  subslet Σ Γ s Δ ->
  sorts_local_ctx (lift_typing typing) Σ Γ (subst_context s 0 Δ') ctxs.
Proof.
  induction Δ' in ctxs |- *; simpl; auto.
  destruct a as [na [b|] ty]; simpl; intuition auto.
  + destruct a0; simpl; rewrite subst_context_snoc /= /subst_decl /map_decl /= Nat.add_0_r. 
    intuition auto.
    - exists x; auto.
      eapply substitution in t; eauto.
    - eapply substitution in b1; eauto.
  + rewrite subst_context_snoc /= /subst_decl /map_decl /= Nat.add_0_r.
    destruct ctxs; auto.
    intuition auto.
    eapply substitution in b; eauto.
Qed.

Lemma weaken_type_local_ctx {cf:checker_flags} Σ Γ Γ' Δ ctxs : 
  wf Σ.1 ->
  wf_local Σ Γ ->
  type_local_ctx (lift_typing typing) Σ Γ' Δ ctxs ->
  type_local_ctx (lift_typing typing) Σ (Γ ,,, Γ') Δ ctxs.
Proof.
  induction Δ; simpl; auto.
  destruct a as [na [b|] ty]; simpl; intuition auto.
  - destruct a0; simpl.
    exists x; auto.
    rewrite -app_context_assoc.
    eapply (weaken_ctx Γ); auto.
  - rewrite -app_context_assoc.
    eapply (weaken_ctx Γ); auto.
  - rewrite -app_context_assoc.
    eapply (weaken_ctx Γ); auto.
Qed.

Lemma weaken_sorts_local_ctx {cf:checker_flags} Σ Γ Γ' Δ ctxs : 
  wf Σ.1 ->
  wf_local Σ Γ ->
  sorts_local_ctx (lift_typing typing) Σ Γ' Δ ctxs ->
  sorts_local_ctx (lift_typing typing) Σ (Γ ,,, Γ') Δ ctxs.
Proof.
  induction Δ in ctxs |- *; simpl; auto.
  destruct a as [na [b|] ty]; simpl; intuition auto.
  - destruct a0; simpl.
    exists x; auto.
    rewrite -app_context_assoc.
    eapply (weaken_ctx Γ); auto.
  - rewrite -app_context_assoc.
    eapply (weaken_ctx Γ); auto.
  - rewrite -app_context_assoc.
    destruct ctxs; auto. destruct X1.
    split; auto; eapply (weaken_ctx Γ); auto.
Qed.

Lemma reln_app acc Γ Δ k : reln acc k (Γ ++ Δ) = 
  reln (reln acc k Γ) (#|Γ| + k) Δ.
Proof.
  induction Γ in acc, Δ, k |- *; simpl; auto.
  destruct a as [na [b|] ty]. rewrite IHΓ. f_equal. lia.
  simpl. rewrite IHΓ. f_equal. lia.
Qed.

Lemma reln_acc acc k Γ : reln acc k Γ = reln [] k Γ ++ acc.
Proof.
  induction Γ in acc, k |- *; simpl; auto.
  destruct a as [na [b|] ty]. rewrite IHΓ. f_equal.
  rewrite IHΓ. rewrite [reln [_] _ _]IHΓ. 
  now rewrite -app_assoc.
Qed.

Lemma to_extended_list_k_app Γ Δ k : to_extended_list_k (Γ ++ Δ) k = 
  to_extended_list_k Δ (#|Γ| + k) ++ to_extended_list_k Γ k.
Proof.
  unfold to_extended_list_k. now rewrite reln_app reln_acc.
Qed.

Lemma to_extended_list_k_fold_context f Γ k : 
  to_extended_list_k (fold_context f Γ) k = to_extended_list_k Γ k.
Proof.
  rewrite /to_extended_list_k.
  generalize (@nil term).
  induction Γ in k |- *.
  simpl; auto.
  intros.
  rewrite fold_context_snoc0. simpl.
  destruct a as [? [?|] ?] => /=; now rewrite IHΓ.  
Qed.

Lemma to_extended_list_k_lift_context c k n k' : 
  to_extended_list_k (lift_context n k c) k' = to_extended_list_k c k'. 
Proof. now rewrite to_extended_list_k_fold_context. Qed.

Lemma reln_lift n k Γ : reln [] (n + k) Γ = map (lift0 n) (reln [] k Γ).
Proof.
  induction Γ in n, k |- *; simpl; auto.
  destruct a as [? [?|] ?]; simpl.
  now rewrite -IHΓ Nat.add_assoc.
  rewrite reln_acc  [reln [tRel k] _ _]reln_acc map_app /=.
  f_equal. now rewrite -IHΓ Nat.add_assoc.
Qed.

Lemma to_extended_list_length Γ : #|to_extended_list Γ| = context_assumptions Γ.
Proof. now rewrite /to_extended_list PCUICCtxShape.to_extended_list_k_length. Qed.
Hint Rewrite to_extended_list_length : len.

Lemma map_subst_app_to_extended_list_k s s' ctx k  :
  k = #|s| ->
  map (subst0 (s ++ s')) (to_extended_list_k ctx k) = 
  map (subst0 s') (to_extended_list_k ctx 0).
Proof.
  intros ->.
  rewrite /to_extended_list_k.
  rewrite -{1}(Nat.add_0_r #|s|) reln_lift map_map_compose.
  apply map_ext. intros x; simpl.
  rewrite subst_app_decomp.
  f_equal. rewrite -{1}(Nat.add_0_r #|s|) simpl_subst' ?lift0_id //.
  now rewrite map_length.
Qed.
  
Lemma subst_context_smash_context s k Γ Δ :
  subst_context s k (smash_context Γ Δ) = 
  smash_context (subst_context s (#|Δ| + k) Γ) (subst_context s k Δ).
Proof.
  induction Δ as [|[? [] ?] ?] in Γ |- *; simpl; auto;
    rewrite subst_context_snoc; simpl.
  - rewrite IHΔ. f_equal.
    rewrite !subst_context_alt !mapi_mapi. apply mapi_ext. clear.
    intros n x. rewrite /subst_decl !PCUICAstUtils.compose_map_decl.
    eapply PCUICAstUtils.map_decl_ext. intros.
    autorewrite with len.
    generalize (Nat.pred #|Γ| - n). generalize (#|Δ| + k). clear.
    intros. rewrite distr_subst_rec. simpl. now rewrite -Nat.add_assoc.
  - rewrite IHΔ. f_equal.
    rewrite subst_context_app. simpl.  unfold app_context. f_equal.
Qed.

Lemma wf_local_rel_smash_context_gen {cf:checker_flags} Σ Γ Δ Δ' :
  wf Σ.1 ->
  wf_local Σ (Δ' ,,, Γ) -> 
  wf_local_rel Σ (Δ' ,,, Γ) Δ ->
  wf_local_rel Σ Δ' (smash_context Δ Γ).
Proof.
  intros wfΣ.
  induction Γ in Δ |- *; simpl; auto.
  intros wfΓ wfΔ. depelim wfΓ; simpl.
  - apply IHΓ; auto. eapply All_local_env_app. split; auto.
    repeat constructor; auto.
    eapply All_local_env_impl; eauto. simpl; intros.
    unfold lift_typing in X |- *.
    now rewrite app_context_assoc.
  - apply IHΓ. auto. eapply All_local_env_subst; eauto. simpl; intros.
    destruct T; unfold lift_typing in X |- *; simpl in *; pcuicfo auto.
    rewrite Nat.add_0_r.
    eapply (substitution _ (Δ' ,,, Γ) [vdef na b t] [b] Γ0) in X; eauto.
    rewrite -{1}(subst_empty 0 b). repeat constructor. now rewrite !subst_empty.
    destruct X as [s Hs]; exists s.
    rewrite Nat.add_0_r.
    eapply (substitution _ _ [vdef na b t] [b] Γ0) in Hs; eauto.
    rewrite -{1}(subst_empty 0 b). repeat constructor. now rewrite !subst_empty.
Qed.

Lemma wf_local_rel_smash_context {cf:checker_flags} Σ Γ Δ :
  wf Σ.1 ->
  wf_local Σ (Δ ,,, Γ) -> 
  wf_local_rel Σ Δ (smash_context [] Γ).
Proof.
  intros. eapply wf_local_rel_smash_context_gen; eauto. constructor.
Qed.

Lemma wf_local_smash_end {cf:checker_flags} Σ Γ Δ : 
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Δ) -> wf_local Σ (Γ ,,, smash_context [] Δ).
Proof.
  intros wfΣ  wf. 
  apply All_local_env_app. split.
  now apply All_local_env_app_inv in wf.
  eapply wf_local_rel_smash_context; auto.
Qed.

Lemma wf_local_rel_empty {cf:checker_flags} Σ Γ : wf_local_rel Σ [] Γ <~> wf_local Σ Γ.
Proof.
  split.
  - intros h. eapply (All_local_env_impl _ _ _ h). pcuicfo.
    red in X |- *. now rewrite app_context_nil_l in X.
  - intros h. eapply (All_local_env_impl _ _ _ h). pcuicfo.
    red in X |- *. now rewrite app_context_nil_l.
Qed.

Lemma wf_local_smash_context {cf:checker_flags} Σ Γ :
  wf Σ.1 -> wf_local Σ Γ -> wf_local Σ (smash_context [] Γ).
Proof.
  intros; apply wf_local_rel_empty. eapply (wf_local_rel_smash_context Σ Γ []); 
    rewrite ?app_context_nil_l; eauto.
Qed.

Lemma context_assumptions_smash_context Δ Γ :
  context_assumptions (smash_context Δ Γ) = 
  context_assumptions Δ + context_assumptions Γ.
Proof.
  induction Γ as [|[? [] ?] ?] in Δ |- *; simpl; auto;
  rewrite IHΓ.
  - now rewrite context_assumptions_fold.
  - rewrite context_assumptions_app /=. lia.
Qed. 

Lemma nth_error_ass_subst_context s k Γ : 
  (forall n d, nth_error Γ n = Some d -> decl_body d = None) ->
  forall n d, nth_error (subst_context s k Γ) n = Some d -> decl_body d = None.
Proof.
  induction Γ as [|[? [] ?] ?] in |- *; simpl; auto;
  intros; destruct n; simpl in *; rewrite ?subst_context_snoc in H0; simpl in H0.
  - noconf H0; simpl.
    specialize (H 0 _ eq_refl). simpl in H; discriminate.
  - specialize (H 0 _ eq_refl). simpl in H; discriminate.
  - noconf H0; simpl. auto.
  - eapply IHΓ. intros. now specialize (H (S n0) d0 H1).
    eauto.
Qed.

Lemma nth_error_smash_context Γ Δ : 
  (forall n d, nth_error Δ n = Some d -> decl_body d = None) ->
  forall n d, nth_error (smash_context Δ Γ) n = Some d -> decl_body d = None.
Proof.
  induction Γ as [|[? [] ?] ?] in Δ |- *; simpl; auto.
  - intros. eapply (IHΓ (subst_context [t] 0 Δ)).
    apply nth_error_ass_subst_context. auto. eauto.
  - intros. eapply IHΓ. 2:eauto.
    intros.
    pose proof (nth_error_Some_length H1). autorewrite with len in H2. simpl in H2.
    destruct (eq_dec n0 #|Δ|). subst.
    rewrite nth_error_app_ge in H1. lia. rewrite Nat.sub_diag /= in H1. noconf H1.
    reflexivity.
    rewrite nth_error_app_lt in H1; try lia. eauto.
Qed.

Lemma context_subst_extended_subst Γ args s : 
  context_subst Γ args s ->
  s = map (inst (List.rev args ⋅n ids)) (extended_subst Γ 0).
Proof.
  induction 1.
  - simpl; auto.
  - simpl.
    rewrite lift_extended_subst.
    rewrite map_map_compose.
    rewrite List.rev_app_distr. simpl. f_equal.
    rewrite IHX. apply map_ext.
    intros. autorewrite with sigma.
    apply inst_ext.
    rewrite subst_consn_subst_cons.
    now rewrite subst_cons_shift.
  - simpl.
    f_equal; auto.
    rewrite IHX.
    autorewrite with sigma.
    apply inst_ext.
    rewrite ren_lift_renaming. autorewrite with len.
    rewrite subst_consn_compose.
    autorewrite with sigma.
    unfold Upn.
    rewrite subst_consn_compose.
    apply subst_consn_proper; first last.
    rewrite -subst_consn_app.
    rewrite shiftk_compose.
    rewrite subst_consn_shiftn //.
    autorewrite with len. now rewrite (context_subst_length2 X).
    rewrite map_inst_idsn //. now autorewrite with len.
Qed.

Lemma map_subst_app_decomp (l l' : list term) (k : nat) (ts : list term) :
  map (subst (l ++ l') k) ts = map (fun x => subst l' k (subst (map (lift0 #|l'|) l) k x)) ts.
Proof.
  apply map_ext. apply subst_app_decomp.
Qed.

Lemma map_reln_ext (f g : term -> term) k Γ :
  (forall n, n < #|Γ| -> f (tRel (k + n)) = g (tRel (k + n))) ->
  map f (reln [] k Γ) = map g (reln [] k Γ).
Proof.
  intros Hf.
  induction Γ as [|[? [] ?] ?] in k, Hf |- *; simpl; auto.
  - rewrite reln_acc map_app. simpl.
    rewrite map_app /=. rewrite IHΓ //.
    intros. simpl in Hf. specialize (Hf (S n)).
    forward Hf. lia. rewrite -Nat.add_assoc. apply Hf.
  - rewrite reln_acc map_app. simpl.
    rewrite map_app /= IHΓ //.
    intros. simpl in Hf. specialize (Hf (S n)).
    forward Hf. lia. rewrite -Nat.add_assoc. apply Hf.
    f_equal. f_equal. specialize (Hf 0). simpl in Hf.
    forward Hf by lia. now rewrite Nat.add_0_r in Hf.
Qed.

Lemma extended_subst_to_extended_list_k Γ k :
  (map (subst (extended_subst Γ 0) k) (to_extended_list_k Γ k)) = 
  to_extended_list_k (smash_context [] Γ) k.
Proof.
  unfold to_extended_list_k.
  induction Γ in k |- *. simpl. reflexivity.
  destruct a as [? [] ?]; simpl.
  - rewrite smash_context_acc //.
    rewrite reln_app. autorewrite with len. simpl.
    rewrite -IHΓ //. rewrite Nat.add_1_r.
    rewrite (reln_lift 1). 
    clear.
    rewrite (map_subst_app_decomp [_]).
    rewrite -map_map_compose. f_equal.
    simpl.
    generalize (lift0 #|extended_subst Γ 0| 
      (subst0 (extended_subst Γ 0) (lift (context_assumptions Γ) #|Γ| t))).
    intros t0.
    change 1 with #|[t0]|.
    generalize [t0]. clear.
    intros l. generalize (Nat.le_refl k).
    generalize k at 1 3.
    induction Γ as [|[? [] ?] ?] in k, l |- *; simpl. reflexivity.
    simpl. intros k0 le0. apply IHΓ. lia.
    intros k0 lek0. rewrite reln_acc map_app. simpl.
    rewrite map_app. simpl.
    elim: leb_spec_Set => Hle. f_equal. apply IHΓ. lia.
    f_equal. elim: nth_error_spec => [x Hx Hl|Hl]. lia.
    f_equal. lia. lia.
  - rewrite smash_context_acc //.
    simpl.
    rewrite reln_acc map_app.
    rewrite (reln_acc [_] _ (smash_context [] Γ)). 
    simpl. rewrite Nat.leb_refl Nat.sub_diag /=. f_equal.
    rewrite -IHΓ //.
    2:{ do 2 f_equal; lia. }
    apply map_reln_ext => n Hn.
    rewrite lift_extended_subst //.
    replace (k + 1 + n) with (S (k + n)) by lia.
    simpl.
    elim: leb_spec_Set => Hle; [|lia].
    elim: leb_spec_Set => Hle'; [|lia].
    replace (S (k + n) - k) with (S n) by lia.
    replace (S (k + n) - (k + 1)) with n by lia.
    simpl.
    rewrite nth_error_map.
    elim: nth_error_spec => [x Hx Hlen|Hlen].
    simpl. rewrite simpl_lift; try lia. f_equal. simpl.
    autorewrite with len in Hlen. lia.
Qed.

Hint Rewrite arities_context_length : len.

Lemma assumption_context_fold f Γ :
  assumption_context Γ -> assumption_context (fold_context f Γ).
Proof. 
  induction 1; simpl. constructor. rewrite fold_context_snoc0.
  now constructor.
Qed.
