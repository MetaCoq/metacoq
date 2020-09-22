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

Lemma ctx_length_ind (P : context -> Type) (p0 : P [])
  (pS : forall d Γ, (forall Γ', #|Γ'| <= #|Γ|  -> P Γ') -> P (d :: Γ)) 
  Γ : P Γ.
Proof.
  generalize (le_n #|Γ|).
  generalize #|Γ| at 2.
  induction n in Γ |- *.
  destruct Γ; [|simpl; intros; elimtype False; lia].
  intros. apply p0.
  intros.
  destruct Γ; simpl in *.
  apply p0. apply pS. intros. apply IHn. simpl. lia.
Qed.

Lemma ctx_length_rev_ind (P : context -> Type) (p0 : P [])
  (pS : forall d Γ, (forall Γ', #|Γ'| <= #|Γ|  -> P Γ') -> P (Γ ++ [d])) 
  Γ : P Γ.
Proof.
  generalize (le_n #|Γ|).
  generalize #|Γ| at 2.
  induction n in Γ |- *.
  destruct Γ using rev_ind; [|simpl; rewrite app_length /=; intros; elimtype False; try lia].
  intros. apply p0.
  destruct Γ using rev_ind; simpl in *; rewrite ?app_length /=; intros Hlen.
  intros. apply p0.
  apply pS. intros. apply IHn. simpl. lia.
Qed.

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

Lemma assumption_context_length ctx : assumption_context ctx ->
  context_assumptions ctx = #|ctx|.
Proof. induction 1; simpl; auto. Qed.

Lemma context_subst_length2 {ctx args s} : context_subst ctx args s -> #|args| = context_assumptions ctx.
Proof.
  induction 1; simpl; auto.
  rewrite app_length; simpl; lia.
Qed.

Lemma context_subst_fun {ctx args s s'} : context_subst ctx args s -> context_subst ctx args s' -> s = s'.
Proof.
  induction 1 in s' |- *; intros H'; depelim H'; auto.
  eapply app_inj_tail in H. intuition subst.
  now specialize (IHX _ H').
  now specialize (IHX _ H').
Qed.

Lemma context_subst_fun' {ctx args args' s s'} : context_subst ctx args s -> context_subst ctx args' s' -> #|args| = #|args'|.
Proof.
  induction 1 as [ | ? ? ? ? ? ? ? IHX | ? ? ? ? ? ? ? IHX ] in args', s' |- *; intros H'; depelim H'; auto.
  now rewrite !app_length; specialize (IHX _ _ H').
  now specialize (IHX _ _ H').
Qed.

Hint Constructors context_subst : core.

Lemma context_subst_app {ctx ctx' args s} : 
  context_subst (ctx ++ ctx') args s -> 
  context_subst (subst_context (skipn #|ctx| s) 0 ctx) (skipn (context_assumptions ctx') args) (firstn #|ctx| s) *
  context_subst ctx' (firstn (context_assumptions ctx') args) (skipn #|ctx| s).
Proof.
  revert ctx' args s.
  induction ctx; intros ctx' args s; simpl.
  - intros Hc. rewrite !skipn_0.
    rewrite - !(context_subst_length2 Hc).
    now rewrite firstn_all skipn_all.
  - intros Hc.
    depelim Hc. simpl.
    rewrite skipn_S.
    specialize (IHctx _ _ _ Hc) as [IHctx IHctx'].
    pose proof (context_subst_length2 IHctx).
    pose proof (context_subst_length2 IHctx').
    pose proof (context_subst_length2 Hc).
    rewrite context_assumptions_app in H1. 
    rewrite firstn_app. rewrite (firstn_0 [a0]).
    rewrite firstn_length_le in H0. lia. lia.
    rewrite app_nil_r. split; auto.
    rewrite skipn_app_le. lia.
    rewrite subst_context_snoc.
    now constructor.

    specialize (IHctx _ _ _ Hc).
    split; try now rewrite skipn_S.
    pose proof (context_subst_length2 Hc).
    rewrite context_assumptions_app in H.
    destruct IHctx as [IHctx _].
    pose proof (context_subst_length _ _ _ IHctx).
    rewrite subst_context_snoc. rewrite !skipn_S.
    rewrite /subst_decl /map_decl /= Nat.add_0_r.
    rewrite -{4}(firstn_skipn #|ctx| s0).
    rewrite subst_app_simpl. simpl.
    rewrite subst_context_length in H0. rewrite -H0.
    now constructor.
Qed.

Lemma make_context_subst_rec_spec ctx args s tele args' s' :
  context_subst ctx args s ->
  (make_context_subst tele args' s = Some s') <~>
  context_subst (List.rev tele ++ ctx) (args ++ args') s'.
Proof.
  induction tele in ctx, args, s, args', s' |- *.
  - move=> /= Hc. case: args'.
    split.  move => [= <-].
    now rewrite app_nil_r.
    rewrite app_nil_r.
    move/context_subst_fun => Hs. now specialize (Hs _ Hc).
    intros. split; try discriminate.
    intros H2. pose proof (context_subst_fun' Hc H2).
    rewrite app_length /= in H. now lia.
  - move=> Hc /=. case: a => [na [body|] ty] /=.
    * specialize (IHtele (vdef na body ty :: ctx) args (subst0 s body :: s) args' s').
       move=> /=. rewrite <- app_assoc.
       now forward IHtele by (constructor; auto).
    * destruct args' as [|a args'].
      split; [congruence | ]. intros Hc'.
      pose proof (context_subst_length2 Hc').
      rewrite !context_assumptions_app ?app_length ?List.rev_length /= Nat.add_0_r in H.
      pose proof (context_subst_length2 Hc). lia.
      
      specialize (IHtele (vass na ty :: ctx) (args ++ [a]) (a :: s) args' s').
      forward IHtele. econstructor. auto.
      rewrite -app_assoc. rewrite -app_comm_cons /=.
      rewrite -app_assoc in IHtele. apply IHtele.
Qed.

Lemma make_context_subst_spec_inv : forall (tele : list context_decl) (args s' : list term),
  context_subst (List.rev tele) args s' ->
  make_context_subst tele args [] = Some s'.
Proof.
  intros. assert (H:=make_context_subst_rec_spec [] [] [] tele args s').
  forward H by constructor.
  rewrite app_nil_r in H. destruct H.
  simpl in *. auto.
Qed.

Lemma map_subst_instance_constr_to_extended_list_k u ctx k :
  map (subst_instance_constr u) (to_extended_list_k (subst_instance_context u ctx) k)
  = to_extended_list_k (subst_instance_context u ctx) k.
Proof.
  pose proof (to_extended_list_k_spec (subst_instance_context u ctx) k).
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
  rewrite (context_subst_length _ _ _ X).
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

Lemma wf_local_instantiate {cf:checker_flags} Σ (decl : global_decl) Γ u c : 
  wf Σ.1 ->
  lookup_env Σ.1 c = Some decl ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  wf_local (Σ.1, universes_decl_of_decl decl) Γ -> 
  wf_local Σ (subst_instance_context u Γ).
Proof.
  intros wfΣ Hdecl Huniv wf.
  epose proof (type_Sort _ _ Universes.Level.lProp wf) as ty. forward ty.
  - apply prop_global_ext_levels.
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
  - apply IHΓ; auto. eapply All_local_env_app_inv. split; auto.
    repeat constructor; auto.
    eapply All_local_env_impl; eauto. simpl; intros.
    unfold lift_typing in X |- *.
    now rewrite app_context_assoc.
  - apply IHΓ. auto. eapply All_local_env_subst; eauto. simpl; intros.
    destruct T; unfold lift_typing in X |- *; simpl in *; firstorder auto.
    rewrite Nat.add_0_r.
    eapply (substitution _ (Δ' ,,, Γ) [vdef na b t] [b] Γ0) in X; eauto.
    rewrite -{1}(subst_empty 0 b). repeat constructor. now rewrite !subst_empty.
    exists x.
    rewrite Nat.add_0_r.
    eapply (substitution _ _ [vdef na b t] [b] Γ0) in p; eauto.
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
  apply All_local_env_app_inv. split.
  now apply All_local_env_app in wf.
  eapply wf_local_rel_smash_context; auto.
Qed.

Lemma wf_local_rel_empty {cf:checker_flags} Σ Γ : wf_local_rel Σ [] Γ <~> wf_local Σ Γ.
Proof.
  split.
  - intros h. eapply (All_local_env_impl _ _ _ h). firstorder.
    red in X |- *. now rewrite app_context_nil_l in X.
  - intros h. eapply (All_local_env_impl _ _ _ h). firstorder.
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

Lemma map_subst_closedn (s : list term) (k : nat) l :
  forallb (closedn k) l -> map (subst s k) l = l.
Proof.
  induction l; simpl; auto.
  move/andP=> [cla cll]. rewrite IHl //.
  now rewrite subst_closedn.
Qed.

Lemma closedn_extended_subst_gen Γ k k' : 
  closedn_ctx k Γ -> 
  forallb (closedn (k' + k + context_assumptions Γ)) (extended_subst Γ k').
Proof.
  induction Γ as [|[? [] ?] ?] in k, k' |- *; simpl; auto;
  rewrite ?closedn_ctx_cons;
   move/andP => [clΓ /andP[clb clt]].
  - rewrite IHΓ //.
    epose proof (closedn_subst (extended_subst Γ k') (k' + k + context_assumptions Γ) 0).
    autorewrite with len in H. rewrite andb_true_r.
    eapply H; auto.
    replace (k' + k + context_assumptions Γ + #|Γ|)
    with (k + #|Γ| + (context_assumptions Γ + k')) by lia.
    eapply closedn_lift. eapply clb.
  - apply andb_and. split.
    * apply Nat.ltb_lt; lia.
    * specialize (IHΓ k (S k') clΓ).
      red. rewrite -IHΓ. f_equal. f_equal. lia.
Qed.

Lemma closedn_extended_subst Γ : 
  closed_ctx Γ -> 
  forallb (closedn (context_assumptions Γ)) (extended_subst Γ 0).
Proof.
  intros clΓ. now apply (closedn_extended_subst_gen Γ 0 0).
Qed.
