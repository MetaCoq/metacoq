From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.CRelationClasses ProofIrrelevance.
From MetaCoq.Template Require Import config Universes monad_utils utils BasicAst
     AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping
     PCUICCumulativity PCUICPosition PCUICEquality PCUICNameless
     PCUICAlpha PCUICNormal PCUICInversion PCUICCumulativity PCUICReduction
     PCUICConfluence PCUICConversion PCUICContextConversion PCUICValidity
     PCUICParallelReductionConfluence PCUICWeakeningEnv
     PCUICClosed PCUICPrincipality PCUICSubstitution
     PCUICWeakening PCUICGeneration PCUICUtils PCUICCtxShape.

From Equations Require Import Equations.

Require Import Equations.Prop.DepElim.
Require Import Equations.Type.Relation_Properties.
Require Import ssreflect ssrbool.

Derive Signature for context_subst.

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

Lemma smash_context_app Δ Γ Γ' : smash_context Δ (Γ ++ Γ')%list = smash_context (smash_context Δ Γ) Γ'.
Proof.
  revert Δ; induction Γ as [|[na [b|] ty]]; intros Δ; simpl; auto.
Qed.

Lemma smash_context_subst Δ s n Γ : smash_context (subst_context s (n + #|Γ|) Δ) (subst_context s n Γ) =
  subst_context s n (smash_context Δ Γ).
Proof.
  revert Δ. induction Γ as [|[na [b|] ty]]; intros Δ; simpl; auto.
  - now rewrite Nat.add_0_r.
  - rewrite -IHΓ.
    rewrite subst_context_snoc /=. f_equal.
    rewrite !subst_context_alt !mapi_compose.
    apply mapi_ext=> n' x.
    destruct x as [na' [b'|] ty']; simpl.
    * rewrite !mapi_length /subst_decl /= /map_decl /=; f_equal.
      f_equal. rewrite Nat.add_0_r distr_subst_rec. simpl. 
      f_equal; try lia. do 2 f_equal; lia. f_equal; lia.
      rewrite Nat.add_0_r distr_subst_rec; simpl.
      f_equal; try lia. do 2 f_equal; lia. f_equal; lia.
    * rewrite !mapi_length /subst_decl /= /map_decl /=; f_equal.
      rewrite Nat.add_0_r distr_subst_rec /=.
      f_equal. f_equal; f_equal; lia. f_equal; lia. 
  - rewrite -IHΓ.
    rewrite subst_context_snoc /= // /subst_decl /map_decl /=.
    f_equal.
    rewrite subst_context_app. simpl.
    rewrite /app_context. f_equal.
    f_equal; lia.
    rewrite /subst_context // /fold_context /= /map_decl /=.
    f_equal. f_equal. f_equal; lia.
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
  depelim Hconv;
  simpl in H; noconf H.
  constructor; auto.
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
Proof.
induction ctx; simpl; auto.
destruct a as [na [b|] ty]; simpl.
intros. depelim H; simpl in H0; noconf H0.
depelim H; simpl in H0; noconf H0.
rewrite IHctx; auto.
Qed.

Lemma context_subst_length2 {ctx args s} : context_subst ctx args s -> #|args| = context_assumptions ctx.
Proof.
  induction 1; simpl; auto.
  rewrite app_length; simpl; lia.
Qed.

Lemma context_subst_fun {ctx args s s'} : context_subst ctx args s -> context_subst ctx args s' -> s = s'.
Proof.
  induction 1 in s' |- *; intros H'; depelim H'; try simpl in H; try noconf H; auto.
  eapply app_inj_tail in H0. intuition subst.
  now specialize (IHX _ H').
  now specialize (IHX _ H').
Qed.

Lemma context_subst_fun' {ctx args args' s s'} : context_subst ctx args s -> context_subst ctx args' s' -> #|args| = #|args'|.
Proof.
  induction 1 as [ | ? ? ? ? ? ? ? IHX | ? ? ? ? ? ? ? IHX ] in args', s' |- *; intros H'; depelim H'; try simpl in H; try noconf H; auto.
  now rewrite !app_length; specialize (IHX _ _ H').
  now specialize (IHX _ _ H').
Qed.

Hint Constructors context_subst : core.
Close Scope string_scope.

Lemma context_subst_app {ctx ctx' args s} : 
  context_subst (ctx ++ ctx')%list args s -> 
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
  context_subst (List.rev tele ++ ctx)%list (args ++ args') s'.
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
      
      specialize (IHtele (vass na ty :: ctx) (args ++ [a])%list (a :: s) args' s').
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

Lemma reln_lift n k Γ : reln [] (n + k) Γ = map (lift0 n) (reln [] k Γ).
Proof.
  induction Γ in n, k |- *; simpl; auto.
  destruct a as [? [?|] ?]; simpl.
  now rewrite -IHΓ Nat.add_assoc.
  rewrite reln_acc  [reln [tRel k] _ _]reln_acc map_app /=.
  f_equal. now rewrite -IHΓ Nat.add_assoc.
Qed.

Lemma map_subst_app_to_extended_list_k s s' ctx k  :
  k = #|s| ->
  map (subst0 (s ++ s')) (to_extended_list_k ctx k) = 
  map (subst0 s') (to_extended_list_k ctx 0).
Proof.
  intros ->.
  rewrite /to_extended_list_k.
  rewrite -{1}(Nat.add_0_r #|s|) reln_lift map_map_compose.
  apply map_ext. intros x; unfold compose; simpl.
  rewrite subst_app_decomp.
  f_equal. rewrite -{1}(Nat.add_0_r #|s|) simpl_subst' ?lift0_id //.
  now rewrite map_length.
Qed.
