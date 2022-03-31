From Equations Require Import Equations.
From Coq Require Import ssreflect.
From MetaCoq.Template Require Import config utils.
From MetaCoq.Template Require Ast TypingWf WfAst TermEquality EtaExpand.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCumulativity
     PCUICLiftSubst PCUICEquality PCUICReduction 
     PCUICUnivSubst PCUICTyping PCUICGlobalEnv TemplateToPCUIC
     PCUICWeakeningConv PCUICWeakeningTyp PCUICSubstitution PCUICGeneration PCUICCasesContexts TemplateToPCUICCorrectness PCUICEtaExpand.

Tactic Notation "wf_inv" ident(H) simple_intropattern(p) :=
(eapply WfAst.wf_inv in H; progress cbn in H; try destruct H as p) || 
(apply WfAst.wf_mkApps_napp in H; [|easy]; try destruct H as p).

Local Hint Constructors expanded : expanded.

Lemma expanded_context_map2_bias_left Σ n bctx ctx :
  #|ctx| = #|bctx| ->
  expanded_context Σ n ctx ->
  expanded_context Σ n
     (map2_bias_left set_binder_name dummy_decl bctx ctx).
Proof.
  unfold expanded_context.
  intros hl. 
  rewrite map2_map2_bias_left //.
  intros [a]. sq.
  induction a in bctx, hl |- *; try econstructor; auto.
  - cbn. destruct bctx; constructor.
  - destruct bctx => //.
    cbn. constructor; auto. cbn.
    destruct (decl_body d); constructor => //. depelim p.
    cbn in hl. assert (#|Γ| = #|bctx|) by lia.
    rewrite map2_length //. now rewrite -H0.
Qed.

Import PCUICWeakeningEnvConv.

Lemma extends_decls_trans Σ Σ' Σ'' : extends_decls Σ Σ' -> extends_decls Σ' Σ'' -> extends_decls Σ Σ''.
Proof.
  intros [? [ext ?]] [? [ext' ?]]. subst. split. now transitivity Σ'.
  rewrite e0 in e2. exists (ext' ++ ext). now rewrite -app_assoc.
Qed.

Lemma declared_minductive_expanded Σ c mdecl :
  expanded_global_env Σ ->
  declared_minductive Σ c mdecl ->
  exists Σ', ∥ extends_decls Σ' Σ ∥ /\ expanded_minductive_decl Σ' mdecl.
Proof.
  unfold expanded_global_env, declared_minductive, lookup_env.
  destruct Σ as [univs Σ]; cbn.
  intros exp; induction exp; cbn => //.
  destruct decl as [kn d]; cbn.
  destruct (eqb_spec c kn). intros [= ->].
  subst c. eexists. split ; [|exact H]. sq. red. split => //. cbn. 
  eexists. cbn. instantiate (1:= [_]); reflexivity.
  intros hl; destruct (IHexp hl). exists x. intuition auto.
  sq. eapply extends_decls_trans; tea. 
  split => //. now exists [(kn, d)].
Qed.

Lemma declared_constructor_expanded {Σ c mdecl idecl cdecl} : 
  expanded_global_env Σ ->
  declared_constructor Σ c mdecl idecl cdecl ->
  exists Σ', ∥ extends_decls Σ' Σ ∥ /\ expanded_minductive_decl Σ' mdecl /\ expanded_constructor_decl Σ' mdecl cdecl.
Proof.
  intros exp [[decli hnth] hnth'].
  eapply declared_minductive_expanded in decli.
  destruct decli as [Σ' [ext exp']]. exists Σ'; split => //. split => //.
  destruct exp' as [hp hb]. solve_all. 
  eapply nth_error_all in hb; tea.
  destruct hb as [hb]. solve_all.
  eapply nth_error_all in hb; tea.
  auto.
Qed.

Lemma expanded_extended_subst {Σ Γ Δ} : 
  expanded_context Σ Γ Δ -> 
  forall n,
  Forall (expanded Σ (repeat 0 (n + context_assumptions Δ) ++ Γ)) (extended_subst Δ n).
Proof.
  intros [a]; induction a. cbn. constructor.
  cbn. destruct d as [na [b|] ty]; cbn in *. constructor; auto. 
  { cbn. eapply (expanded_subst _ _ 0 _ []) => //. cbn. rewrite -/(repeat _ _).
    specialize (IHa n). solve_all.
    len. rewrite repeat_app Nat.add_comm. 
    eapply expanded_lift. 1-2:now len; rewrite !repeat_length.
    now depelim p. }
  constructor; auto.
  eapply (expanded_tRel _ _ _ _ []) => //. cbn.
  rewrite nth_error_app_lt. rewrite repeat_length. lia.
  rewrite nth_error_repeat //. lia.
  specialize (IHa (S n)).
  now rewrite Nat.add_succ_r.
Qed.

Lemma expanded_let_expansion {Σ} {Δ : context} {Γ t} :
  expanded_context Σ Γ Δ ->
  expanded_context Σ (repeat 0 #|Δ| ++ Γ) t ->
  expanded_context Σ (repeat 0 (context_assumptions Δ) ++ Γ) (expand_lets_ctx Δ t).
Proof.
  rewrite /expanded_context.
  intros [aΔ] [a]; sq.
  unfold expand_lets_ctx, expand_lets_k_ctx.
  do 2 eapply PCUICParallelReduction.All_fold_fold_context_k.
  eapply All_fold_impl; tea. cbn.
  intros Γ' x f. destruct (decl_body x) => //; constructor.
  len. depelim f.
  eapply expanded_subst. now rewrite repeat_length.
  clear -aΔ. eapply (expanded_extended_subst (sq aΔ) 0).
  len. rewrite app_assoc -repeat_app. eapply expanded_lift. len. now rewrite !repeat_length.
  now rewrite repeat_length. rewrite repeat_app -app_assoc //.
Qed.

Lemma expanded_context_subst {Σ} {Δ Δ' : list nat} {Γ s k t} :
  #|s| = #|Δ'| ->
  #|Δ| = k ->
  Forall (expanded Σ Γ) s ->
  expanded_context Σ (Δ ++ repeat 0 #|Δ'| ++ Γ) t ->
  expanded_context Σ (Δ ++ Γ) (subst_context s k t).
Proof.
  intros hs hs' has.
  rewrite /expanded_context.
  intros [aΔ]; sq.
  eapply PCUICParallelReduction.All_fold_fold_context_k.
  eapply All_fold_impl; tea. cbn.
  intros Γ' x f. destruct (decl_body x) => //; constructor.
  len. depelim f. rewrite app_assoc.
  eapply expanded_subst. len. rewrite repeat_length. lia. solve_all. auto.
  now rewrite -app_assoc hs.
Qed.

Lemma expanded_inds {Σ Γ ind u bodies} : Forall (expanded Σ Γ) (inds ind u bodies).
Proof.
  unfold inds. induction #|bodies|; cbn; auto. constructor => //. constructor.
Qed.

Implicit Types (cf : checker_flags).

Lemma expanded_weakening {cf} {Σ Σ' Γ t} : 
  wf Σ' -> extends_decls Σ Σ' -> expanded Σ Γ t -> expanded Σ' Γ t.
Proof.
  intros wfΣ ext.
  eapply expanded_ind; intros.
  all:try solve [econstructor; eauto].
  - econstructor; eauto. solve_all. sq. eapply All_fold_impl; tea; cbn.
    intros ? ? []; constructor; auto. now rewrite <- repeat_app.
  - eapply expanded_tConstruct_app; tea.
    eapply weakening_env_declared_constructor; tea. now eapply extends_decls_extends.
Qed.

Lemma expanded_context_weakening {cf} {Σ Σ' Γ t} : 
  wf Σ' -> extends_decls Σ Σ' -> expanded_context Σ Γ t -> expanded_context Σ' Γ t.
Proof.
  intros wfΣ ext.
  intros [a]; sq.
  eapply All_fold_impl; tea; cbn; eauto.
  intros ?? []; constructor.
  now eapply expanded_weakening.
Qed.

Lemma expanded_bcontext {cf} Σ ind k mdecl idecl cdecl bctx bbody :
  wf Σ ->
  PCUICEtaExpand.expanded_global_env Σ ->
  #|cstr_branch_context ind mdecl cdecl| = #|bctx| ->
  declared_constructor Σ (ind, k) mdecl idecl cdecl ->
  expanded_context Σ (repeat 0 (context_assumptions mdecl.(ind_params))) (bcontext (trans_branch ind mdecl cdecl bctx bbody)).
Proof.
  intros wfΣ expΣ hl declc.
  eapply expanded_context_map2_bias_left => //.
  destruct (declared_constructor_expanded expΣ declc) as [Σ' [ext [expm expc]]].
  destruct expm as [hp hb]. destruct expc as [hargs hty].
  unfold cstr_branch_context.
  epose proof (expanded_let_expansion hp (t:=(subst_context
  (inds (inductive_mind ind) (abstract_instance (ind_universes mdecl))
     (ind_bodies mdecl)) #|ind_params mdecl| 
  (cstr_args cdecl)))).
  rewrite !app_nil_r in H. forward H.
  epose proof (expanded_context_subst (Γ := []) (Δ' := repeat 0 #|ind_bodies mdecl|)).
  rewrite !app_nil_r in H0. eapply H0; rewrite ?repeat_length //. len. apply expanded_inds.
  rewrite -repeat_app. exact hargs.
  destruct ext. eapply expanded_context_weakening; tea.
Qed.

Lemma trans_expanded {cf : checker_flags} {Σ} {wfΣ : Template.Typing.wf Σ} Γ T  :
  let Σ' := trans_global_env Σ in
  WfAst.wf Σ T ->
  PCUICEtaExpand.expanded_global_env Σ' ->
  EtaExpand.expanded Σ Γ T ->
  expanded Σ' Γ (trans Σ' T).
Proof with eauto using expanded.
  intros Σ' wf expΣ' exp. revert wf.
  induction exp; intros wf; cbn -[Σ']...
  all: try now (wf_inv wf []; eauto using expanded).
  - wf_inv wf ?. eapply expanded_tRel with (args := []). eauto. lia. econstructor.
  - wf_inv wf [[[]]]. eapply expanded_tRel. eauto. len. solve_all.
  - wf_inv wf [[[]]]. econstructor. solve_all.
  - wf_inv wf []. cbn. eapply expanded_mkApps with (args := [_]); cbn... econstructor. 
    eapply expanded_tRel with (args := []). reflexivity. lia. econstructor.
  - try now (wf_inv wf [[]]; eauto using expanded).
  - wf_inv wf [[[]]].
    forward IHexp; eauto.
    eapply expanded_mkApps; eauto. 2:solve_all.
    destruct f7; cbn in *; eauto.
    destruct TransLookup.lookup_inductive as [[] | ]; cbn; eauto.
  - wf_inv wf []. eapply forall_decls_declared_constructor in H; eauto. 2: now eapply template_to_pcuic_env.
    eapply expanded_tConstruct_app with (args := []).
    eauto. cbn. unfold trans_local. now rewrite context_assumptions_map. econstructor.
  - wf_inv wf (mdecl' & idecl' & []). eapply forall_decls_declared_inductive in d; eauto. 2: now eapply template_to_pcuic_env.
    unfold Σ'.
    erewrite trans_lookup_inductive, declared_inductive_lookup; eauto.
    econstructor; eauto. cbn.
    + solve_all.
    + cbn. eapply All2_nth_hyp in a1.
      eapply All_Forall, All2_All_map2, All2_map.
      eapply Forall_All in H2. eapply All2_All_mix_right in a1; tea.
      eapply All2_impl; tea. intros x y. cbv beta. intros [[i [Hi []]] ?].
      split.
      { rewrite map_length. relativize #|Ast.pparams type_info|.
        eapply expanded_bcontext => //.
        - now eapply template_to_pcuic_env.
        - len. eapply All2_length in a2. len in a2.
        - split; tea. cbn; rewrite nth_error_map. erewrite Hi => //.
        - cbn. tea. rewrite context_assumptions_map. now rewrite e. }
      * cbn. rewrite map2_bias_left_length. now eapply e0.
    + eapply template_to_pcuic_env; eauto.
  - now (wf_inv wf [[]]; eauto using expanded).
  - wf_inv wf [[]]. wf_inv w ?. eapply expanded_tFix.
    + solve_all. revert H0. now rewrite mapi_cst_map rev_map_spec map_map.
    + solve_all.
    + destruct args; cbn; congruence.
    + now rewrite nth_error_map H5.
    + now simpl_list.
  - wf_inv wf ?. econstructor. solve_all.
  - wf_inv wf [[[]]]. eapply forall_decls_declared_constructor in H; eauto. 2: now eapply template_to_pcuic_env.
    eapply expanded_tConstruct_app. eauto. cbn. unfold trans_local. now rewrite map_length context_assumptions_map. solve_all.
Qed.