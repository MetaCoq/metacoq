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

Lemma trans_expanded {cf : checker_flags} {Σ} {wfΣ : Template.Typing.wf Σ} T :
  let Σ' := trans_global_env Σ in
  WfAst.wf Σ T ->
  EtaExpand.expanded Σ T ->
  expanded Σ' (trans Σ' T).
Proof with eauto using expanded.
  intros Σ' wf exp. revert wf.
  induction exp; intros wf; cbn -[Σ']...
  all: try now (wf_inv wf []; eauto using expanded).
  all: try now (wf_inv wf [[]]; eauto using expanded).
  - wf_inv wf ?. econstructor; eauto. solve_all.
  - wf_inv wf []. eapply expanded_mkApps with (args := [_]); cbn...
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
    econstructor; eauto. cbn. induction a1; cbn; econstructor.
    + cbn. inversion H0; subst. eapply H3. eapply r.
    + inversion H0; subst. inversion H; subst. eapply IHa1; eauto.
    + eapply template_to_pcuic_env; eauto.
  - wf_inv wf [[]]. wf_inv w ?. eapply expanded_tFix.
    + solve_all.
    + solve_all.
    + destruct args; cbn; congruence.
    + now rewrite nth_error_map H4.
    + now simpl_list.
  - wf_inv wf ?. econstructor. solve_all.
  - wf_inv wf [[[]]]. eapply forall_decls_declared_constructor in H; eauto. 2: now eapply template_to_pcuic_env.
    eapply expanded_tConstruct_app. eauto. cbn. unfold trans_local. now rewrite map_length context_assumptions_map. solve_all.
Qed.