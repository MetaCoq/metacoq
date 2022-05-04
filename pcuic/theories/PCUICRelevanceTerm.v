From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICRelevance PCUICInduction PCUICCases PCUICSigmaCalculus PCUICLiftSubst PCUICWeakeningEnv.

Require Import ssreflect.


Lemma mark_inst_case_context params puinst (pctx : context) :
  marks_of_context (inst_case_context params puinst pctx) = marks_of_context pctx.
Proof.
  unfold marks_of_context, inst_case_context, subst_context, subst_instance, subst_instance_context, map_context.
  rewrite -map_map map_decl_name_fold_context_k !map_map. now cbn.
Qed.

Lemma mark_inst_case_predicate_context p :
  marks_of_context (inst_case_predicate_context p) = marks_of_context p.(pcontext).
Proof. apply mark_inst_case_context. Qed.

Lemma mark_inst_case_branch_context p br :
  marks_of_context (inst_case_branch_context p br) = marks_of_context br.(bcontext).
Proof. apply mark_inst_case_context. Qed.

Lemma extends_irrelevant {cf : checker_flags} {Pcmp P} Σ Σ' Γ t :
  on_global_env Pcmp P Σ' ->
  extends Σ Σ' ->
  isTermRel Σ Γ t Irrelevant ->
  isTermRel Σ' Γ t Irrelevant.
Proof.
  induction t in Γ |- * using term_forall_list_ind;
    cbn; intros ext Hirr; auto.
  - unfold relevance_of_constant.
    destruct lookup_constant eqn:H => //.
    erewrite extends_lookup_constant; eauto.
  - unfold relevance_of_constructor.
    destruct lookup_inductive eqn:H => //.
    erewrite extends_lookup_inductive; eauto.
  - unfold relevance_of_projection.
    destruct lookup_projection eqn:H => //.
    erewrite extends_lookup_projection; eauto.
Qed.

