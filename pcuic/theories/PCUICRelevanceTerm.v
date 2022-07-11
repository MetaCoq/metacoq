From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICRelevance PCUICInduction PCUICCases PCUICSigmaCalculus PCUICLiftSubst PCUICWeakeningEnv.

Require Import ssreflect.
From Equations Require Import Equations.


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

Lemma mark_fix_context f g mfix :
  marks_of_context (fix_context (map (map_def f g) mfix)) = marks_of_context (fix_context mfix).
Proof.
  rewrite /fix_context /marks_of_context !mapi_map !map_rev !map_mapi //.
Qed.

Lemma marks_of_context_univ_subst Γ u : marks_of_context Γ@[u] = marks_of_context Γ.
Proof.
  rewrite /marks_of_context /subst_instance /subst_instance_context /map_context map_map //=.
Qed.

Lemma extends_isTermRelOpt {cf : checker_flags} {Pcmp P} Σ Σ' Γ t relopt :
  on_global_env Pcmp P Σ' ->
  extends Σ Σ' ->
  PCUICEnvTyping.isTermRelOpt Σ Γ t relopt ->
  PCUICEnvTyping.isTermRelOpt Σ' Γ t relopt.
Proof.
  destruct relopt => //=.
  induction t in Γ |- * using term_forall_list_ind;
    intros wfΣ' ext Hirr; depelim Hirr; try econstructor; eauto with extends.
Qed.

#[global] Hint Resolve extends_isTermRelOpt : extends.

