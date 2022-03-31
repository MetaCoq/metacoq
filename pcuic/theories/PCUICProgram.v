(** * Definition of programs in template-coq, well-typed terms and provided transformations **)
From Coq Require Import ssreflect.
From MetaCoq.Template Require Import
        utils
        Ast           (* The term AST *)
        Typing        (* Typing judgment *)
        config        (* Typing configuration *)
        Transform        
        TemplateProgram.

From MetaCoq.PCUIC Require Import PCUICAstUtils PCUICAst TemplateToPCUIC
    TemplateToPCUICWcbvEval
    TemplateToPCUICCorrectness 
    TemplateToPCUICExpanded
    PCUICGlobalEnv PCUICTyping PCUICEtaExpand.

Import Transform.

(** * Translation from Template to PCUIC, directly preserves evaluation *)

Definition eval_pcuic_program (p : pcuic_program) (v : term) :=
  ∥ PCUICWcbvEval.eval p.1.(trans_env_env) p.2 v ∥.
      
Definition template_to_pcuic_obseq (p : Ast.Env.program) (p' : pcuic_program) (v : Ast.term) (v' : term) :=
  let Σ := Ast.Env.empty_ext p.1 in v' = trans (trans_global Σ) v.

Lemma trans_template_program_wt {cf : checker_flags} p (wtp : wt_template_program p) : wt_pcuic_program (trans_template_program p).
Proof.
  move: p wtp.
  intros [Σ t] [wfext ht].
  unfold wt_pcuic_program, trans_template_program; cbn in *.
  cbn. split. eapply template_to_pcuic_env_ext in wfext. apply wfext.
  destruct ht as [T HT]. exists (trans (trans_global_env Σ) T).
  eapply (template_to_pcuic_typing (Σ := Ast.Env.empty_ext Σ) []). apply wfext.
  apply HT.
Qed.

Program Definition template_to_pcuic_transform {cf : checker_flags} : 
  Transform.t template_program pcuic_program Ast.term term 
  eval_template_program eval_pcuic_program :=
 {| name := "template to pcuic";
    pre p := ∥ wt_template_program p ∥ /\ EtaExpand.expanded_program p ;
    transform p _ := trans_template_program p ;
    post p := ∥ wt_pcuic_program p ∥ /\ PCUICEtaExpand.expanded_pcuic_program p;
    obseq := template_to_pcuic_obseq |}.
Next Obligation.
  cbn. intros cf p [[wtp] etap].
  split; [split|].
  now eapply trans_template_program_wt.
  now eapply expanded_trans_program in etap.
Qed.
Next Obligation.
  red. intros cf [Σ t] v [[]].
  unfold eval_pcuic_program, eval_template_program.
  cbn. intros [ev].
  unshelve eapply TemplateToPCUICWcbvEval.trans_wcbvEval in ev; eauto. apply X.
  eexists; split; split; eauto.
  eapply template_to_pcuic_env.
  apply X. destruct X as [wfΣ [T HT]]. apply TypingWf.typing_wf in HT. apply HT. auto.
Qed.

From MetaCoq.PCUIC Require Import PCUICExpandLets PCUICExpandLetsCorrectness.

(** Expansion of let bindings in constructor types / case branches. 
    Direcly preserves evaluation as well: the new value is simply the 
    expansion of the old one, which is the identiy on normal forms.
*)

Program Definition build_global_env_map (g : global_env) : global_env_map := 
  {| trans_env_env := g; 
     trans_env_map := EnvMap.EnvMap.of_global_env g.(declarations) |}.
Next Obligation.
  intros g. eapply EnvMap.EnvMap.repr_global_env.
Qed.

Definition let_expansion_obseq (p : pcuic_program) (p' : pcuic_program) (v : term) (v' : term) :=
  v' = PCUICExpandLets.trans v.

Definition expand_lets_program (p : pcuic_program) : pcuic_program :=
  let Σ' := PCUICExpandLets.trans_global p.1 in 
  ((build_global_env_map Σ', p.1.2), PCUICExpandLets.trans p.2).
    
Lemma expanded_expand_lets_program {cf : checker_flags} p (wtp : wt_pcuic_program p) :
  expanded_pcuic_program p ->
  expanded_pcuic_program (expand_lets_program p).
Proof.
  destruct p as [[Σ udecl] t]; intros [etaenv etat].
  destruct wtp as [wfΣ wtp].
  cbn in *. split; cbn.
  now eapply (expanded_global_env_expand_lets (cf:=cf) (Σ, udecl)). 
  cbn in *.
  now eapply expanded_expand_lets in etat.
Qed.

Program Definition pcuic_expand_lets_transform {cf : checker_flags} : 
  self_transform pcuic_program term eval_pcuic_program eval_pcuic_program :=
 {| name := "let expansion in branches/constructors";
    pre p := ∥ wt_pcuic_program p ∥ /\ PCUICEtaExpand.expanded_pcuic_program p ;
    transform p hp := expand_lets_program p;
    post p := ∥ wt_pcuic_program (cf:=PCUICExpandLetsCorrectness.cf' cf) p ∥ /\ PCUICEtaExpand.expanded_pcuic_program p;
    obseq := let_expansion_obseq |}.
Next Obligation.
  intros cf [Σ t] [[[wfext ht]] etap].
  cbn. split. sq. unfold build_global_env_map. unfold global_env_ext_map_global_env_ext. simpl.
  split. eapply PCUICExpandLetsCorrectness.trans_wf_ext in wfext. apply wfext.
  destruct ht as [T HT]. exists (PCUICExpandLets.trans T).
  eapply (PCUICExpandLetsCorrectness.pcuic_expand_lets Σ []) => //.
  apply wfext. apply PCUICExpandLetsCorrectness.trans_wf_ext in wfext. apply wfext.
  now eapply expanded_expand_lets_program.
Qed.
Next Obligation.
  red. intros cf [Σ t] v [[]].
  unfold eval_pcuic_program.
  cbn. intros [ev]. destruct X.
  eapply (PCUICExpandLetsCorrectness.trans_wcbveval (Σ:=global_env_ext_map_global_env_ext Σ)) in ev.
  eexists; split; split; eauto.
  destruct s as [T HT]. now apply PCUICClosedTyp.subject_closed in HT.
Qed.