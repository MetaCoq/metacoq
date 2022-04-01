(** * Definition of programs in template-coq, well-typed terms and provided transformations **)

From MetaCoq.Template Require Import
        utils
        Ast           (* The term AST *)
        Typing        (* Typing judgment *)
        config        (* Typing configuration *)
        Transform
        WcbvEval
        EtaExpand.

Import Transform.

Definition template_program := Ast.Env.program.

(** Well-typedness of template programs *)

Definition wt_template_program {cf : checker_flags} (p : template_program) :=
  let Σ := Ast.Env.empty_ext p.1 in
  wf_ext Σ × ∑ T, Σ ;;; [] |- p.2 : T.

(** Evaluation relation on template programs *)

Definition eval_template_program (p : Ast.Env.program) (v : Ast.term) :=
  ∥ WcbvEval.eval p.1 p.2 v ∥.

(* Eta-expansion *)

Definition template_expand_obseq (p p' : template_program) (v v' : Ast.term) :=
  v' = EtaExpand.eta_expand p.1.(Ast.Env.declarations) [] v.
  
Local Obligation Tactic := idtac.

Program Definition template_eta_expand {cf : checker_flags} : self_transform template_program Ast.term eval_template_program eval_template_program :=
 {| name := "eta-expansion of template program";
    pre p := ∥ wt_template_program p ∥;
    transform p _ := EtaExpand.eta_expand_program p;
    post p := ∥ wt_template_program p ∥ /\ EtaExpand.expanded_program p;
    obseq := template_expand_obseq |}.
Next Obligation.
  intros cf [Σ t] [[wfext ht]].
  cbn. split. split. todo "eta-expansion preserves wf ext and typing".
  red.
  destruct ht as [T ht].
  split; cbn. eapply EtaExpand.eta_expand_global_env_expanded. apply wfext.
  eapply EtaExpand.expanded_env_irrel.
  epose proof (EtaExpand.eta_expand_expanded (Σ := Ast.Env.empty_ext Σ) [] [] t T).
  forward H. apply wfext. specialize (H ht).
  forward H by constructor. cbn in H.
  destruct Σ; cbn in *. exact H.
Qed.
Next Obligation.
  red. intros cf [Σ t] v [[]].
  unfold eval_template_program.
  cbn. intros ev.
  exists (EtaExpand.eta_expand (Ast.Env.declarations Σ) [] v). split. split.
  todo "eta-expansion preserves evaluation".
  red. reflexivity.
Qed.
