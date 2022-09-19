(** * Definition of programs in template-coq, well-typed terms and provided transformations **)

From MetaCoq.Template Require Import
        utils
        Transform
        Ast           (* The term AST *)
        Typing        (* Typing judgment *)
        config        (* Typing configuration *)
        WcbvEval
        TemplateEnvMap.

Definition template_program := Ast.Env.program.

Definition template_program_env := (TemplateEnvMap.GlobalEnvMap.t * Ast.term).

(** Well-typedness of template programs *)

Definition wt_template_program {cf : checker_flags} (p : template_program) :=
  let Σ := Ast.Env.empty_ext p.1 in
  wf_ext Σ × ∑ T, Σ ;;; [] |- p.2 : T.

(** Evaluation relation on template programs *)

Definition eval_template_program (p : Ast.Env.program) (v : Ast.term) :=
  ∥ WcbvEval.eval p.1 p.2 v ∥.

(** Well-typedness of template programs with efficient environments *)

Definition wt_template_program_env {cf : checker_flags} (p : template_program_env) :=
  let Σ := Ast.Env.empty_ext p.1 in
  wf_ext Σ × ∑ T, Σ ;;; [] |- p.2 : T.

(** Evaluation relation on template programs *)

Definition eval_template_program_env (p : template_program_env) (v : Ast.term) :=
  ∥ WcbvEval.eval p.1 p.2 v ∥.

Import Transform.

Lemma wt_template_program_fresh {cf : checker_flags} p : ∥ wt_template_program p ∥ -> EnvMap.EnvMap.fresh_globals (declarations p.1).
Proof. intros [[wfΣ _]]. eapply TemplateEnvMap.wf_fresh_globals, wfΣ. Qed.

Definition make_template_program_env {cf : checker_flags} (p : template_program) (wtp : ∥ wt_template_program p ∥) : template_program_env :=
  (GlobalEnvMap.make p.1 (wt_template_program_fresh p wtp), p.2).

Program Definition build_template_program_env {cf : checker_flags} :
  Transform.t template_program template_program_env Ast.term Ast.term eval_template_program eval_template_program_env :=
  {| name := "rebuilding environment lookup table";
     pre p := ∥ wt_template_program p ∥ ;
     transform p pre := make_template_program_env p pre;
     post p := ∥ wt_template_program_env p ∥;
     obseq g g' v v' := v = v' |}.
Next Obligation.
  cbn. exists v. cbn; split; auto.
Qed.
