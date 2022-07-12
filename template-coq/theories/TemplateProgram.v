(** * Definition of programs in template-coq, well-typed terms and provided transformations **)

From MetaCoq.Template Require Import
        utils
        Ast           (* The term AST *)
        Typing        (* Typing judgment *)
        config        (* Typing configuration *)
        WcbvEval.

Definition template_program := Ast.Env.program.

(** Well-typedness of template programs *)

Definition wt_template_program {cf : checker_flags} (p : template_program) :=
  let Σ := Ast.Env.empty_ext p.1 in
  wf_ext Σ × ∑ T, Σ ;;; [] |- p.2 : T.

(** Evaluation relation on template programs *)

Definition eval_template_program (p : Ast.Env.program) (v : Ast.term) :=
  ∥ WcbvEval.eval p.1 p.2 v ∥.

