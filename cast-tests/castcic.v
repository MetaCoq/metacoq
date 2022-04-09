From MetaCoq.Template Require Import TemplateMonad config utils Loader.
From MetaCoq.PCUIC Require Import PCUICAst PCUICToTemplate PCUICPretty PCUICSN PCUICTyping PCUICNormal.
From MetaCoq.SafeChecker Require Import PCUICErrors SafeTemplateChecker PCUICWfEnvImpl PCUICWfEnv PCUICSafeChecker PCUICSafeReduce.
Import MCMonadNotation.

Global Existing Instance PCUICSN.default_normalizing.

Check typecheck_program.
Check PCUICSafeReduce.hnf.
Check check_wf_type.

Axiom unk : forall (A : Type), A.
Axiom castcic_err : forall (A : Type), A.
Axiom castcic_cast : forall (A B : Type), A -> B.

Notation err := castcic_err.
Notation cast := castcic_cast.

Program Definition eval_compute_cheat (cf := default_checker_flags)
  {nor : normalizing_flags}
  (p : Ast.Env.program) φ : Ast.term
  := let p' := trans_program p in
    let tm := reduce_term RedFlags.default
    canonical_abstract_env_ext_impl
    {| referenced_impl_env_ext  := (p'.1 , φ);
       referenced_impl_ext_wf  := (todo "wf") |}
    [] p'.2 (todo "welltyped") in
    PCUICToTemplate.trans tm.

MetaCoq Quote Recursively Definition foo := (1 + pred (1 + (unk nat))).
Definition foo' := Eval lazy in eval_compute_cheat foo Monomorphic_ctx.
MetaCoq Unquote Definition foo'' := foo'.
Print foo''.