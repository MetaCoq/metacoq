(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaCoq.Template Require Import config monad_utils utils BasicAst AstUtils
     UnivSubst.
From MetaCoq.Checker Require Import uGraph Typing.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICNormal PCUICSR
     PCUICGeneration PCUICReflect PCUICEquality PCUICInversion PCUICValidity
     PCUICWeakening PCUICPosition PCUICCumulativity PCUICSafeLemmata PCUICSN TemplateToPCUIC.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICSafeConversion PCUICSafeChecker SafeTemplateChecker.
From MetaCoq.Erasure Require Import ErasureFunction.

Import MonadNotation.

Existing Instance envcheck_monad.

Program Definition erase_template_program (p : Ast.program)
  : EnvCheck Prelim.E.term :=
  let Σ := List.rev (trans_global (AstUtils.empty_ext p.1)).1 in
  G <- check_wf_env Σ ;;
  t <- wrap_error ("During erasure of " ++ string_of_term (trans p.2)) (erase (empty_ext Σ) _ nil _ (trans p.2));;
  ret (Monad:=envcheck_monad) t.

Next Obligation.
  unfold trans_global.
  simpl. unfold wf_ext, empty_ext. simpl.
  unfold on_global_env_ext. destruct H0. constructor.
  split; auto. simpl. todo "on_udecl on empty universe context"%string.
Qed.

Next Obligation.
  unfold trans_global.
  simpl. unfold wf_ext, empty_ext. simpl.
  unfold on_global_env_ext. destruct H0. constructor.
  auto.
Qed.

Local Open Scope string_scope.

Program Definition erase_and_print_template_program {cf : checker_flags} (p : Ast.program)
  : string + string :=
  match erase_template_program p return string + string with
  | CorrectDecl t =>
    inl ("Environment is well-formed and " ++ string_of_term (trans p.2) ++
         " has type: " ++ string_of_eterm t.π1)
  | EnvError (AlreadyDeclared id) =>
    inr ("Already declared: " ++ id)
  | EnvError (IllFormedDecl id e) =>
    inr ("Type error: " ++ PCUICSafeChecker.string_of_type_error e ++ ", while checking " ++ id)
  end.

(* Program Definition check_template_program {cf : checker_flags} (p : Ast.program) (ty : Ast.term) *)
(*   : EnvCheck (∥ trans_global (AstUtils.empty_ext (List.rev p.1)) ;;; [] |- trans p.2 : trans ty ∥) := *)
(*   p <- typecheck_program (cf:=cf) ((trans_global (AstUtils.empty_ext p.1)).1, trans p.2) ;; *)
(*   wrap_error "During checking of type constraints" (check p.1 _ _ _ (trans ty));; *)
(*   ret (Monad:=envcheck_monad) _. *)

(* Next Obligation. *)
(*   unfold trans_global. *)
(*   simpl. unfold empty_ext in X. *)
(*   unfold trans_global_decls in X. *)
(*   rewrite <-map_rev in X. *)
(* Qed. *)

(* Program Definition typecheck_template_program' {cf : checker_flags} (p : Ast.program) *)
(*   : EnvCheck (∑ A, ∥ Typing.typing (AstUtils.empty_ext (List.rev p.1)) [] p.2 A ∥) := *)
(*   p <- typecheck_template_program (cf:=cf) p ;; *)
(*   ret (Monad:=envcheck_monad) (p.π1 ; _). *)
