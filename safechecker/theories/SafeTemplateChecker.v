(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program.
From MetaCoq.Template Require Import config utils.
From MetaCoq.Template Require AstUtils Typing.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping
     TemplateToPCUIC PCUICSN BDToPCUIC PCUICProgram.
From MetaCoq.SafeChecker Require Import PCUICErrors PCUICSafeChecker PCUICWfEnv PCUICWfEnvImpl.

Import MCMonadNotation.

Definition trans_program (p : Ast.Env.program) : program := 
  let Σ' := trans_global_env p.1 in
  (Σ', trans Σ' p.2).

Program Definition infer_template_program {cf : checker_flags} {nor : normalizing_flags} (p : Ast.Env.program) φ
  : EnvCheck wf_env_ext (let p' := trans_program p in ∑ A, ∥ (p'.1, φ) ;;; [] |- p'.2 : A ∥) :=
  p <- typecheck_program optimized_abstract_env_impl (trans_program p) φ ;;
  ret (p.π1 ; _).
Next Obligation.
  sq. destruct X. eapply infering_typing; tea. eapply w. constructor.
Qed.

Program Definition infer_and_print_template_program {cf : checker_flags} {nor : normalizing_flags} (p : Ast.Env.program) φ
  : string + string :=
  match infer_template_program (cf:=cf) p φ return string + string with
  | CorrectDecl t =>
    let Σ' := trans_global_env p.1 in
    inl ("Environment is well-formed and " ^ string_of_term (trans Σ' p.2) ^
         " has type: " ^ string_of_term t.π1)
  | EnvError Σ (AlreadyDeclared id) =>
    inr ("Already declared: " ^ id)
  | EnvError Σ (IllFormedDecl id e) =>
    inr ("Type error: " ^ string_of_type_error Σ e ^ ", while checking " ^ id)
  end.

(* Program Definition check_template_program {cf : checker_flags} (p : Ast.Env.program) (ty : Ast.Env.term) *)
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

(* Program Definition typecheck_template_program' {cf : checker_flags} (p : Ast.Env.program) *)
(*   : EnvCheck (∑ A, ∥ Typing.typing (AstUtils.empty_ext (List.rev p.1)) [] p.2 A ∥) := *)
(*   p <- typecheck_template_program (cf:=cf) p ;; *)
(*   ret (Monad:=envcheck_monad) (p.π1 ; _). *)
