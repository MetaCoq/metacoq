(*i camlp4deps: "grammar/grammar.cma" i*)

DECLARE PLUGIN "metacoq_safechecker_plugin"

open Stdarg
open Pp
open PeanoNat.Nat
open Datatypes
open PCUICSafeChecker

let pr_char c = str (Char.escaped c)

let pr_char_list = prlist_with_sep mt pr_char

let check env evm c =
  (* if Feedback.msg_debug (str"Quoting"); *)
  let term = Ast_quoter.quote_term_rec env (EConstr.to_constr evm c) in
  (* Feedback.msg_debug (str"Finished quoting.. checking."); *)
  match SafeTemplateChecker.infer_and_print_template_program Config0.default_checker_flags term with
  | Coq_inl s ->
     Feedback.msg_info (pr_char_list s)
  | Coq_inr s -> CErrors.user_err ~hdr:"metacoq" (pr_char_list s)

VERNAC COMMAND EXTEND MetaCoqSafeCheck CLASSIFIED AS QUERY
| [ "MetaCoq" "SafeCheck" constr(c) ] -> [
    let (evm,env) = Pfedit.get_current_context () in
    let (c, _) = Constrintern.interp_constr env evm c in
    check env evm c
  ]
END

let kern_check env evm c =
  let (env,term) = Ast_id_quoter.quote_term_rec env (EConstr.to_constr evm c) in
  let _ = Kernel.Typeops.infer env term in
  Feedback.msg_info "I don't know what to do."

VERNAC COMMAND EXTEND MetaCoqUnsafeCheck CLASSIFIED AS QUERY
| [ "MetaCoq" "UnsafeCheck" constr(c) ] -> [
    let (evm,env) = Pfedit.get_current_context () in
    let (c, _) = Constrintern.interp_constr env evm c in
    kern_check env evm c
  ]
END
