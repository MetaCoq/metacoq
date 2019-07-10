(*i camlp4deps: "grammar/grammar.cma" i*)

DECLARE PLUGIN "metacoq_safechecker"

open Stdarg
open Pp
open PeanoNat.Nat
open Checker0
let pr_char c = str (Char.escaped c)

let pr_char_list = prlist_with_sep mt pr_char

let check env evm c =
  (* if Feedback.msg_debug (str"Quoting"); *)
  let term = Ast_quoter.quote_term_rec env (EConstr.to_constr evm c) in
  (* Feedback.msg_debug (str"Finished quoting.. checking."); *)
  let checker_flags = Config0.default_checker_flags in
  match SafeChecker0.typecheck_program checker_flags term with
  | CorrectDecl t ->
     Feedback.msg_info (str "Successfully checked of type: " ++ pr_char_list (Checker0.string_of_term t))
  | EnvError (AlreadyDeclared id) ->
     CErrors.user_err ~hdr:"metacoq" (str "Already declared: " ++ pr_char_list id)
  | EnvError (IllFormedDecl (id, e)) ->
     CErrors.user_err ~hdr:"metacoq" (pr_char_list (Checker0.string_of_type_error e) ++ str ", while checking " ++ pr_char_list id)

VERNAC COMMAND EXTEND MetaCoqSafeCheck CLASSIFIED AS QUERY
| [ "MetaCoq" "SafeCheck" constr(c) ] -> [
    let (evm,env) = Pfedit.get_current_context () in
    let (c, _) = Constrintern.interp_constr env evm c in
    check env evm c
  ]
END
