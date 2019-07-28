(*i camlp4deps: "grammar/grammar.cma" i*)

DECLARE PLUGIN "metacoq_checker"

open Stdarg
open Pp
open PeanoNat.Nat
open Checker0
let pr_char c = str (Char.escaped c)

let pr_char_list = prlist_with_sep mt pr_char

let check env evm c =
  (* Feedback.msg_debug (str"Quoting"); *)
  let term = Ast_quoter.quote_term_rec env (EConstr.to_constr evm c) in
  (* Feedback.msg_debug (str"Finished quoting.. checking."); *)
  let fuel = pow two (pow two (pow two two)) in
  let checker_flags = Config0.default_checker_flags in
  match Checker0.typecheck_program checker_flags fuel term with
  | CorrectDecl t ->
     Feedback.msg_info (str "Successfully checked of type: " ++ pr_char_list (AstUtils.string_of_term t))
  | EnvError (AlreadyDeclared id) ->
     CErrors.user_err ~hdr:"metacoq" (str "Already declared: " ++ pr_char_list id)
  | EnvError (IllFormedDecl (id, e)) ->
     CErrors.user_err ~hdr:"metacoq" (pr_char_list (Checker0.string_of_type_error e) ++ str ", while checking " ++ pr_char_list id)

VERNAC COMMAND EXTEND MetaCoqCheck CLASSIFIED AS QUERY
| [ "MetaCoq" "Check" constr(c) ] -> [
    let (evm,env) = Pfedit.get_current_context () in
    let (c, _) = Constrintern.interp_constr env evm c in
    check env evm c
  ]
END
