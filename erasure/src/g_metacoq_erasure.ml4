(*i camlp4deps: "grammar/grammar.cma" i*)

DECLARE PLUGIN "metacoq_erasure_plugin"

open Stdarg
open Pp
open PeanoNat.Nat
open Datatypes
open PCUICSafeChecker

let pr_char c = str (Char.escaped c)

let rec seq_of_list = function
  | [] -> Seq.empty
  | c :: cs -> fun () -> Seq.Cons (c, seq_of_list cs)

let pr_char_list l =
  (* We allow utf8 encoding *)
  str (Bytes.to_string (Bytes.of_seq (seq_of_list l)))

let check env evm c =
  (* if Feedback.msg_debug (str"Quoting"); *)
  let term = Ast_quoter.quote_term_rec env (EConstr.to_constr evm c) in
  (* Feedback.msg_debug (str"Finished quoting.. checking."); *)
  let checker_flags = Config0.default_checker_flags in
  match SafeTemplateErasure.erase_and_print_template_program checker_flags term with
  | Coq_inl s -> Feedback.msg_info (pr_char_list s)
  | Coq_inr s -> CErrors.user_err ~hdr:"metacoq" (pr_char_list s)

VERNAC COMMAND EXTEND MetaCoqErase CLASSIFIED AS QUERY
| [ "MetaCoq" "Erase" constr(c) ] -> [
    let (evm,env) = Pfedit.get_current_context () in
    let (c, _) = Constrintern.interp_constr env evm c in
    check env evm c
  ]
END
