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

let retypecheck_term_dependencies env gr =
  let typecheck env c = ignore (Typeops.infer env c) in
  let typecheck_constant c =
    let auctx = Environ.constant_context env c in
    let fakeinst = Univ.AUContext.instance auctx in
    let cu = (c, fakeinst) in
    let cbody, ctype, cstrs = Environ.constant_value_and_type env cu in
    let env' = Environ.push_context (Univ.UContext.make (fakeinst, cstrs)) env in
    typecheck env' ctype;
    Option.iter (typecheck env') cbody
  in
  let st = Conv_oracle.get_transp_state (Environ.oracle (Global.env())) in
  let deps = Assumptions.assumptions ~add_opaque:true ~add_transparent:true
      st gr (Globnames.printable_constr_of_global gr) in
  let process_object k _ty =
    let open Printer in
    match k with
    | Variable id -> Feedback.msg_debug (str "Ignoring variable " ++ Names.Id.print id)
    | Axiom (ax, _) ->
      begin match ax with
        | Constant c -> typecheck_constant c
        | Positive mi -> () (* typecheck_inductive mi *)
        | Guarded c -> typecheck_constant c
      end
    | Opaque c | Transparent c -> typecheck_constant c
  in Printer.ContextObjectMap.iter process_object deps

let kern_check env evm gr =
  try
    let () = retypecheck_term_dependencies env gr in
    Feedback.msg_info (Printer.pr_global gr ++ str " and all its dependencies are well-typed.")
  with e -> raise e

VERNAC COMMAND EXTEND MetaCoqCoqCheck CLASSIFIED AS QUERY
| [ "MetaCoq" "CoqCheck" global(c) ] -> [
    let (evm,env) = Pfedit.get_current_context () in
    kern_check env evm (Nametab.global c)
  ]
END
