open Pp

let contrib_name = "template-coq"

let gen_constant_in_modules locstr dirs s =
  lazy (Universes.constr_of_global (Coqlib.gen_reference_in_modules locstr dirs s))


let opt_debug = ref false

let debug (m : unit ->Pp.t) =
  if !opt_debug then
    Feedback.(msg_debug (m ()))
  else
    ()

let rec app_full trm acc =
  match Constr.kind trm with
    Constr.App (f, xs) -> app_full f (Array.to_list xs @ acc)
  | _ -> (trm, acc)

let pr_constr trm =
  let (evm, env) = Pfedit.get_current_context () in
  Printer.pr_constr_env env evm trm

let not_supported trm =
  CErrors.user_err (str "Not Supported:" ++ spc () ++ pr_constr trm)

let not_supported_verb trm rs =
  CErrors.user_err (str "Not Supported raised at " ++ str rs ++ str ":" ++ spc () ++ pr_constr trm)

let bad_term trm =
  CErrors.user_err (str "Bad term:" ++ spc () ++ pr_constr trm)

let bad_term_verb trm rs =
  CErrors.user_err (str "Bad term:" ++ spc () ++ pr_constr trm
                    ++ spc () ++ str " Error: " ++ str rs)
