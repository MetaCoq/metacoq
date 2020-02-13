open Pp

let contrib_name = "template-coq"

let gen_constant_in_modules s =
  lazy (
    let tm_ref = Coqlib.lib_ref s in
    UnivGen.constr_of_monomorphic_global tm_ref
  )
  (* lazy (Universes.constr_of_global (Coqlib.gen_reference_in_modules locstr dirs s)) *)


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

let not_supported trm =
  let env = Global.env () in
  CErrors.user_err (str "Not Supported:" ++ spc () ++ Printer.pr_constr_env env (Evd.from_env env) trm)

let not_supported_verb trm rs =
  let env = Global.env () in
  CErrors.user_err (str "Not Supported raised at " ++ str rs ++ str ":" ++ spc () ++ 
    Printer.pr_constr_env env (Evd.from_env env) trm)

let bad_term trm =
  let env = Global.env () in
  CErrors.user_err (str "Bad term:" ++ spc () ++ Printer.pr_constr_env env (Evd.from_env env) trm)

let bad_term_verb trm rs =
  let env = Global.env () in
  CErrors.user_err (str "Bad term:" ++ spc () ++ Printer.pr_constr_env env (Evd.from_env env) trm
                    ++ spc () ++ str " Error: " ++ str rs)
