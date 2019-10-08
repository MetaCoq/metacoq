(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

open Ltac_plugin
open Names

DECLARE PLUGIN "template_coq"

(** Calling Ltac **)

let ltac_lcall tac args =
  let (location, name) = Loc.tag (Names.Id.of_string tac)
    (* Loc.tag @@ Names.Id.of_string tac *)
  in
  Tacexpr.TacArg(Loc.tag @@ Tacexpr.TacCall
                              (Loc.tag (Misctypes.ArgVar (CAst.make ?loc:location name),args)))

open Tacexpr
open Tacinterp
open Misctypes
open Stdarg
open Tacarg

let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optname = "Casting of propositions in template-coq";
  Goptions.optkey = ["Template";"Cast";"Propositions"];
  Goptions.optread = (fun () -> !Quoter.cast_prop);
  Goptions.optwrite = (fun a -> Quoter.cast_prop:=a);
}


let ltac_apply (f : Value.t) (args: Tacinterp.Value.t list) =
  let fold arg (i, vars, lfun) =
    let id = Names.Id.of_string ("x" ^ string_of_int i) in
    let (l,n) = (Loc.tag id) in
    let x = Reference (ArgVar (CAst.make ?loc:l n)) in
    (succ i, x :: vars, Id.Map.add id arg lfun)
  in
  let (_, args, lfun) = List.fold_right fold args (0, [], Id.Map.empty) in
  let lfun = Id.Map.add (Id.of_string "F") f lfun in
  let ist = { (Tacinterp.default_ist ()) with Tacinterp.lfun = lfun; } in
  Tacinterp.eval_tactic_ist ist (ltac_lcall "F" args)

let to_ltac_val c = Tacinterp.Value.of_constr c


let run_template_program env evm pgm =
  Run_template_monad.run_template_program_rec (fun _ -> ()) env (evm, pgm)

(** ********* Commands ********* *)

VERNAC COMMAND EXTEND Make_tests CLASSIFIED AS QUERY
    | [ "MetaCoq" "Test" "Quote" constr(def) ] ->
      [ let (evm,env) = Pfedit.get_current_context () in
        let (evm, def) = Constrintern.interp_open_constr env evm def in
        let (evm, pgm) = EConstr.fresh_global env evm (Lazy.force Template_monad.ptmTestQuote) in
        let pgm = Constr.mkApp (EConstr.to_constr evm pgm, [|Constr.mkRel 0; EConstr.to_constr evm def|]) in
        run_template_program env evm pgm ]
END;;

VERNAC COMMAND EXTEND Make_vernac CLASSIFIED AS SIDEFF
    | [ "MetaCoq" "Quote" "Definition" ident(name) ":=" constr(def) ] ->
      [ let (evm,env) = Pfedit.get_current_context () in
        let (evm, def) = Constrintern.interp_open_constr env evm def in
        let (evm, pgm) = EConstr.fresh_global env evm (Lazy.force Template_monad.ptmQuoteDefinition) in
        let pgm = Constr.mkApp (EConstr.to_constr evm pgm, [|Constr_quoter.TemplateCoqQuoter.quote_ident name; Constr.mkRel 0; EConstr.to_constr evm def|]) in
        run_template_program env evm pgm ]
END;;

VERNAC COMMAND EXTEND Make_vernac_reduce CLASSIFIED AS SIDEFF
    | [ "MetaCoq" "Quote" "Definition" ident(name) ":=" "Eval" red_expr(rd) "in" constr(def) ] ->
      [ let (evm, env) = Pfedit.get_current_context () in
        let (evm, def) = Constrintern.interp_open_constr env evm def in
        (* TODO : implem quoting of tactic reductions so that we can use ptmQuoteDefinitionRed *)
        let (evm, rd) = Tacinterp.interp_redexp env evm rd in
	let (evm, def) = Quoter.reduce env evm rd (EConstr.to_constr evm def) in
        let (evm, pgm) = EConstr.fresh_global env evm (Lazy.force Template_monad.ptmQuoteDefinition) in
        let pgm = Constr.mkApp (EConstr.to_constr evm pgm, [|Constr_quoter.TemplateCoqQuoter.quote_ident name; Constr.mkRel 0; def|]) in
        run_template_program env evm pgm ]
END;;

VERNAC COMMAND EXTEND Make_recursive CLASSIFIED AS SIDEFF
    | [ "MetaCoq" "Quote" "Recursively" "Definition" ident(name) ":=" constr(def) ] ->
      [ let (evm,env) = Pfedit.get_current_context () in
        let (evm, def) = Constrintern.interp_open_constr env evm def in
        let (evm, pgm) = EConstr.fresh_global env evm (Lazy.force Template_monad.ptmQuoteRecDefinition) in
        let pgm = Constr.mkApp (EConstr.to_constr evm pgm, [|Constr_quoter.TemplateCoqQuoter.quote_ident name; Constr.mkRel 0; EConstr.to_constr evm def|]) in
        run_template_program env evm pgm ]
END;;

VERNAC COMMAND EXTEND Unquote_vernac CLASSIFIED AS SIDEFF
    | [ "MetaCoq" "Unquote" "Definition" ident(name) ":=" constr(def) ] ->
      [ let (evm, env) = Pfedit.get_current_context () in
        let (evm, def) = Constrintern.interp_open_constr env evm def in
        let (evm, pgm) = EConstr.fresh_global env evm (Lazy.force Template_monad.ptmMkDefinition) in
        let pgm = Constr.mkApp (EConstr.to_constr evm pgm, [|Constr_quoter.TemplateCoqQuoter.quote_ident name; EConstr.to_constr evm def|]) in
        run_template_program env evm pgm ]
END;;

VERNAC COMMAND EXTEND Unquote_inductive CLASSIFIED AS SIDEFF
    | [ "MetaCoq" "Unquote" "Inductive" constr(def) ] ->
      [ let (evm, env) = Pfedit.get_current_context () in
        let (evm, def) = Constrintern.interp_open_constr env evm def in
        let (evm, pgm) = EConstr.fresh_global env evm (Lazy.force Template_monad.ptmMkInductive) in
        let pgm = Constr.mkApp (EConstr.to_constr evm pgm, [|EConstr.to_constr evm def|]) in
        run_template_program env evm pgm ]
END;;

VERNAC COMMAND EXTEND Run_program CLASSIFIED AS SIDEFF
    | [ "MetaCoq" "Run" constr(def) ] ->
      [ let (evm, env) = Pfedit.get_current_context () in
        let (evm, def) = Constrintern.interp_open_constr env evm def in
        let pgm = EConstr.to_constr evm def in
        run_template_program env evm pgm ]
END;;


(** ********* Tactics ********* *)

TACTIC EXTEND get_goal
    | [ "quote_term" constr(c) tactic(tac) ] ->
      [ (** quote the given term, pass the result to t **)
        Proofview.Goal.nf_enter begin fun gl ->
          let env = Proofview.Goal.env gl in
          let c = EConstr.to_constr (Proofview.Goal.sigma gl) c in
	  let c = Constr_quoter.TermReify.quote_term env c in
	  ltac_apply tac (List.map to_ltac_val [EConstr.of_constr c])
  end ]
END;;

TACTIC EXTEND denote_term
    | [ "denote_term" constr(c) tactic(tac) ] ->
      [ Proofview.Goal.enter (begin fun gl ->
         let evm = Proofview.Goal.sigma gl in
         let evm, c = Constr_denoter.denote_term evm (EConstr.to_constr evm c) in
         Proofview.tclTHEN (Proofview.Unsafe.tclEVARS evm)
	   (ltac_apply tac (List.map to_ltac_val [EConstr.of_constr c]))
      end) ]
END;;

TACTIC EXTEND run_program
    | [ "run_template_program" constr(c) tactic(tac) ] ->
      [ Proofview.Goal.enter (begin fun gl ->
         let env = Proofview.Goal.env gl in
         let evm = Proofview.Goal.sigma gl in
         let ret = ref None in
         Run_template_monad.run_template_program_rec ~intactic:true (fun x -> ret := Some x) env (evm, EConstr.to_constr evm c);
         match !ret with
           Some (env, evm, t) ->
            Proofview.tclTHEN
              (Proofview.Unsafe.tclEVARS evm) 
              (ltac_apply tac (List.map to_ltac_val [EConstr.of_constr t]))
         | None -> Proofview.tclUNIT ()
       end) ]
END;;

VERNAC COMMAND EXTEND Make_tests CLASSIFIED AS QUERY
    | [ "MetaCoq" "Test" "Quote" constr(c) ] ->
      [ let (evm,env) = Pfedit.get_current_context () in
	let c = Constrintern.interp_constr env evm c in
	let result = Constr_quoter.TermReify.quote_term env (EConstr.to_constr evm (fst c)) in
        Feedback.msg_notice (Tm_util.pr_constr result) ;
	() ]
END;;
