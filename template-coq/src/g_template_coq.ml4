(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

open Ltac_plugin
open Entries
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
         let env = Proofview.Goal.env gl in
         let evm = Proofview.Goal.sigma gl in
         let evdref = ref evm in
         let c = Denote.denote_term evdref (EConstr.to_constr evm c) in
         (* TODO : not the right way of retype things *)
         let def' = Constrextern.extern_constr true env !evdref (EConstr.of_constr c) in
         let def = Constrintern.interp_constr env !evdref def' in
         Proofview.tclTHEN (Proofview.Unsafe.tclEVARS !evdref)
	   (ltac_apply tac (List.map to_ltac_val [fst def]))
      end) ]
END;;


VERNAC COMMAND EXTEND Make_vernac CLASSIFIED AS SIDEFF
    | [ "Quote" "Definition" ident(name) ":=" constr(def) ] ->
      [ let (evm,env) = Pfedit.get_current_context () in
	let def,uctx = Constrintern.interp_constr env evm def in
	let trm = Constr_quoter.TermReify.quote_term env (EConstr.to_constr evm def) in
	ignore(Declare.declare_definition
                 ~kind:Decl_kinds.Definition name
                 (trm, Monomorphic_const_entry (UState.context_set uctx))) ]
END;;

VERNAC COMMAND EXTEND Make_vernac_reduce CLASSIFIED AS SIDEFF
    | [ "Quote" "Definition" ident(name) ":=" "Eval" red_expr(rd) "in" constr(def) ] ->
      [ let (evm,env) = Pfedit.get_current_context () in
	let def, uctx = Constrintern.interp_constr env evm def in
        let evm = Evd.from_ctx uctx in
        let (evm,rd) = Tacinterp.interp_redexp env evm rd in
	let (evm,def) = Quoter.reduce env evm rd (EConstr.to_constr evm def) in
	let trm = Constr_quoter.TermReify.quote_term env def in
	ignore(Declare.declare_definition
                 ~kind:Decl_kinds.Definition
                 name
                 (trm, Monomorphic_const_entry (Evd.universe_context_set evm))) ]
END;;

VERNAC COMMAND EXTEND Make_recursive CLASSIFIED AS SIDEFF
    | [ "Quote" "Recursively" "Definition" ident(name) ":=" constr(def) ] ->
      [ let (evm,env) = Pfedit.get_current_context () in
	let def, uctx = Constrintern.interp_constr env evm def in
	let trm = Constr_quoter.TermReify.quote_term_rec env (EConstr.to_constr evm def) in
	ignore(Declare.declare_definition
	  ~kind:Decl_kinds.Definition name
	  (trm, Monomorphic_const_entry (UState.context_set uctx))) ]
END;;

VERNAC COMMAND EXTEND Unquote_vernac CLASSIFIED AS SIDEFF
    | [ "Make" "Definition" ident(name) ":=" constr(def) ] ->
      [ let (evm, env) = Pfedit.get_current_context () in
	let (trm, uctx) = Constrintern.interp_constr env evm def in
        let evdref = ref (Evd.from_ctx uctx) in
	let trm = Denote.denote_term evdref (EConstr.to_constr evm trm) in
	let _ = Declare.declare_definition
                  ~kind:Decl_kinds.Definition
                  name
                  (trm, Monomorphic_const_entry (Evd.universe_context_set !evdref)) in
        () ]
END;;

VERNAC COMMAND EXTEND Unquote_vernac_red CLASSIFIED AS SIDEFF
    | [ "Make" "Definition" ident(name) ":=" "Eval" red_expr(rd) "in" constr(def) ] ->
      [ let (evm, env) = Pfedit.get_current_context () in
	let (trm, uctx) = Constrintern.interp_constr env evm def in
        let evm = Evd.from_ctx uctx in
        let (evm,rd) = Tacinterp.interp_redexp env evm rd in
	let (evm,trm) = Quoter.reduce env evm rd (EConstr.to_constr evm trm) in
        let evdref = ref evm in
        let trm = Denote.denote_term evdref trm in
	let _ = Declare.declare_definition ~kind:Decl_kinds.Definition name
                  (trm, Monomorphic_const_entry (Evd.universe_context_set !evdref)) in
        () ]
END;;

VERNAC COMMAND EXTEND Unquote_inductive CLASSIFIED AS SIDEFF
    | [ "Make" "Inductive" constr(def) ] ->
      [ let (evm,env) = Pfedit.get_current_context () in
	let (body,uctx) = Constrintern.interp_constr env evm def in
        Denote.declare_inductive env evm (EConstr.to_constr evm body) ]
END;;

VERNAC COMMAND EXTEND Run_program CLASSIFIED AS SIDEFF
    | [ "Run" "TemplateProgram" constr(def) ] ->
      [ let (evm, env) = Pfedit.get_current_context () in
        let (def, _) = Constrintern.interp_constr env evm def in
        (* todo : uctx ? *)
        Denote.run_template_program_rec (fun _ -> ()) (Global.env ()) (evm, (EConstr.to_constr evm def)) ]
END;;

TACTIC EXTEND run_program
    | [ "run_template_program" constr(c) tactic(tac) ] ->
      [ Proofview.Goal.enter (begin fun gl ->
         let evm = Proofview.Goal.sigma gl in
         let env = Proofview.Goal.env gl in
         let ret = ref None in
         Denote.run_template_program_rec ~intactic:true (fun (evm, t) -> ret := Some t) env (evm, EConstr.to_constr evm c);
         match !ret with
           Some c ->
           ltac_apply tac (List.map to_ltac_val [EConstr.of_constr c])
         | None -> Proofview.tclUNIT ()
       end) ]
END;;

VERNAC COMMAND EXTEND Make_tests CLASSIFIED AS QUERY
    | [ "Test" "Quote" constr(c) ] ->
      [ let (evm,env) = Pfedit.get_current_context () in
	let c = Constrintern.interp_constr env evm c in
	let result = Constr_quoter.TermReify.quote_term env (EConstr.to_constr evm (fst c)) in
        Feedback.msg_notice (Quoter.pr_constr result) ;
	() ]
END;;
