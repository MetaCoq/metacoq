let __coq_plugin_name = "template_coq"
let _ = Mltop.add_known_module __coq_plugin_name

# 6 "src/g_template_coq.mlg"
 

open Attributes
open Ltac_plugin
open Names

(** Calling Ltac **)

let ltac_lcall tac args =
  let (location, name) = Loc.tag (Names.Id.of_string tac)
    (* Loc.tag @@ Names.Id.of_string tac *)
  in
  Tacexpr.TacArg(CAst.make ?loc:location (Tacexpr.TacCall
                              (CAst.make (Locus.ArgVar (CAst.make ?loc:location name),args))))

open Tacexpr
open Tacinterp
open Stdarg
open Tacarg
open Genredexpr

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
    let x = Reference (Locus.ArgVar (CAst.make ?loc:l n)) in
    (succ i, x :: vars, Id.Map.add id arg lfun)
  in
  let (_, args, lfun) = List.fold_right fold args (0, [], Id.Map.empty) in
  let lfun = Id.Map.add (Id.of_string "F") f lfun in
  let ist = { (Tacinterp.default_ist ()) with Tacinterp.lfun = lfun; } in
  Tacinterp.eval_tactic_ist ist (ltac_lcall "F" args)

let to_ltac_val c = Tacinterp.Value.of_constr c


let run_template_program env evm ~poly pgm =
  Run_template_monad.run_template_program_rec ~poly (fun _ -> ()) env (evm, pgm)

let fresh_env () = 
  let env = Global.env () in
  let sigma = Evd.from_env env in
  env, sigma


let () = Vernacextend.vernac_extend ~command:"TemplateCoq_Test_Quote" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Test", 
                                     Vernacextend.TyTerminal ("Quote", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNil))), (let coqpp_body def
                                                            poly ~st = 
                                                            let () = 
                                                            
# 64 "src/g_template_coq.mlg"
        let (env, evm) = fresh_env () in
        let (evm, def) = Constrintern.interp_open_constr env evm def in
        let (evm, pgm) = EConstr.fresh_global env evm (Lazy.force Template_monad.ptmTestQuote) in
        let pgm = Constr.mkApp (EConstr.to_constr evm pgm, [|Constr.mkRel 0; EConstr.to_constr evm def|]) in
        run_template_program env evm ~poly pgm 
                                                             in st in fun def
                                                            ~atts ~st
                                                            -> coqpp_body def
                                                            (Attributes.parse polymorphic atts) ~st), None))]

let () = Vernacextend.vernac_extend ~command:"TemplateCoq_Quote_Definition" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Quote", 
                                     Vernacextend.TyTerminal ("Definition", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                     Vernacextend.TyTerminal (":=", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNil))))), 
         (let coqpp_body name def poly ~st = let () = 
# 73 "src/g_template_coq.mlg"
        let (env, evm) = fresh_env () in
        let (evm, def) = Constrintern.interp_open_constr env evm def in
        let (evm, pgm) = EConstr.fresh_global env evm (Lazy.force Template_monad.ptmQuoteDefinition) in
        let pgm = Constr.mkApp (EConstr.to_constr evm pgm, [|Constr_quoter.TemplateCoqQuoter.quote_ident name; Constr.mkRel 0; EConstr.to_constr evm def|]) in
        run_template_program env evm ~poly pgm 
                                              in st in fun name
         def ~atts ~st -> coqpp_body name def
         (Attributes.parse polymorphic atts) ~st), None))]

let () = Vernacextend.vernac_extend ~command:"TemplateCoq_Quote_Definition_Eval" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Quote", 
                                     Vernacextend.TyTerminal ("Definition", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                     Vernacextend.TyTerminal (":=", Vernacextend.TyTerminal ("Eval", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_red_expr), 
                                                                    Vernacextend.TyTerminal ("in", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNil)))))))), 
         (let coqpp_body name rd def poly ~st = let () = 
# 82 "src/g_template_coq.mlg"
        let (env, evm) = fresh_env () in
        let (evm, def) = Constrintern.interp_open_constr env evm def in
        (* TODO : implem quoting of tactic reductions so that we can use ptmQuoteDefinitionRed *)
        let (evm, rd) = Tacinterp.interp_redexp env evm rd in
	      let (evm, def) = Quoter.reduce env evm rd (EConstr.to_constr evm def) in
        let (evm, pgm) = EConstr.fresh_global env evm (Lazy.force Template_monad.ptmQuoteDefinition) in
        let pgm = Constr.mkApp (EConstr.to_constr evm pgm, [|Constr_quoter.TemplateCoqQuoter.quote_ident name; Constr.mkRel 0; def|]) in
        run_template_program env evm ~poly pgm 
                                                 in st in fun name
         rd def ~atts ~st -> coqpp_body name rd def
         (Attributes.parse polymorphic atts) ~st), None))]

let () = Vernacextend.vernac_extend ~command:"TemplateCoq_Quote_Recursively_Definition" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Quote", 
                                     Vernacextend.TyTerminal ("Recursively", 
                                     Vernacextend.TyTerminal ("Definition", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                     Vernacextend.TyTerminal (":=", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNil)))))), 
         (let coqpp_body name def poly ~st = let () = 
# 94 "src/g_template_coq.mlg"
        let (env, evm) = fresh_env () in
        let (evm, def) = Constrintern.interp_open_constr env evm def in
        let (evm, pgm) = EConstr.fresh_global env evm (Lazy.force Template_monad.ptmQuoteRecDefinition) in
        let pgm = Constr.mkApp (EConstr.to_constr evm pgm, [|Constr_quoter.TemplateCoqQuoter.quote_ident name; Constr.mkRel 0; EConstr.to_constr evm def|]) in
        run_template_program env evm ~poly pgm 
                                              in st in fun name
         def ~atts ~st -> coqpp_body name def
         (Attributes.parse polymorphic atts) ~st), None))]

let () = Vernacextend.vernac_extend ~command:"TemplateCoq_Make_Definition" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Make", 
                                     Vernacextend.TyTerminal ("Definition", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                     Vernacextend.TyTerminal (":=", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNil))))), 
         (let coqpp_body name def poly ~st = let () = 
# 103 "src/g_template_coq.mlg"
        let (env, evm) = fresh_env () in
        let (evm, def) = Constrintern.interp_open_constr env evm def in
        let (evm, pgm) = EConstr.fresh_global env evm (Lazy.force Template_monad.ptmMkDefinition) in
        let pgm = Constr.mkApp (EConstr.to_constr evm pgm, [|Constr_quoter.TemplateCoqQuoter.quote_ident name; EConstr.to_constr evm def|]) in
        run_template_program env evm ~poly pgm 
                                              in st in fun name
         def ~atts ~st -> coqpp_body name def
         (Attributes.parse polymorphic atts) ~st), None))]

let () = Vernacextend.vernac_extend ~command:"TemplateCoq_Make_Inductive" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Make", 
                                     Vernacextend.TyTerminal ("Inductive", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNil))), (let coqpp_body def
                                                            poly ~st = 
                                                            let () = 
                                                            
# 112 "src/g_template_coq.mlg"
        let (env, evm) = fresh_env () in
        let (evm, def) = Constrintern.interp_open_constr env evm def in
        let (evm, pgm) = EConstr.fresh_global env evm (Lazy.force Template_monad.ptmMkInductive) in
        let pgm = Constr.mkApp (EConstr.to_constr evm pgm, [|EConstr.to_constr evm def|]) in
        run_template_program env evm ~poly pgm 
                                                             in st in fun def
                                                            ~atts ~st
                                                            -> coqpp_body def
                                                            (Attributes.parse polymorphic atts) ~st), None))]

let () = Vernacextend.vernac_extend ~command:"TemplateCoq_Run_Template_Program" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Run", 
                                     Vernacextend.TyTerminal ("TemplateProgram", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNil))), (let coqpp_body def
                                                            poly ~st = 
                                                            let () = 
                                                            
# 121 "src/g_template_coq.mlg"
        let (env, evm) = fresh_env () in
        let (evm, def) = Constrintern.interp_open_constr env evm def in
        let pgm = EConstr.to_constr evm def in
        run_template_program env evm ~poly pgm 
                                                             in st in fun def
                                                            ~atts ~st
                                                            -> coqpp_body def
                                                            (Attributes.parse polymorphic atts) ~st), None))]

let () = Tacentries.tactic_extend __coq_plugin_name "TemplateCoq_quote_term" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("quote_term", Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                              Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                              Tacentries.TyNil))), 
           (fun c tac ist -> 
# 132 "src/g_template_coq.mlg"
        (* quote the given term, pass the result to t *)
        Proofview.Goal.enter begin fun gl ->
          let env = Proofview.Goal.env gl in
          let c = EConstr.to_constr (Proofview.Goal.sigma gl) c in
	  let c = Constr_quoter.TermReify.quote_term env c in
	  ltac_apply tac (List.map to_ltac_val [EConstr.of_constr c])
  end 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "TemplateCoq_denote_term" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("denote_term", Tacentries.TyArg (
                                                               Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                               Tacentries.TyArg (
                                                               Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                               Tacentries.TyNil))), 
           (fun c tac ist -> 
# 143 "src/g_template_coq.mlg"
        Proofview.Goal.enter (begin fun gl ->
         let evm = Proofview.Goal.sigma gl in
         let evm, c = Constr_denoter.denote_term evm (EConstr.to_constr evm c) in
         Proofview.tclTHEN (Proofview.Unsafe.tclEVARS evm)
	   (ltac_apply tac (List.map to_ltac_val [EConstr.of_constr c]))
      end) 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "TemplateCoq_run_template_program" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("run_template_program", 
                            Tacentries.TyArg (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                            Tacentries.TyArg (Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                            Tacentries.TyNil))), (fun c tac ist -> 
# 153 "src/g_template_coq.mlg"
        let open Proofview.Notations in
        Proofview.tclProofInfo [@ocaml.warning "-3"] >>= fun (name, poly) ->
        Proofview.Goal.enter (begin fun gl ->
         let env = Proofview.Goal.env gl in
         let evm = Proofview.Goal.sigma gl in
         let ret = ref None in
         Run_template_monad.run_template_program_rec ~poly ~intactic:true (fun x -> ret := Some x) env (evm, EConstr.to_constr evm c);
         match !ret with
           Some (env, evm, t) ->
            Proofview.tclTHEN
              (Proofview.Unsafe.tclEVARS evm) 
              (ltac_apply tac (List.map to_ltac_val [EConstr.of_constr t]))
         | None -> Proofview.tclUNIT ()
       end) 
                                                 )))]

