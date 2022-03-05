open BasicAst
open Datatypes
open PCUICAst
open Universes0

type eval =
| Coq_eval_beta of term * aname * term * term * term * term * term * 
   eval * eval * eval
| Coq_eval_zeta of aname * term * term * term * term * term * eval * eval
| Coq_eval_delta of kername * PCUICEnvironment.constant_body * term
   * Instance.t * term * eval
| Coq_eval_iota of case_info * term * nat
   * PCUICEnvironment.mutual_inductive_body
   * PCUICEnvironment.one_inductive_body * PCUICEnvironment.constructor_body
   * Instance.t * term list * term predicate * term branch list * term branch
   * term * eval * eval
| Coq_eval_proj of inductive * nat * nat * term * term list * Instance.t
   * term * term * eval * eval
| Coq_eval_fix of term * term mfixpoint * nat * term list * term * term
   * term * term * eval * eval * eval
| Coq_eval_fix_value of term * term mfixpoint * nat * term list * term * 
   term * nat * term * eval * eval
| Coq_eval_cofix_case of case_info * term mfixpoint * nat * term predicate
   * term * term list * nat * term * term branch list * term * eval * 
   eval
| Coq_eval_cofix_proj of projection * term mfixpoint * nat * term * term list
   * nat * term * term * eval * eval
| Coq_eval_app_cong of term * term * term * term * eval * eval
| Coq_eval_atom of term
