open Ast0
open BasicAst
open Datatypes
open List0
open PCUICAst
open PCUICAstUtils
open Universes0
open Utils

module T = Ast0

val trans : T.term -> term

val trans_decl : T.context_decl -> context_decl

val trans_local : T.context_decl list -> context_decl list

val trans_one_ind_body : T.one_inductive_body -> one_inductive_body

val trans_constant_body : T.constant_body -> constant_body

val trans_minductive_body : T.mutual_inductive_body -> mutual_inductive_body

val trans_global_decl : T.global_decl -> global_decl

val trans_global_decls : T.global_decl list -> global_decl list

val trans_global : T.global_env_ext -> global_decl list * constraints
