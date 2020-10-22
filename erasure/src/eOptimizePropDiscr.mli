open BasicAst
open Datatypes
open EAst
open ETyping
open Extract
open List0
open MCProd

val optimize : E.global_context -> E.term -> E.term

val optimize_constant_decl :
  E.global_context -> E.constant_body -> E.constant_body

val optimize_decl : E.global_context -> E.global_decl -> E.global_decl

val optimize_env : global_declarations -> (kername * E.global_decl) list
