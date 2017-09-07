(** Translate from Coq terms to Template_AST terms *)
val quote_string : string -> char list
val quote_term : Environ.env -> Constr.t -> Ast0.term
val quote_term_rec : Environ.env -> Constr.t -> Ast0.program
