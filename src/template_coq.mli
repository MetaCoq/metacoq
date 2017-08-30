(** Translate from Coq terms to Template_AST terms *)
val quote_string : string -> char list
val quote_term : Environ.env -> Constr.t -> Template_AST.term
val quote_term_rec : Environ.env -> Constr.t -> Template_AST.program
