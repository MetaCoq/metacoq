type ('a,'b) sum =
  Left of 'a | Right of 'b

type ('term, 'name, 'nat) adef = { adname : 'name; adtype : 'term; adbody : 'term; rarg : 'nat }

type ('term, 'name, 'nat) amfixpoint = ('term, 'name, 'nat) adef list

type ('term, 'nat, 'ident, 'name, 'quoted_sort, 'cast_kind, 'kername, 'inductive, 'universe_instance, 'projection) structure_of_term =
  | ACoq_tRel of 'nat
  | ACoq_tVar of 'ident
  | ACoq_tEvar of 'nat * 'term list
  | ACoq_tSort of 'quoted_sort
  | ACoq_tCast of 'term * 'cast_kind * 'term
  | ACoq_tProd of 'name * 'term * 'term
  | ACoq_tLambda of 'name * 'term * 'term
  | ACoq_tLetIn of 'name * 'term * 'term * 'term
  | ACoq_tApp of 'term * 'term list
  | ACoq_tConst of 'kername * 'universe_instance
  | ACoq_tInd of 'inductive * 'universe_instance
  | ACoq_tConstruct of 'inductive * 'nat * 'universe_instance
  | ACoq_tCase of ('inductive * 'nat) * 'term * 'term * ('nat * 'term) list
  | ACoq_tProj of 'projection * 'term
  | ACoq_tFix of ('term, 'name, 'nat) amfixpoint * 'nat
  | ACoq_tCoFix of ('term, 'name, 'nat) amfixpoint * 'nat

(* todo(gmm): these are helper functions *)
let string_to_list s =
  let rec aux acc i =
    if i < 0 then acc
    else aux (s.[i] :: acc) (i - 1)
  in aux [] (String.length s - 1)

let list_to_string l =
  let buf = Bytes.create (List.length l) in
  let rec aux i = function
    | [] -> ()
    | c :: cs ->
      Bytes.set buf i c; aux (succ i) cs
  in
  aux 0 l;
  Bytes.to_string buf

(* Remove '#' from names *)
let clean_name s =
  let l = List.rev (CString.split '#' s) in
  match l with
    s :: rst -> s
  | [] -> raise (Failure "Empty name cannot be quoted")

let split_name s : (Names.DirPath.t * Names.Id.t) =
  let ss = List.rev (CString.split '.' s) in
  match ss with
    nm :: rst ->
     let nm = clean_name nm in
     let dp = (Names.DirPath.make (List.map Names.Id.of_string rst)) in (dp, Names.Id.of_string nm)
  | [] -> raise (Failure "Empty name cannot be quoted")



module type Quoted =
sig
  type t (* this represented quoted Gallina terms *)

  type quoted_ident
  type quoted_int
  type quoted_bool
  type quoted_name
  type quoted_sort
  type quoted_cast_kind
  type quoted_kernel_name
  type quoted_inductive
  type quoted_proj
  type quoted_global_reference

  type quoted_sort_family
  type quoted_constraint_type
  type quoted_univ_constraint
  type quoted_univ_constraints
  type quoted_univ_instance
  type quoted_univ_context
  type quoted_univ_contextset
  type quoted_abstract_univ_context
  type quoted_variance
  type quoted_universes_decl

  type quoted_mind_params
  type quoted_ind_entry = quoted_ident * t * quoted_bool * quoted_ident list * t list
  type quoted_definition_entry = t * t option * quoted_universes_decl
  type quoted_mind_entry
  type quoted_mind_finiteness
  type quoted_entry

  (* Local contexts *)
  type quoted_context_decl
  type quoted_context

  type quoted_one_inductive_body
  type quoted_mutual_inductive_body
  type quoted_constant_body
  type quoted_global_decl
  type quoted_global_env
  type quoted_program  (* the return type of quote_recursively *)

  val mkRel : quoted_int -> t
  val mkVar : quoted_ident -> t
  val mkEvar : quoted_int -> t array -> t
  val mkSort : quoted_sort -> t
  val mkCast : t -> quoted_cast_kind -> t -> t
  val mkProd : quoted_name -> t -> t -> t
  val mkLambda : quoted_name -> t -> t -> t
  val mkLetIn : quoted_name -> t -> t -> t -> t
  val mkApp : t -> t array -> t
  val mkConst : quoted_kernel_name -> quoted_univ_instance -> t
  val mkInd : quoted_inductive -> quoted_univ_instance -> t
  val mkConstruct : quoted_inductive * quoted_int -> quoted_univ_instance -> t
  val mkCase : (quoted_inductive * quoted_int) -> quoted_int list -> t -> t ->
               t list -> t
  val mkProj : quoted_proj -> t -> t
  val mkFix : (quoted_int array * quoted_int) * (quoted_name array * t array * t array) -> t
  val mkCoFix : quoted_int * (quoted_name array * t array * t array) -> t

  val mkName : quoted_ident -> quoted_name
  val mkAnon : unit -> quoted_name

end
