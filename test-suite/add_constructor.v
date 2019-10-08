Require Import MetaCoq.Template.All.
Require Import List String.
Import ListNotations MonadNotation.

(* **************************************************** *)
(* In this file we define a small plugin which allow to *)
(* add a constructor to an inductive without rewriting  *)
(* the whole inductive.                                 *)
(* **************************************************** *)


(** ** Auxiliary functions *)


Class TslIdent := { tsl_ident : ident -> ident }.

Instance prime_tsl_ident : TslIdent
  := {| tsl_ident := fun id => (id ++ "'")%string |}.

Fixpoint try_remove_n_lambdas (n : nat) (t : term) {struct n} : term :=
  match n, t with
  | 0, _ => t
  | S n, tLambda _ _ t => try_remove_n_lambdas n t
  | S n, _ => t
  end.


(** * Plugin *)

(* [add_ctor] add a constructor to a [mutual_inductive_body]
 (that is a reified declaration of an inductive). *)

Polymorphic Definition add_ctor (mind : mutual_inductive_body) (ind0 : inductive) (idc : ident) (ctor : term)
  : mutual_inductive_body
  := let i0 := inductive_ind ind0 in
     {| ind_finite := mind.(ind_finite);
        ind_npars := mind.(ind_npars) ;
        ind_universes := mind.(ind_universes) ;
        ind_params := mind.(ind_params);
        ind_bodies := mapi (fun (i : nat) (ind : one_inductive_body) =>
                         {| ind_name := tsl_ident ind.(ind_name) ;
                            ind_type  := ind.(ind_type) ;
                            ind_kelim := ind.(ind_kelim) ;
                            ind_ctors := let ctors := map (fun '(id, t, k) => (tsl_ident id, t, k)) ind.(ind_ctors) in
                                         if Nat.eqb i i0 then
                                           let n := #|ind_bodies mind| in
                                           let typ := try_remove_n_lambdas n ctor in
                                           ctors ++ [(idc, typ, 0)]  (* fixme 0 *)
                                         else ctors;
                            ind_projs := ind.(ind_projs) |})
                            mind.(ind_bodies) |}.


(* [add_constructor] is a new command (in Template Coq style) *)
(* which do what we want *)

Polymorphic Definition add_constructor (tm : Ast.term)
            (idc : ident) (type : Ast.term)
  : TemplateMonad unit
  := match tm with
     | tInd ind0 _ =>
       decl <- tmQuoteInductive (inductive_mind ind0) ;;
       let ind' := add_ctor decl ind0 idc type in
       tmMkInductive' ind'
     | _ => tmPrint tm ;; tmFail " is not an inductive"
     end.


(** * Examples *)
Local Open Scope string.
(** Here we add a silly constructor to bool. *)
MetaCoq Run (
    add_constructor <% bool %> "foo" <% (fun x : Type => nat -> x -> bool -> x) %>).
(* Inductive bool' : Set := *)
(*     true' : bool' *)
(*   | false' : bool' *)
(*   | foo : nat -> bool' -> bool -> bool' *)


(** Here is a useful usecase: add a case to a syntax. *)
Inductive tm :=
| var : nat -> tm
| lam : tm -> tm
| app : tm -> tm -> tm.

MetaCoq Run (add_constructor <%tm%> "letin" <% (fun tm' => tm' -> tm' -> tm') %>).

Print tm'.
(* Inductive tm' : Type := *)
(*     var' : nat -> tm' *)
(*   | lam' : tm' -> tm' *)
(*   | app' : tm' -> tm' -> tm' *)
(*   | letin : tm' -> tm' -> tm' *)


MetaCoq Run (add_constructor <%@eq%> "foo'"
                    <% (fun (eq':forall A, A -> A -> Type) => forall A x y, nat -> eq' A x x -> bool -> eq' A x y) %>).

Require Import Even.
MetaCoq Run (add_constructor <%@odd%> "foo''"
                    <%(fun (even' odd':nat -> Prop) => odd' 0)%>).

Module A.
MetaCoq Run (add_constructor <%even%> "foo'"
                    <%(fun (even' odd':nat -> Prop) => even' 0)%>).
End A.
