From Template Require Import Ast Template Typing LiftSubst Checker monad_utils.
Require Import  Translations.translation_utils.
Require Import List String.
Import ListNotations MonadNotation.

(* **************************************************** *)
(* In this file we define a small plugin which allow to *)
(* add a constructor to an inductive without rewriting  *)
(* the whole inductive.                                 *)
(* **************************************************** *)


(** ** Auxiliary functions *)

Definition try_beta_reduce t :=
  let flags := RedFlags.mk true false false false false false in
  match reduce_opt flags [] [] fuel t with
  | Some t => t
  | None => t
  end.

Class TslIdent := { tsl_ident : ident -> ident }.

Instance prime_tsl_ident : TslIdent
  := {| tsl_ident := fun id => (id ++ "'")%string |}.


(** * Plugin *)

(* [add_ctor] add a constructor to a [minductive_decl]
 (that is a reified declaration of an inductive). *)

Definition add_ctor (mind : minductive_decl) (ind0 : inductive) (idc : ident) (ctor : term)
  : minductive_decl.
  refine {| ind_npars := mind.(ind_npars); ind_bodies := _ |}.
  refine (map_i _ mind.(ind_bodies)).
  intros i ind.
  refine {| ind_name := tsl_ident ind.(ind_name);
            ind_type := ind.(ind_type);
            ind_kelim := ind.(ind_kelim);
            ind_ctors := _;
            ind_projs := ind.(ind_projs) |}.
  refine (let ctors := List.map (fun '((id,t),k) => (tsl_ident id,t,k))
                                ind.(ind_ctors) in
          let i0 := inductive_ind ind0 in _).
  refine (if Nat.eqb i i0
          then (ctors ++ [_])%list else ctors).
  exact (let n := List.length mind.(ind_bodies) in
         let typ := try_beta_reduce (tApp ctor [tRel (n - i0 - 1)]) in
         (idc, typ, 0)).
Defined.

(* [add_constructor] is a new command (in Template Coq style) *)
(* which do what we want *)

Definition add_constructor {A} (ind : A) (idc : ident)
                           (ctor : A -> Type)
  : TemplateMonad unit
  := tm <- tmQuote ind ;;
     match tm with
     | tInd ind0 _ =>
       decl <- tmQuoteInductive (inductive_mind ind0) ;;
       ctor <- tmQuote ctor ;;
       e <- tmEval lazy (mind_decl_to_entry
                         (add_ctor decl ind0 idc ctor)) ;;
       tmMkInductive e
     | _ => tmPrint ind ;; tmFail " is not an inductive"
     end.


(** * Examples *)

(** Here we add a silly constructor to bool. *)
Run TemplateProgram (add_constructor bool "P" (fun bool' => nat -> bool' -> bool -> bool')).

Print bool'.
(* Inductive bool' : Set := *)
(*     true' : bool' *)
(*   | false' : bool' *)
(*   | P : nat -> bool' -> bool -> bool' *)


(** Here is a useful usecase: add a case to a syntax. *)
Inductive tm :=
| var : nat -> tm
| lam : tm -> tm
| app : tm -> tm -> tm.

Run TemplateProgram
    (add_constructor tm "letin" (fun tm' => tm' -> tm' -> tm')).

Print tm'.
(* Inductive tm' : Type := *)
(*     var' : nat -> tm' *)
(*   | lam' : tm' -> tm' *)
(*   | app' : tm' -> tm' -> tm' *)
(*   | letin : tm' -> tm' -> tm' *)
