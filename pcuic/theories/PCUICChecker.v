(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaCoq.Template Require Import config monad_utils utils AstUtils UnivSubst.
From MetaCoq.Checker Require Import uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICUnivSubst
     PCUICTyping.

Import MonadNotation.
Open Scope pcuic.

(** * Coq type-checker for kernel terms

  *WIP*

  Implemets [typecheck_program] which returns an error and
  on success should guarantee that the term has the given type.
  Currently uses fuel to implement reduction.

  Correctness and completeness proofs are a work-in-progress.

  This file implements reduction with a stack machine [reduce_stack],
  conversion/cumulativity with the first-order fast-path heuristic [isconv]
  that are used to type-check terms in reasonable time. *)


Inductive type_error :=
| UnboundRel (n : nat)
| UnboundVar (id : string)
| UnboundMeta (m : nat)
| UnboundEvar (ev : nat)
| UndeclaredConstant (c : string)
| UndeclaredInductive (c : inductive)
| UndeclaredConstructor (c : inductive) (i : nat)
| NotConvertible (Γ : context) (t u t' u' : term)
| NotASort (t : term)
| NotAProduct (t t' : term)
| NotAnInductive (t : term)
| IllFormedFix (m : mfixpoint term) (i : nat)
| UnsatisfiedConstraints (c : ConstraintSet.t)
| CannotTakeSuccessor (u : universe)
| NotEnoughFuel (n : nat).


Inductive typing_result (A : Type) :=
| Checked (a : A)
| TypeError (t : type_error).
Global Arguments Checked {A} a.
Global Arguments TypeError {A} t.

Instance typing_monad : Monad typing_result :=
  {| ret A a := Checked a ;
     bind A B m f :=
       match m with
       | Checked a => f a
       | TypeError t => TypeError t
       end
  |}.

Instance monad_exc : MonadExc type_error typing_result :=
  { raise A e := TypeError e;
    catch A m f :=
      match m with
      | Checked a => m
      | TypeError t => f t
      end
  }.

Definition fix_decls (l : mfixpoint term) :=
  let fix aux acc ds :=
      match ds with
      | nil => acc
      | d :: ds => aux (vass d.(dname) d.(dtype) :: acc) ds
      end
  in aux [] l.

Section lookups.
  Context (Σ : global_env).

  Definition lookup_constant_type Σ cst u :=
    match lookup_env Σ cst with
    | Some (ConstantDecl _ {| cst_type := ty; cst_universes := uctx |}) =>
      ret (subst_instance_constr u ty)
    |  _ => raise (UndeclaredConstant cst)
    end.

  Definition lookup_ind_decl ind i :=
    match lookup_env Σ ind with
    | Some (InductiveDecl _ {| ind_bodies := l; ind_universes := uctx |}) =>
      match nth_error l i with
      | Some body => ret (l, uctx, body)
      | None => raise (UndeclaredInductive (mkInd ind i))
      end
    | _ => raise (UndeclaredInductive (mkInd ind i))
    end.

  Definition lookup_ind_type ind i (u : list Level.t) :=
    res <- lookup_ind_decl ind i ;;
    ret (subst_instance_constr u (snd res).(ind_type)).

  Definition lookup_constructor_decl ind i k :=
    res <- lookup_ind_decl ind i;;
    let '(l, uctx, body) := res in
    match nth_error body.(ind_ctors) k with
    | Some (_, ty, _) => ret (l, uctx, ty)
    | None => raise (UndeclaredConstructor (mkInd ind i) k)
    end.

  Definition lookup_constructor_type ind i k u :=
    res <- lookup_constructor_decl ind i k ;;
    let '(l, uctx, ty) := res in
    ret (subst0 (inds ind u l) (subst_instance_constr u ty)).
End lookups.
