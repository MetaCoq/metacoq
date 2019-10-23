From Coq Require Import Ascii String Bool OrderedType Lia List Program Arith.
From MetaCoq.Template Require Import utils BasicAst.
Import List.ListNotations.
Require Import ssreflect.

Set Asymmetric Patterns.

Module Type Term.

  Parameter (term : Set).

End Term.

Module Environment (T : Term).

  Import T.

  (** ** Declarations *)

  (** *** The context of De Bruijn indices *)

  Record context_decl := mkdecl {
    decl_name : name ;
    decl_body : option term ;
    decl_type : term
  }.

  (** Local (de Bruijn) variable binding *)

  Definition vass x A :=
    {| decl_name := x ; decl_body := None ; decl_type := A |}.

  (** Local (de Bruijn) let-binding *)

  Definition vdef x t A :=
    {| decl_name := x ; decl_body := Some t ; decl_type := A |}.

  (** Local (de Bruijn) context *)

  Definition context := list context_decl.

  (** Last declaration first *)

  Definition snoc {A} (Γ : list A) (d : A) := d :: Γ.

  Notation " Γ ,, d " := (snoc Γ d) (at level 20, d at next level).

End Environment.

