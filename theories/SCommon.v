From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast SAst Typing SLiftSubst.

Record context_decl := { decl_name : name ;
                         decl_body : option sterm ;
                         decl_type : sterm }.

Definition vass x A := {| decl_name := x; decl_body := None; decl_type := A |}.
Definition vdef x t A :=
  {| decl_name := x; decl_body := Some t; decl_type := A |}.

Definition context := (list context_decl).

Definition snoc (Γ : context) (d : context_decl) := d :: Γ.

Notation " Γ ,, d " := (snoc Γ d) (at level 20, d at next level) : s_scope.

Record squash (A : Set) : Prop := { _ : A }.