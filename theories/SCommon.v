From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast SAst Typing SLiftSubst.

Record scontext_decl := { decl_name : name ;
                         decl_body : option sterm ;
                         decl_type : sterm }.

Definition svass x A := {| decl_name := x; decl_body := None; decl_type := A |}.
Definition svdef x t A :=
  {| decl_name := x; decl_body := Some t; decl_type := A |}.

Definition scontext := (list scontext_decl).

Definition ssnoc (Γ : scontext) (d : scontext_decl) := d :: Γ.

Notation " Γ ,, d " := (ssnoc Γ d) (at level 20, d at next level) : s_scope.

Record squash (A : Set) : Prop := { _ : A }.