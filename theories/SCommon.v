From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast SAst Typing SLiftSubst.

Record scontext_decl := { sdecl_name : name ;
                          sdecl_body : option sterm ;
                          sdecl_type : sterm }.

Definition svass x A :=
  {| sdecl_name := x; sdecl_body := None; sdecl_type := A |}.
Definition svdef x t A :=
  {| sdecl_name := x; sdecl_body := Some t; sdecl_type := A |}.

Definition scontext := (list scontext_decl).

Definition ssnoc (Γ : scontext) (d : scontext_decl) := d :: Γ.

Notation " Γ ,, d " := (ssnoc Γ d) (at level 20, d at next level) : s_scope.

Record squash (A : Set) : Prop := { _ : A }.

(* Common lemmata *)

Lemma eq_safe_nth :
  forall {Γ n x A isdecl isdecl'},
    safe_nth (Γ ,, svass x A) (exist _ (S n) isdecl') =
    safe_nth Γ (exist _ n isdecl).
Proof.
  intros Γ. induction Γ ; intros n x A isdecl isdecl'.
  - easy.
  - destruct n.
    + reflexivity.
    + cbn. admit.
Admitted.

Lemma max_id :
  forall s, max_sort s s = s.
Admitted.

Lemma max_succ_id :
  forall s, max_sort (succ_sort s) s = succ_sort s.
Admitted.