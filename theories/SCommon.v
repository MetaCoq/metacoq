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

Fact safe_nth_S :
  forall {A n} {a : A} {l isdecl},
    ∑ isdecl',
      safe_nth (a :: l) (exist _ (S n) isdecl) =
      safe_nth l (exist _ n isdecl').
Proof.
  intros A n. induction n ; intros a l isdecl.
  - cbn. eexists. reflexivity.
  - eexists. cbn. reflexivity.
Defined.

Lemma eq_safe_nth' :
  forall {Γ : scontext} {n a isdecl isdecl'},
    safe_nth (a :: Γ) (exist _ (S n) isdecl') =
    safe_nth Γ (exist _ n isdecl).
Proof.
  intros Γ. induction Γ ; intros n A isdecl isdecl'.
  - easy.
  - destruct n.
    + reflexivity.
    + destruct (@safe_nth_S _ (S n) A (a :: Γ) isdecl')
        as [isecl0 eq].
      rewrite eq.
      destruct (@safe_nth_S _ n a Γ isdecl)
        as [isecl1 eq1].
      rewrite eq1.
      apply IHΓ.
Defined.

Lemma eq_safe_nth :
  forall {Γ n x A isdecl isdecl'},
    safe_nth (Γ ,, svass x A) (exist _ (S n) isdecl') =
    safe_nth Γ (exist _ n isdecl).
Proof.
  intros Γ n x A isdecl isdecl'.
  apply eq_safe_nth'.
Defined.

Lemma max_id :
  forall s, max_sort s s = s.
Proof.
  intro s. induction s.
  all: cbn ; reflexivity.
Defined.

Lemma max_succ_id :
  forall s, max_sort (succ_sort s) s = succ_sort s.
Proof.
  (* This lemma is only true when s is not Prop which I ignored. *)
  intro s. induction s.
  all: cbn.
Admitted.

Definition sapp_context (Γ Γ' : scontext) : scontext := (Γ' ++ Γ)%list.
Notation " Γ  ,,, Γ' " := (sapp_context Γ Γ') (at level 25, Γ' at next level, left associativity) : s_scope.