From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast utils Typing.
From Translation Require Import SAst SLiftSubst.

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
Delimit Scope s_scope with s.

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

Definition max_sort := max.

Lemma max_id :
  forall s, max_sort s s = s.
Proof.
  intro s. unfold max_sort. auto with arith.
Defined.

Definition succ_sort := S.

Lemma max_succ_id :
  forall s, max_sort (succ_sort s) s = succ_sort s.
Proof.
  intro s. unfold max_sort, succ_sort.
  auto with arith.
Defined.

Definition sapp_context (Γ Γ' : scontext) : scontext := (Γ' ++ Γ)%list.
Notation " Γ  ,,, Γ' " := (sapp_context Γ Γ') (at level 25, Γ' at next level, left associativity) : s_scope.

(* Copy of global_contexts

   In some cases we just keep the TemplateCoq version (TC).
*)

Record sone_inductive_body := {
  sind_name : ident;
  sind_type : sterm;
  sind_kelim : list sort_family; (* TC *)
  sind_ctors : list (ident * sterm * nat);
  sind_projs : list (ident * term) (* TC *)
}.

Record smutual_inductive_body := {
  sind_npars : nat;
  sind_bodies : list sone_inductive_body ;
  sind_universes : universe_context }.

Inductive sglobal_decl :=
| SConstantDecl : kername -> constant_body -> sglobal_decl (* TC *)
| SInductiveDecl : kername -> smutual_inductive_body -> sglobal_decl.

Definition sglobal_declarations := list sglobal_decl.

Definition sglobal_context : Type := sglobal_declarations (* * uGraph.t *).