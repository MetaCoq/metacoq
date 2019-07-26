From Coq Require Import Ascii String Bool OrderedType Lia List Program Arith
     Omega.
From MetaCoq.Template Require Import utils AstUtils.
From MetaCoq.Template Require Import BasicAst.
From MetaCoq.PCUIC Require Import PCUICAst.
Import List.ListNotations.
Require Import ssreflect.

From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

Set Asymmetric Patterns.

Derive NoConfusion for term.
Derive Signature for All2.

Section ListSize.
  Context {A} (size : A -> nat).

  Equations list_size (l : list A) : nat :=
  list_size nil := 0;
  list_size (cons a v) := S (size a + list_size v).
  Global Transparent list_size.

  Lemma list_size_app (l l' : list A) : list_size (l ++ l') = list_size l + list_size l'.
  Proof.
    funelim (list_size l); simpl; rewrite ?H; auto with arith.
  Defined.

  Lemma list_size_rev (l : list A) : list_size (List.rev l) = list_size l.
  Proof.
    funelim (list_size l); simpl; rewrite ?H ?list_size_app; simpl; auto; try lia.
  Defined.

End ListSize.

Section ListSizeMap.
  Context {A} (sizeA : A -> nat).
  Context {B} (sizeB : B -> nat).

  Lemma list_size_mapi_rec_eq (l : list A) (f : nat -> A -> B) k :
    (forall i x, sizeB (f i x) = sizeA x) ->
    list_size sizeB (mapi_rec f l k) = list_size sizeA l.
  Proof.
    revert k.
    funelim (list_size sizeA l); simpl; intros; rewrite ?H ?list_size_app; simpl; auto; try lia.
  Defined.

  Lemma list_size_mapi_eq (l : list A) (f : nat -> A -> B) :
    (forall i x, sizeB (f i x) = sizeA x) ->
    list_size sizeB (mapi f l) = list_size sizeA l.
  Proof.
    unfold mapi. intros. now apply list_size_mapi_rec_eq.
  Defined.

  Lemma list_size_map_eq (l : list A) (f : A -> B) :
    (forall x, sizeA x = sizeB (f x)) ->
    list_size sizeB (map f l) = list_size sizeA l.
  Proof.
    intros.
    induction l; simpl; auto.
  Defined.

  Lemma list_size_mapi_rec_le (l : list A) (f : nat -> A -> B) k :
    (forall i x, sizeB (f i x) <= sizeA x) ->
    list_size sizeB (mapi_rec f l k) <= list_size sizeA l.
  Proof.
    intros Hf. revert k.
    apply_funelim (list_size sizeA l); simpl; intros; rewrite ?H ?list_size_app;
      simpl; auto; try lia.
    specialize (Hf k a).
    specialize (H (S k)). lia.
  Defined.

  Lemma list_size_mapi_le (l : list A) (f : nat -> A -> B) :
    (forall i x, sizeB (f i x) <= sizeA x) ->
    list_size sizeB (mapi f l) <= list_size sizeA l.
  Proof.
    unfold mapi. intros. now apply list_size_mapi_rec_le.
  Defined.

  Lemma list_size_map_le (l : list A) (f : A -> B) :
    (forall x, sizeB (f x) <= sizeA x) ->
    list_size sizeB (map f l) <= list_size sizeA l.
  Proof.
    intros.
    induction l; simpl; auto. specialize (H a).
    lia.
  Defined.

End ListSizeMap.

Lemma list_size_map_hom {A} (size : A -> nat) (l : list A) (f : A -> A) :
  (forall x, size x = size (f x)) ->
  list_size size (map f l) = list_size size l.
Proof.
  intros.
  induction l; simpl; auto.
Defined.

Definition def_size (size : term -> nat) (x : def term) := size (dtype x) + size (dbody x).
Definition mfixpoint_size (size : term -> nat) (l : mfixpoint term) :=
  list_size (def_size size) l.

Definition decl_size (size : term -> nat) (x : context_decl) :=
  size (decl_type x) + option_default size (decl_body x) 0.

Definition context_size (size : term -> nat) (l : context) :=
  list_size (decl_size size) l.

Fixpoint size t : nat :=
  match t with
  | tRel i => 1
  | tEvar ev args => S (list_size size args)
  | tLambda na T M => S (size T + size M)
  | tApp u v => S (size u + size v)
  | tProd na A B => S (size A + size B)
  | tLetIn na b t b' => S (size b + size t + size b')
  | tCase ind p c brs => S (size p + size c + list_size (fun x => size (snd x)) brs)
  | tProj p c => S (size c)
  | tFix mfix idx => S (mfixpoint_size size mfix)
  | tCoFix mfix idx => S (mfixpoint_size size mfix)
  | x => 1
  end.
