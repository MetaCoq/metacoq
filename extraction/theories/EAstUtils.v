From Coq Require Import Ascii String Bool OrderedType Lia List Program Arith.
From MetaCoq.Template Require Import utils Ast.
From MetaCoq.Extraction Require Import EAst.
Import List.ListNotations.
Require Import FunctionalExtensionality.
Require Import ssreflect.

Set Asymmetric Patterns.

Fixpoint decompose_app_rec t l :=
  match t with
  | tApp f a => decompose_app_rec f (a :: l)
  | f => (f, l)
  end.

Definition decompose_app f := decompose_app_rec f [].
