From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import Loader.
Require Import String.
Set Template Cast Propositions.

Definition foo (x : nat) (p : True) := p.

MetaCoq Quote Recursively Definition q_foo := foo.

Definition fooapp := foo 0 I.
MetaCoq Quote Recursively Definition q_fooapp := @fooapp.
Definition f (x : nat) (p : True) (y : nat) := y.

Definition fapp (x : nat) := f 0 I x.
MetaCoq Quote Recursively Definition q_fapp := @fapp.

Definition setprop : { x : nat | x = 0 } := exist _ 0 eq_refl.
MetaCoq Quote Recursively Definition q_setprop := setprop.

Notation proof t :=
  (Ast.tCast t BasicAst.Cast (Ast.tCast _ BasicAst.Cast (Ast.tSort ((Universes.sProp :: nil)%list; _)))).
