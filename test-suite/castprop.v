Require Import Template.Template.
Require Import String.
Set Template Cast Propositions.

Definition foo (x : nat) (p : True) := p.

Quote Recursively Definition q_foo := foo.

Definition fooapp := foo 0 I.
Quote Recursively Definition q_fooapp := @fooapp.
Definition f (x : nat) (p : True) (y : nat) := y.

Definition fapp (x : nat) := f 0 I x.
Quote Recursively Definition q_fapp := @fapp.

Definition setprop : { x : nat | x = 0 } := exist _ 0 eq_refl.
Quote Recursively Definition q_setprop := setprop.

Notation proof t :=
  (Ast.tCast t Ast.Cast (Ast.tCast _ Ast.Cast (Ast.tSort Ast.sProp))).
