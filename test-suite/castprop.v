Require Import Template.Template.
Require Import String.
Set Template Cast Propositions.

Definition foo (x : nat) (p : True) := p.

Quote Recursively Definition q_foo := foo.


Definition setprop : { x : nat | x = 0 } := exist _ 0 eq_refl.


Quote Recursively Definition q_setprop := setprop.

Notation proof t := (Ast.tCast (Ast.tCast t Ast.Cast _)
                               Ast.Cast (Ast.tSort Ast.sProp)).
