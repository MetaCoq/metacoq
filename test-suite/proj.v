Require Import Template.Template.

Set Primitive Projections.

Record Eq (A : Type) := { eq : A -> A -> bool }.

Goal forall {A} {e : Eq A} x y, e.(eq _) x y = eq _ e x y.
Proof.
  intros.
  match goal with
   |- ?T => quote_term T (fun x => pose (qgoal:=x))
  end.
Show.
  match goal with
    H:= context [Ast.tProj "Top.proj.eq" _] |- _ => idtac
  end.
  reflexivity.
Qed.