Require Import MetaCoq.Template.Loader.

Goal True.
  evar (n : nat).
  match goal with
    H := ?t |- _ => quote_term t (fun x => pose (qn:=x))
  end.
  match goal with
    qn := Ast.tEvar _ nil |- _ => idtac
  end.
  exact I.
  Unshelve. exact 0.
Qed.