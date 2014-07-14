Require Import Template.Template.

Local Open Scope string_scope.

(** This is just printing **)
Test Quote (fun x : nat => x).

Test Quote (fun (f : nat -> nat) (x : nat) => f x).

Test Quote (let x := 2 in x).

Test Quote (let x := 2 in
            match x with
              | 0 => 0
              | S n => n
            end).

(** Build a definition **)
Definition d : Ast.term.
  let t := constr:(fun x : nat => x) in
  let k x := refine x in
  quote_term t k.
Defined.

(** Another way **)
Quote Definition d' := (fun x : nat => x).

(** To quote existing definitions **)
Definition id_nat : nat -> nat := fun x => x.

Quote Definition d'' := Eval compute in id_nat.

(** Fixpoints **)
Fixpoint add (a b : nat) : nat :=
  match a with
    | 0 => b
    | S a => S (add a b)
  end.

Fixpoint add' (a b : nat) : nat :=
  match b with
    | 0 => a
    | S b => S (add' a b)
  end.

Quote Definition add_syntax := Eval compute in add.

Quote Definition add'_syntax := Eval compute in add'.

(** Reflecting definitions **)

Make Definition zero_from_syntax := (Ast.tConstruct (Ast.mkInd "Coq.Init.Datatypes.nat" 0) 0).

Make Definition two_from_syntax := (Ast.tApp (Ast.tConstruct (Ast.mkInd "Coq.Init.Datatypes.nat" 0) 1)
   (Ast.tApp (Ast.tConstruct (Ast.mkInd "Coq.Init.Datatypes.nat" 0) 1)
      (Ast.tConstruct (Ast.mkInd "Coq.Init.Datatypes.nat" 0) 0 :: nil) :: nil)).
