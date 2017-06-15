Require Import Template.Template.
Require Import String.

Open Scope string.


(* Set Universe Polymorphism. *)

Monomorphic Universe i j.
Definition test := (fun (T : Type@{i}) (T2 : Type@{j}) => T -> T2).
Set Printing Universes.
Print test.
Print Universes.
Unset Printing Universes. 

Quote Definition qtest := Eval compute in (fun (T : Type@{i}) (T2 : Type@{j}) => T -> T2).
Print qtest.
Print test.

Make Definition bla := (Ast.tLambda (Ast.nNamed "T") (Ast.tSort (Ast.sType "Top.1"))
  (Ast.tLambda (Ast.nNamed "T2") (Ast.tSort (Ast.sType "Top.2")) (Ast.tProd Ast.nAnon (Ast.tRel 1) (Ast.tRel 1)))).

Set Printing Universes.
Print bla.
Print Universes.

Print test.
Unset Printing Universes.

Set Universe Polymorphism.

Section test.
  Universe u v.

  Definition t@{u v} :=  (fun (T : Type@{u}) (T2 : Type@{v}) => T -> T2).
  Set Printing Universes.
  Print t.

  
End test.

Compute t.
Compute (@t Type@{i} Type@{j}).

Quote Definition qt := Eval compute in t.
Print qt.

Polymorphic Definition Funtp@{i} (A B: Type@{i}) := A->B.

Quote Definition qFuntp := Eval compute in Funtp.
Print qFuntp.
(** the same thing is quoted in demo.v using the template-coq monad
there the poly vars actually show up *)


Make Definition t2 := (Ast.tLambda (Ast.nNamed "T") (Ast.tSort (Ast.sType "Top.1"))
                                   (Ast.tLambda (Ast.nNamed "T2") (Ast.tSort (Ast.sType "Top.2")) (Ast.tProd Ast.nAnon (Ast.tRel 1) (Ast.tRel 1)))).
Set Printing Universes.
Print t2.
Print Universes.
