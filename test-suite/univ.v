From Template Require Import Ast TemplateMonad Loader.
Require Import String.

Open Scope string.

Set Printing Universes.


Inductive foo (A : Type) : Type :=
| fooc : list A -> foo A.
(* Print Universes.*)
(* Top.1 <= Coq.Init.Datatypes.44 *)

Quote Recursively Definition qfoo := foo.
Compute qfoo.

Polymorphic Inductive foo2 (A : Type) : Type :=
| fooc2 : list A -> foo2 A.
(* Top.4 |= Top.4 <= Coq.Init.Datatypes.44 *)
(* Print Universes.*)

Definition foo2_instance := foo2.
(* Print Universes.*)
(* Top.9 <= Coq.Init.Datatypes.44 *)

Quote Recursively Definition qfoo2 := foo2.
Compute qfoo2.
(* (Level.Var 0, Le, Level.Level "Coq.Init.Datatypes.44") *)

Polymorphic Inductive foo3@{i j k l} (A : Type@{i}) (B : Type@{j}) : Type@{k} :=
| fooc3 : @eq Type@{l} (list A) B-> foo3 A B.
(* i j k l |= l < Coq.Init.Logic.8
              Set <= l
              i <= l
              i <= Coq.Init.Datatypes.44
              j <= l *)
Quote Recursively Definition qfoo3 := foo3.
Compute qfoo3.

Require Import Template.monad_utils. Import MonadNotation.
Run TemplateProgram (tmQuoteInductive "foo" >>= tmPrint).
Run TemplateProgram (tmQuoteInductive "foo2" >>= tmPrint).
Run TemplateProgram (tmQuoteInductive "foo3" >>= tmPrint).

Polymorphic Definition TT@{i j} : Type@{j} := Type@{i}.
Quote Recursively Definition qTT := TT.

Polymorphic Inductive TT2@{i j} : Type@{j} := tt2 : Type@{i} -> TT2.
Quote Recursively Definition qTT2 := TT2.

Require Import Template.utils.
Require Import List. Import ListNotations.

Module toto.

  (* Run TemplateProgram (en <- tmEval all (mind_body_to_entry (Build_minductive_decl 0 [{| *)
  (*  ind_name := "TT2"; *)
  (*  ind_type := tSort ((Level.Var 1, false) :: nil)%list; *)
  (*  ind_kelim := InProp :: (InSet :: InType :: nil)%list; *)
  (*  ind_ctors := ("tt2", *)
  (*               tProd nAnon (tSort ((Level.Var 0, false) :: nil)%list) (tRel 1), *)
  (*               1) :: nil; *)
  (*  ind_projs := nil |}] (UContext.make (Level.Var 0 :: Level.Var 1 :: nil)%list *)
  (*    (ConstraintSet.add (make_univ_constraint (Level.Var 0) Lt (Level.Var 1)) *)
  (*       ConstraintSet.empty)))) ;; *)

End toto.




(* Set Universe Polymorphism. *)

Monomorphic Universe i j.
Definition test := (fun (T : Type@{i}) (T2 : Type@{j}) => T -> T2).
Set Printing Universes.
Print test.
(* Print Universes. *)
Unset Printing Universes. 

Quote Definition qtest := Eval compute in (fun (T : Type@{i}) (T2 : Type@{j}) => T -> T2).
Print qtest.

Notation "'rAnon'" := (mkBindAnn nAnon Relevant).
Notation "'rName' n" := (mkBindAnn (nNamed n) Relevant) (at level 100).

Make Definition bla := Eval compute in qtest.
Make Definition bla' := (tLambda (rName "T") (tSort ((Level.Level "Top.2", false) :: nil)%list) (tLambda (rName "T2") (tSort ((Level.Level "Top.1", false) :: nil)%list) (tProd rAnon (tRel 1) (tRel 1)))).

Set Printing Universes.
Print bla.
Print bla'.
(* Print Universes. *)
Unset Printing Universes.

Set Universe Polymorphism.

Section test.
  Universe u v.

  Definition t@{u v} : _ -> _ -> Type@{max(u,v)}:=  (fun (T : Type@{u}) (T2 : Type@{v}) => T -> T2).
  Set Printing Universes.
  Print t.

  
End test.

Compute t.
Compute (@t Type@{i} Type@{j}).
(* Compute (@t@{i j i j}). *)

Quote Definition qt := Eval compute in t.
Print qt.

Make Definition t' := Eval compute in qt.

Polymorphic Definition Funtp@{i} (A B: Type@{i}) := A->B.

Polymorphic Definition F@{i} := Type@{i}.

Quote Definition qT := Eval compute in F.
Require Import List. Import ListNotations.

(* FIXME: this does not work *)
Fail Make Definition T' := (tSort [(Level.Var 1, false)]).

Quote Recursively Definition qT' := F.

Quote Definition qFuntp := Eval compute in Funtp.
Print qFuntp.
(** the same thing is quoted in demo.v using the template-coq monad
there the poly vars actually show up *)


Make Definition t2 := (Ast.tLambda (rName "T") (Ast.tSort [(Level.Level "Top.10001", false)])
                                   (Ast.tLambda (rName "T2") (Ast.tSort [(Level.Level "Top.10002", false)]) (Ast.tProd rAnon (Ast.tRel 1) (Ast.tRel 1)))).
Set Printing Universes.
Print t2.
(* Print Universes. *)


Monomorphic Universe i1 j1.
Definition f := (forall (A:Type@{i1}) (B: Type@{j1}), A -> B -> A).
(* : Type@{i1+1, j1+1} *)

Quote Recursively Definition ff := f.
Require Import Template.Checker.
Check (eq_refl :
         true =
         let T := infer (Typing.reconstruct_global_context (fst ff)) [] (snd ff) in
         match T with
         | Checked (tSort [(Level.Level _, true); (Level.Level _, true)]) => true
         | _ => false
         end).
Check (eq_refl :
         true =
         let T := infer ([], init_graph) [] ((tProd (rName "A") (tSort [(Level.Level "Toto.85", false)]) (tProd (rName "B") (tSort [(Level.Level "Toto.86", false)]) (tProd rAnon (tRel 1) (tProd rAnon (tRel 1) (tRel 3)))))) in
         match T with
         | Checked (tSort [(Level.Level _, true); (Level.Level _, true)]) => true
         | _ => false
         end).

Set Universe Polymorphism.

Definition id_f := fun x : nat => x.

Quote Definition id_syn := f.


(* Fails with "globalization of polymorphic reference f would forget universes." *)
Fail Make Definition id_f' := Eval compute in id_syn.

Fail Run TemplateProgram (
     id_syn <- tmQuote id_f;;
     id_f <- tmUnquoteTyped (nat -> nat) id_syn;;
     tmDefinition "id_f''" id_f
     ).
