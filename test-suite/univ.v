From Template Require Import All.
Require Import String List Arith.
Import ListNotations MonadNotation.
Open Scope string.

Set Printing Universes.

Test Quote Type.

Fail Make Definition t1 := (tSort []).
Fail Make Definition t1 := (tSort [(Level.Level "Top.400", false)]).

Monomorphic Definition T := Type.
(* Make Definition t1 := (tSort [(Level.Level "Top.2", false)]). *)

Unset Strict Unquote Universe Mode.
Make Definition t2 := (tSort []).
Make Definition t3 := (tSort [(Level.Level "Top.400", false)]).
Make Definition t4 := (tSort [(Level.Level "Top.2", false); (Level.Level "Top.2", true); (Level.Level "Top.200", false)]).


Monomorphic Universe i j.

Set Strict Unquote Universe Mode.
Test Quote (Type@{j} -> Type@{i}).
Make Definition T'' := (tSort [(Level.Level "j", false)]).
Unset Strict Unquote Universe Mode.


Polymorphic Definition pidentity {A : Type} (a : A) := a.
Test Quote @pidentity.
Polymorphic Definition selfpid := pidentity (@pidentity).
Test Quote @selfpid.

Constraint i < j.
Make Definition yuyu := (tConst "selfpid" [Level.Level "j"; Level.Level "i"]).


Quote Definition t0 := nat.
Run TemplateProgram (tmUnquoteTyped Type t0).
Definition ty : Type := Type.
Run TemplateProgram (tmUnquoteTyped ty t0).

Polymorphic Cumulative Inductive test := .
Polymorphic Cumulative Record packType := {pk : Type}.
Run TemplateProgram (α <- tmQuoteInductive "test" ;; tmPrint α).
Run TemplateProgram (tmQuoteInductive "packType" >>= tmEval all >>= tmPrint).
Polymorphic Cumulative Record Category@{i j} :=
{ Obj : Type@{i}; Hom : Obj -> Obj -> Type@{j} }.
Polymorphic  Record Functor@{i j} (C D : Category@{i j}):=
{ ObjF : C.(Obj) -> D.(Obj) }.
Polymorphic Definition Cat@{i j k l} : Category@{i j}
 := Build_Category@{i j} Category@{k l} Functor@{k l}.

Run TemplateProgram (tmQuoteInductive "Category" >>= tmEval all >>= tmPrint).
Run TemplateProgram (tmQuoteConstant "Cat" false >>= tmEval all >>= tmPrint).


Polymorphic Cumulative Inductive list (A : Type) : Type :=
nil : list A | cons : A -> list A -> list A.

Module to.
Run TemplateProgram (t <- tmQuoteInductive "list" ;;
                     t <- tmEval all (mind_body_to_entry t) ;;
                     tmMkInductive t).
End to.

Compute (AstUtils.mind_body_to_entry {|
ind_npars := 0;
ind_bodies := [{|
               ind_name := "Category";
               ind_type := tSort
                             [(Level.Level "Top.275", true);
                             (Level.Level "Top.276", true)];
               ind_kelim := [InProp; InSet; InType];
               ind_ctors := [("Build_Category",
                             tProd (nNamed "Obj") (tSort [(Level.Var 0, false)])
                               (tProd (nNamed "Hom")
                                  (tProd nAnon (tRel 0)
                                     (tProd nAnon (tRel 1)
                                        (tSort [(Level.Var 1, false)]))) 
                                  (tRel 2)), 2)];
               ind_projs := [] |}];
ind_universes := Cumulative_ctx
                   ([Level.Level "Top.275"; Level.Level "Top.276"],
                   {|
                   ConstraintSet.this := [];
                   ConstraintSet.is_ok := ConstraintSet.Raw.empty_ok |},
                   [Variance.Covariant; Variance.Covariant]) |}).

Fail Make Inductive {|
       mind_entry_record := None;
       mind_entry_finite := Finite;
       mind_entry_params := [];
       mind_entry_inds := [{|
                           mind_entry_typename := "Category";
                           mind_entry_arity := tSort
                                                 [(Level.Level "Top.275", true);
                                                 (Level.Level "Top.276", true)];
                           mind_entry_template := false;
                           mind_entry_consnames := ["Build_Category"];
                           mind_entry_lc := [tProd (nNamed "Obj")
                                               (tSort [(Level.Var 0, false)])
                                               (tProd 
                                                  (nNamed "Hom")
                                                  (tProd nAnon 
                                                     (tRel 0)
                                                     (tProd nAnon 
                                                     (tRel 1)
                                                     (tSort [(Level.Var 1, false)])))
                                                  (tRel 2))] |}];
       mind_entry_universes := Cumulative_ctx
                                 ([Level.Level "Top.275"; Level.Level "Top.276"],
                                 {|
                                 ConstraintSet.this := [];
                                 ConstraintSet.is_ok := ConstraintSet.Raw.empty_ok |},
                                 [Variance.Covariant; Variance.Covariant]);
       mind_entry_private := None |}.


Definition f@{i j k} := fun (E:Type@{i}) => Type@{max(i,j)}.
Quote Definition qf := Eval cbv in f.
Make Definition uqf := Eval cbv in qf.


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
Require Import Template.TemplateMonad.Core.

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


Definition test2 := (fun (T : Type@{i}) (T2 : Type@{j}) => T -> T2).
Set Printing Universes.
Print test.
(* Print Universes. *)
Unset Printing Universes. 

Quote Definition qtest := Eval compute in (fun (T : Type@{i}) (T2 : Type@{j}) => T -> T2).
Print qtest.

Make Definition bla := Eval compute in qtest.
Unset Strict Unquote Universe Mode.
Make Definition bla' := (tLambda (nNamed "T") (tSort ((Level.Level "Top.2", false) :: nil)%list) (tLambda (nNamed "T2") (tSort ((Level.Level "Top.1", false) :: nil)%list) (tProd nAnon (tRel 1) (tRel 1)))).

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
Make Definition T'2 := (tSort [(Level.Var 1, false)]).

Quote Recursively Definition qT' := F.

Quote Definition qFuntp := Eval compute in Funtp.
Print qFuntp.
(** the same thing is quoted in demo.v using the template-coq monad
there the poly vars actually show up *)


Make Definition t22 := (Ast.tLambda (Ast.nNamed "T") (Ast.tSort [(Level.Level "Top.10001", false)])
                                   (Ast.tLambda (Ast.nNamed "T2") (Ast.tSort [(Level.Level "Top.10002", false)]) (Ast.tProd Ast.nAnon (Ast.tRel 1) (Ast.tRel 1)))).
Set Printing Universes.
Print t2.
(* Print Universes. *)


Monomorphic Universe i1 j1.
Definition f' := (forall (A:Type@{i1}) (B: Type@{j1}), A -> B -> A).
(* : Type@{i1+1, j1+1} *)

Quote Recursively Definition ff := f'.
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
         let T := infer ([], init_graph) [] ((tProd (nNamed "A") (tSort [(Level.Level "Toto.85", false)]) (tProd (nNamed "B") (tSort [(Level.Level "Toto.86", false)]) (tProd nAnon (tRel 1) (tProd nAnon (tRel 1) (tRel 3)))))) in
         match T with
         | Checked (tSort [(Level.Level _, true); (Level.Level _, true)]) => true
         | _ => false
         end).
