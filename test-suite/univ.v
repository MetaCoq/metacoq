From MetaCoq.Template Require Import All.
Require Import String List Arith.
Import ListNotations MonadNotation.
Open Scope string.

Set Printing Universes.

MetaCoq Test Quote Type.
Quote Definition a_random_univ := Type.
(* 
Fail Make Definition t1 := (tSort ([]; _)).
Fail Make Definition t1 := (tSort (Universe.make (Level.Level "Top.400"))).

Monomorphic Definition T := Type.
(* Make Definition t1 := (tSort (Universe.make (Level.Level "Top.5"))). *)

Unset Strict Unquote Universe Mode.
Make Definition t2 := (tSort fresh_universe).
Make Definition t3 := (tSort (Universe.make (Level.Level "Top.400"))).


Monomorphic Universe i j.

Set Strict Unquote Universe Mode.
MetaCoq Test Quote (Type@{j} -> Type@{i}).
Make Definition T'' := (tSort (Universe.make (Level.Level "j"))).
Unset Strict Unquote Universe Mode.


Polymorphic Definition pidentity {A : Type} (a : A) := a.
MetaCoq Test Quote @pidentity.
Polymorphic Definition selfpid := pidentity (@pidentity).
MetaCoq Test Quote @selfpid.

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

Set Printing Universes.

Definition clean_universes_entry e :=
  match e with
  | Monomorphic_entry e => Monomorphic_entry e
  | Polymorphic_entry names e => Polymorphic_entry (map (fun x => nAnon) names) e
  end.

Definition clean_universes_decl (m : mutual_inductive_entry) : mutual_inductive_entry :=
  {| mind_entry_record := m.(mind_entry_record);
    mind_entry_finite := m.(mind_entry_finite);
    mind_entry_params := m.(mind_entry_params);
    mind_entry_inds := m.(mind_entry_inds);
    mind_entry_universes := clean_universes_entry m.(mind_entry_universes);
    mind_entry_variance := m.(mind_entry_variance);
    mind_entry_private := m.(mind_entry_private) |}.

Module to.
 Run TemplateProgram (t <- tmQuoteInductive "list" ;;
                     t <- tmEval all (mind_body_to_entry t) ;;
                     tmPrint t ;;
                     tmMkInductive (clean_universes_decl t)).
                     Print list.
End to.


Definition f@{i j k} := fun (E:Type@{i}) => Type@{max(i,j)}.
Quote Definition qf := Eval cbv in f.
Make Definition uqf := qf.


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

Require Import MetaCoq.Template.monad_utils. Import MonadNotation.
Require Import MetaCoq.Template.TemplateMonad.Core.

Run TemplateProgram (tmQuoteInductive "foo" >>= tmPrint).
Run TemplateProgram (tmQuoteInductive "foo2" >>= tmPrint).
Run TemplateProgram (tmQuoteInductive "foo3" >>= tmPrint).

Polymorphic Definition TT@{i j} : Type@{j} := Type@{i}.
Quote Recursively Definition qTT := TT.

Polymorphic Inductive TT2@{i j} : Type@{j} := tt2 : Type@{i} -> TT2.
Quote Recursively Definition qTT2 := TT2.

Require Import MetaCoq.Template.utils.
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

Make Definition bla := qtest.
Unset Strict Unquote Universe Mode.
Make Definition bla' := (tLambda (nNamed "T") (tSort (Universe.make (Level.Level "Top.46"))) (tLambda (nNamed "T2") (tSort (Universe.make (Level.Level "Top.477"))) (tProd nAnon (tRel 1) (tRel 1)))).

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

Make Definition t' := qt.

Polymorphic Definition Funtp@{i} (A B: Type@{i}) := A->B.

Polymorphic Definition F@{i} := Type@{i}.

Quote Definition qT := Eval compute in F.
Require Import List. Import ListNotations.
Fail Make Definition T'2 := (tSort [(Level.Var 1, false)]).

Quote Recursively Definition qT' := F.

Quote Definition qFuntp := Eval compute in Funtp.
Print qFuntp.
(** the same thing is quoted in demo.v using the template-coq monad
there the poly vars actually show up *)




Monomorphic Universe i1 j1.
Definition f' := (forall (A:Type@{i1}) (B: Type@{j1}), A -> B -> A).
(* : Type@{i1+1, j1+1} *)

Quote Recursively Definition ff := f'.

Require Import MetaCoq.Checker.All.
Compute (infer' (empty_ext (fst ff)) [] (snd ff)).
Check (eq_refl : infer' (empty_ext (fst ff)) [] (snd ff) =
         Checked (tSort (Universe.from_kernel_repr (Level.Level _, true) [(Level.Level _, true)]))).
Open Scope string_scope.
Check (eq_refl : infer [] init_graph [] ((tProd (nNamed "A") (tSort (Universe.make (Level.Level _))) (tProd (nNamed "B") (tSort (Universe.make (Level.Level _))) (tProd nAnon (tRel 1) (tProd nAnon (tRel 1) (tRel 3)))))) = Checked (tSort _)).

(* Make Definition t4 := (tSort (Universe.make (fresh_level))). *)
*)