(* -*- coq-prog-args: ("-top" "TemplateTestSuite.demo") -*-  *)

Require Import List Arith.
Require Import Template.monad_utils Template.Ast Template.Template.
Import ListNotations MonadNotation.

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
Eval vm_compute in add.

Fixpoint add' (a b : nat) : nat :=
  match b with
    | 0 => a
    | S b => S (add' a b)
  end.

Fixpoint even (a : nat) : bool :=
  match a with
    | 0 => true
    | S a => odd a
  end
with odd (a : nat) : bool :=
  match a with
    | 0 => false
    | S a => even a
  end.

Quote Definition add_syntax := Eval compute in add.

Quote Definition eo_syntax := Eval compute in even.

Quote Definition add'_syntax := Eval compute in add'.


(** Reflecting definitions **)
Make Definition zero_from_syntax := (Ast.tConstruct (Ast.mkInd "Coq.Init.Datatypes.nat" 0) 0 []).

(* the function unquote_kn in reify.ml4 is not yet implemented *)
Make Definition add_from_syntax := ltac:(let t:= eval compute in add_syntax in exact t).

Make Definition eo_from_syntax :=
ltac:(let t:= eval compute in eo_syntax in exact t).
Print eo_from_syntax.

Make Definition two_from_syntax := (Ast.tApp (Ast.tConstruct (Ast.mkInd "Coq.Init.Datatypes.nat" 0) 1 nil)
   (Ast.tApp (Ast.tConstruct (Ast.mkInd "Coq.Init.Datatypes.nat" 0) 1 nil)
      (Ast.tConstruct (Ast.mkInd "Coq.Init.Datatypes.nat" 0) 0 nil :: nil) :: nil)).

Quote Recursively Definition plus_synax := plus.

Quote Recursively Definition mult_syntax := mult.

Make Definition d''_from_syntax := ltac:(let t:= eval compute in d'' in exact t).


(** Primitive Projections. *)

Set Primitive Projections.
Record prod' A B : Type :=
  pair' { fst' : A ; snd' : B }.
Arguments fst' {A B} _.
Arguments snd' {A B} _.

Test Quote ((pair' _ _ true 4).(snd')).
Make Definition x := (tProj (mkInd "prod'" 0, 2, 1)
   (tApp (tConstruct (mkInd "prod'" 0) 0 nil)
      [tInd (mkInd "Coq.Init.Datatypes.bool" 0) nil;
      tInd (mkInd "Coq.Init.Datatypes.nat" 0) nil;
      tConstruct (mkInd "Coq.Init.Datatypes.bool" 0) 0 nil;
      tApp (tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 1 nil)
        [tApp (tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 1 nil)
           [tApp (tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 1 nil)
              [tApp (tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 1 nil)
                 [tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 0 nil]]]]])).


(** Reflecting  Inductives *)

Definition one_i : one_inductive_entry :=
{|
  mind_entry_typename := "demoBool";
  mind_entry_arity := tSort Universe.type0;
  mind_entry_template := false;
  mind_entry_consnames := ["demoTrue"; "demoFalse"];
  mind_entry_lc := [tRel 1; tRel 1];
|}.

Definition one_i2 : one_inductive_entry :=
{|
  mind_entry_typename := "demoBool2";
  mind_entry_arity := tSort Universe.type0;
  mind_entry_template := false;
  mind_entry_consnames := ["demoTrue2"; "demoFalse2"];
  mind_entry_lc := [tRel 0; tRel 0];
|}.

Definition mut_i : mutual_inductive_entry :=
{|
  mind_entry_record := None;
  mind_entry_finite := Finite;
  mind_entry_params := [];
  mind_entry_inds := [one_i; one_i2];
  mind_entry_universes := Monomorphic_ctx ([], ConstraintSet.empty);
  mind_entry_private := None;
|}.

Make Inductive mut_i.


Definition mkImpl (A B : term) : term :=
tProd nAnon A B.


Definition one_list_i : one_inductive_entry :=
{|
  mind_entry_typename := "demoList";
  mind_entry_arity := tSort Universe.type0;
  mind_entry_template := false;
  mind_entry_consnames := ["demoNil"; "demoCons"];
  mind_entry_lc := [tApp (tRel 1) [tRel 0]; 
    mkImpl (tRel 0) (mkImpl (tApp (tRel 2) [tRel 1]) (tApp (tRel 3) [tRel 2]))];
|}.

Definition mut_list_i : mutual_inductive_entry :=
{|
  mind_entry_record := None;
  mind_entry_finite := Finite;
  mind_entry_params := [("A", LocalAssum (tSort Universe.type0))];
  mind_entry_inds := [one_list_i];
  mind_entry_universes := Monomorphic_ctx ([], ConstraintSet.empty);
  mind_entry_private := None;
|}.


Make Inductive mut_list_i.

(** Records *)

Definition one_pt_i : one_inductive_entry :=
{|
  mind_entry_typename := "Point";
  mind_entry_arity := tSort Universe.type0;
  mind_entry_template := false;
  mind_entry_consnames := ["mkPoint"];
  mind_entry_lc := [
    mkImpl (tRel 0) (mkImpl (tRel 1) (tApp (tRel 3) [tRel 2]))];
|}.

Definition mut_pt_i : mutual_inductive_entry :=
{|
  mind_entry_record := Some (Some "pp");
  mind_entry_finite := BiFinite;
  mind_entry_params := [("A", LocalAssum (tSort Universe.type0))];
  mind_entry_inds := [one_pt_i];
  mind_entry_universes := Monomorphic_ctx ([], ConstraintSet.empty);
  mind_entry_private := None;
|}.

Make Inductive mut_pt_i.


(*
Inductive demoList (A : Set) : Set :=
    demoNil : demoList A | demoCons : A -> demoList A -> demoList A
*)


(** Putting the above commands in monadic program *)

Run TemplateProgram (tmBind (tmQuote (3 + 3)) tmPrint).

Run TemplateProgram (tmBind (tmQuoteRec add) tmPrint).

Definition printInductive (name  : ident): TemplateMonad unit :=
  (tmBind (tmQuoteInductive name) tmPrint).

Run TemplateProgram (printInductive "Coq.Init.Datatypes.nat").
Run TemplateProgram (printInductive "nat").

CoInductive cnat : Set :=  O :cnat | S : cnat -> cnat.
Run TemplateProgram (printInductive "cnat").

Run TemplateProgram (tmBind (tmQuoteConstant "add" false) tmPrint).
Fail Run TemplateProgram (tmBind (tmQuoteConstant "nat" false) tmPrint).

Definition six : nat.
  exact (3 + 3).
Qed.
Run TemplateProgram ((tmQuoteConstant "six" true) >>= tmPrint).
Run TemplateProgram ((tmQuoteConstant "six" false) >>= tmPrint).


Run TemplateProgram (t <- tmLemma "foo4" nat ;;
                     tmDefinition "foo5" (t + t + 2)).
Next Obligation.
  exact 3.
Defined.
Print foo5.
Fail Definition tttt : _ := _.


Run TemplateProgram (t <- tmLemma "foo44" nat ;;
                     qt <- tmQuote t ;;
                     t <- tmEval all t ;;
                     tmPrint qt ;; tmPrint t).
Next Obligation.
  exact (3+2).
Defined.



(* Run TemplateProgram (tmQuoteInductive "demoList" *)
(*                        >>= tmDefinition "demoList_syntax"). *)
(* Example unquote_quote_id1: demoList_syntax=mut_list_i *)
(* (* demoList was obtained from mut_list_i *). *)
(*   unfold demoList_syntax. *)
(*   unfold mut_list_i. *)
(*     f_equal. *)
(* Qed. *)

Run TemplateProgram (tmDefinition "foo4'" nat >>= tmPrint).

(* We can chain the definition. In the following,
 foo5' = 12 and foo6' = foo5' *)
Run TemplateProgram (t <- tmDefinition "foo5'" 12 ;;
                       tmDefinition "foo6'" t).

Obligation Tactic := idtac.

Run TemplateProgram (tmLemma "foo51" nat;;
                     tmLemma "foo61" bool).
Next Obligation.
  exact 3.
Defined.
Next Obligation.
  exact true.
Qed.



Definition printConstant (name  : ident): TemplateMonad unit :=
  X <- tmUnquote (tConst name []) ;;
  X' <- tmEval all (projT2 X) ;;
 tmPrint X'.

Fail Run TemplateProgram (printInductive "Coq.Arith.PeanoNat.Nat.add").
Run TemplateProgram (printConstant "Coq.Arith.PeanoNat.Nat.add").


(* Fail Run TemplateProgram (tmUnquoteTyped (nat -> nat) add_syntax >>= *)
(*                           tmPrint). *)
Run TemplateProgram (tmUnquoteTyped (nat -> nat -> nat) add_syntax >>=
                     tmPrint).




Inductive NonRec (A:Set) (C: A -> Set): Set := 
| SS : forall (f:A), C f -> NonRec A C.

Run TemplateProgram (printInductive "NonRec").


Set Printing Universes.
Monomorphic Definition Funtm (A B: Type) := A->B.
Polymorphic Definition Funtp@{i} (A B: Type@{i}) := A->B.
Run TemplateProgram (printConstant "TemplateTestSuite.demo.Funtp").
Run TemplateProgram (printConstant "TemplateTestSuite.demo.Funtm").

Polymorphic Definition Funtp2@{i j} 
   (A: Type@{i}) (B: Type@{j}) := A->B.
Run TemplateProgram (printConstant "TemplateTestSuite.demo.Funtp2").


Definition tmDefinition' : ident -> forall {A}, A -> TemplateMonad unit
  := fun id A t => tmDefinition id t ;; tmReturn tt.

(** A bit less efficient, but does the same job as tmMkDefinition *)
Definition tmMkDefinition' : ident -> term -> TemplateMonad unit
  := fun id t => x <- tmUnquote t ;;
              x' <- tmEval all (projT2 x) ;;
              tmDefinition' id x'.

Run TemplateProgram (tmMkDefinition' "foo" add_syntax).
Run TemplateProgram (tmMkDefinition "foo1" add_syntax).

Run TemplateProgram ((tmFreshName "foo") >>= tmPrint).
Run TemplateProgram (tmAxiom "foo0" (nat -> nat) >>= tmPrint).
Run TemplateProgram (tmAxiom "foo0'" (nat -> nat) >>=
                     fun t => tmDefinition' "foo0''" t).
Run TemplateProgram (tmFreshName "foo" >>= tmPrint).

Run TemplateProgram (tmBind (tmAbout "foo") tmPrint).
Run TemplateProgram (tmBind (tmAbout "qlsnkqsdlfhkdlfh") tmPrint).
Run TemplateProgram (tmBind (tmAbout "eq") tmPrint).
Run TemplateProgram (tmBind (tmAbout "Logic.eq") tmPrint).
Run TemplateProgram (tmBind (tmAbout "eq_refl") tmPrint).

Run TemplateProgram (tmCurrentModPath tt >>= tmPrint).

Run TemplateProgram (tmBind (tmEval all (3 + 3)) tmPrint).
Run TemplateProgram (tmBind (tmEval hnf (3 + 3)) tmPrint).

Fail Run TemplateProgram (tmFail "foo" >>= tmQuoteInductive).


(* Definition duplicateDefn (name newName : ident): TemplateMonad unit := *)
(*   (tmBind (tmQuote name false) (fun body => *)
(*     match body with *)
(*     | Some (inl (DefinitionEntry {| definition_entry_body := bd |})) => *)
(*         (tmBind (tmPrint body) (fun _ => tmMkDefinition newName bd)) *)
(*     | _ => tmReturn tt *)
(*     end)) *)
(*     . *)

(* Run TemplateProgram (duplicateDefn "add" "addUnq"). *)
(* Check (eq_refl: add=addUnq). *)



(** Universes *)

Set Printing Universes.
Test Quote Type.
Test Quote Set.
Test Quote Prop.

Inductive T : Type :=
  | toto : Type -> T.
Quote Recursively Definition TT := T.
Make Definition t := (tSort ([(Level.Level "Top.20000", false)])).
Make Definition t' := (tSort ([(Level.Level "Top.20000", false); (Level.Level "Top.20001", true)])).
Make Definition myProp := (tSort [(Level.lProp, false)]).
Make Definition myProp' := Eval compute in (tSort Universe.type0m).
Make Definition mySucProp := (tSort [(Level.lProp, true)]).
Make Definition mySet := (tSort [(Level.lSet, false)]).

(** Cofixpoints *)
CoInductive streamn : Set :=
  scons : nat -> streamn -> streamn.

CoFixpoint ones : streamn := scons 1 ones.

Quote Definition ones_syntax := Eval compute in ones.

Make Definition ones' := Eval compute in ones_syntax.

Check eq_refl : ones = ones'.


(* Too long *)
(* Run TemplateProgram (tmQuoteUniverses tt >>= tmDefinition "universes"). *)
(* Print universes. *)
(* Definition tyu := Eval vm_compute in universes. *)
(* Check (universes : uGraph.t). *)
