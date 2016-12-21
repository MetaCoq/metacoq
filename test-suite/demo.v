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

Quote Recursively Definition plus_syntax := plus.

Quote Recursively Definition mult_syntax := mult.

Make Definition d''_from_syntax := ltac:(let t:= eval compute in d'' in exact t).




(** Reflecting  Inductives *)

Require Import List.
Import ListNotations.
Require Import Template.Ast.

Definition one_i : one_inductive_entry :=
{|
  mind_entry_typename := "demoBool";
  mind_entry_arity := tSort sSet;
  mind_entry_template := false;
  mind_entry_consnames := ["demoTrue"; "demoFalse"];
  mind_entry_lc := [tRel 1; tRel 1];
|}.

Definition one_i2 : one_inductive_entry :=
{|
  mind_entry_typename := "demoBool2";
  mind_entry_arity := tSort sSet;
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
  mind_entry_polymorphic := false;
  mind_entry_private := None;
|}.

Make Inductive mut_i.


Definition mkImpl (A B : term) : term :=
tProd nAnon A B.


Definition one_list_i : one_inductive_entry :=
{|
  mind_entry_typename := "demoList";
  mind_entry_arity := tSort sSet;
  mind_entry_template := false;
  mind_entry_consnames := ["demoNil"; "demoCons"];
  mind_entry_lc := [tApp (tRel 1) [tRel 0]; 
    mkImpl (tRel 0) (mkImpl (tApp (tRel 2) [tRel 1]) (tApp (tRel 3) [tRel 2]))];
|}.

Definition mut_list_i : mutual_inductive_entry :=
{|
  mind_entry_record := None;
  mind_entry_finite := Finite;
  mind_entry_params := [("A", LocalAssum (tSort sSet))];
  mind_entry_inds := [one_list_i];
  mind_entry_polymorphic := false;
  mind_entry_private := None;
|}.


Make Inductive mut_list_i.

(** Records *)

Definition one_pt_i : one_inductive_entry :=
{|
  mind_entry_typename := "Point";
  mind_entry_arity := tSort sSet;
  mind_entry_template := false;
  mind_entry_consnames := ["mkPoint"];
  mind_entry_lc := [
    mkImpl (tRel 0) (mkImpl (tRel 1) (tApp (tRel 3) [tRel 2]))];
|}.

Definition mut_pt_i : mutual_inductive_entry :=
{|
  mind_entry_record := Some (Some "pp");
  mind_entry_finite := BiFinite;
  mind_entry_params := [("A", LocalAssum (tSort sSet))];
  mind_entry_inds := [one_pt_i];
  mind_entry_polymorphic := false;
  mind_entry_private := None;
|}.

Make Inductive mut_pt_i.


(*
Inductive demoList (A : Set) : Set :=
    demoNil : demoList A | demoCons : A -> demoList A -> demoList A
*)



(** Putting the above commands in monadic program *)

Definition program : TemplateMonad unit :=
tmBind  
  (tmBind (tmReturn tt) (fun x => tmMkDefinition true "id2" d''))
  (fun x => tmMkDefinition true "id1" d'').

Run TemplateProgram program.

(*
id2 is defined
id1 is defined
*)

Fixpoint getFirstConstr (p:Ast.program) : option term :=
match p with
| PConstr _ t _ => Some t
| PType _ _ _ p => getFirstConstr p
| PAxiom _ t p => getFirstConstr p
| PIn _ => None
end.

Definition printTerm (name  : ident): TemplateMonad unit :=
  (tmBind (tmQuote name true) tmPrint)
    .

Definition duplicateDefn2 (name newName : ident): TemplateMonad unit :=
  (tmBind (tmQuote name false) (fun body => 
    match body with
    | Some (inl bd) => 
        (tmBind (tmPrint body) (fun _ => tmMkDefinition true newName bd))
    | _ => tmReturn tt
    end))
    .

Definition id := fun x:nat => x.

Locate id.
(* Fix: Top may not work in interactive use *)
Run TemplateProgram (printTerm "id"). 
Run TemplateProgram (duplicateDefn2 "Top.id" "id4").
Run TemplateProgram (printTerm "Coq.Init.Datatypes.nat").
Run TemplateProgram (printTerm "nat"). 
(*
(Some
   (inr
      {|
      mind_entry_record := None;
      mind_entry_finite := Finite;
      mind_entry_params := [];
      mind_entry_inds := [{|
                          mind_entry_typename := "nat";
                          mind_entry_arity := tSort sSet;
                          mind_entry_template := false;
                          mind_entry_consnames := ["O"; "S"];
                          mind_entry_lc := [tRel 0; tProd nAnon (tRel 0) (tRel 1)] |}];
      mind_entry_polymorphic := false;
      mind_entry_private := None |}))
*)

Run TemplateProgram (printTerm "demoList").
(*
(Some
   (inr
      {|
      mind_entry_record := None;
      mind_entry_finite := Finite;
      mind_entry_params := [("A", LocalAssum (tSort sSet))];
      mind_entry_inds := [{|
                          mind_entry_typename := "list";
                          mind_entry_arity := tSort sSet;
                          mind_entry_template := false;
                          mind_entry_consnames := ["nil"; "cons"];
                          mind_entry_lc := [tApp (tRel 1) [tRel 0];
                                           tProd nAnon (tRel 0)
                                             (tProd nAnon (tApp (tRel 2) [tRel 1])
                                                (tApp (tRel 3) [tRel 2]))] |}];
      mind_entry_polymorphic := false;
      mind_entry_private := None |}))
*)

Print demoList. (* exact same as above. So in this instance,
quoting was indded the inverse of unquoting*)

Run TemplateProgram
  ((tmBind (tmQuote "demoList" false) (fun body =>
    match body with
    | Some (inl bd)
    | Some (inr bd) =>
        tmMkDefinition false "demoList_syntax" bd
    | N_ => tmReturn tt
    end))
    ).
Print demoList_syntax.

Example unquote_quote_id1: demoList_syntax=mut_list_i 
  (* demoList was obtained from this *).
  reflexivity.
Qed.

Run TemplateProgram (printTerm "Coq.Arith.PeanoNat.Nat.add").
(* Names need not be canonical *)
Run TemplateProgram (printTerm "PeanoNat.Nat.add").
Run TemplateProgram (printTerm "add").

(*
(Some
   (inl
      (tFix
         [{|
          dname := nNamed "add";
          dtype := tProd (nNamed "a") (tInd (mkInd "Coq.Init.Datatypes.nat" 0))
                     (tProd (nNamed "b") (tInd (mkInd "Coq.Init.Datatypes.nat" 0))
                        (tInd (mkInd "Coq.Init.Datatypes.nat" 0)));
          dbody := tLambda (nNamed "a") (tInd (mkInd "Coq.Init.Datatypes.nat" 0))
                     (tLambda (nNamed "b") (tInd (mkInd "Coq.Init.Datatypes.nat" 0))
                        (tCase (mkInd "Coq.Init.Datatypes.nat" 0, 0)
                           (tLambda (nNamed "a") (tInd (mkInd "Coq.Init.Datatypes.nat" 0))
                              (tInd (mkInd "Coq.Init.Datatypes.nat" 0))) 
                           (tRel 1)
                           [(0, tRel 0);
                           (1,
                           tLambda (nNamed "a") (tInd (mkInd "Coq.Init.Datatypes.nat" 0))
                             (tApp (tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 1)
                                [tApp (tRel 3) [tRel 0; tRel 1]]))]));
          rarg := 0 |}] 0)))
*)