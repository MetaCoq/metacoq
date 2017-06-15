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

Make Definition zero_from_syntax := (Ast.tConstruct (Ast.mkInd "Coq.Init.Datatypes.nat" 0) 0).

Make Definition eo_from_syntax := 
ltac:(let t:= eval compute in eo_syntax in exact t).
Print eo_from_syntax.

Make Definition two_from_syntax := (Ast.tApp (Ast.tConstruct (Ast.mkInd "Coq.Init.Datatypes.nat" 0) 1 nil)
   (Ast.tApp (Ast.tConstruct (Ast.mkInd "Coq.Init.Datatypes.nat" 0) 1 nil)
      (Ast.tConstruct (Ast.mkInd "Coq.Init.Datatypes.nat" 0) 0 nil :: nil) :: nil)).

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

Definition printTerm (name  : ident): TemplateMonad unit :=
  (tmBind (tmQuote name true) tmPrint).

Definition duplicateDefn (name newName : ident): TemplateMonad unit :=
  (tmBind (tmQuote name false) (fun body => 
    match body with
    | Some (inl bd) => 
        (tmBind (tmPrint body) (fun _ => tmMkDefinition true newName bd))
    | _ => tmReturn tt
    end))
    .



Run TemplateProgram (duplicateDefn "add" "addUnq").
Check (eq_refl: add=addUnq).

Run TemplateProgram (printTerm "Coq.Init.Datatypes.nat").
Run TemplateProgram (printTerm "nat"). 

CoInductive cnat : Set :=  O :cnat | S : cnat -> cnat.
Run TemplateProgram (printTerm "cnat"). 

Run TemplateProgram
  ((tmBind (tmQuote "demoList" false) (fun body =>
    match body with
    | Some (inl bd)
    | Some (inr bd) =>
        tmMkDefinition false "demoList_syntax" bd
    | N_ => tmReturn tt
    end))
    ).

Print demoList.

Definition demoConsType := ltac:(let T := type of demoCons in exact T).
Run TemplateProgram (printTerm "nat"). 
(*
None
*)

Run TemplateProgram (printTerm "demoConsType"). 
(*
(Some
   (inl
      (tProd (nNamed "A") (tSort sSet)
         (tCast
            (tProd nAnon (tRel 0)
               (tCast
                  (tProd nAnon (tApp (tInd (mkInd "Top.demoList" 0)) [tRel 1])
                     (tCast (tApp (tInd (mkInd "Top.demoList" 0)) [tRel 2]) Cast
                        (tSort sSet))) Cast (tSort sSet))) Cast 
            (tSort sSet)))))
*)

Example unquote_quote_id1: demoList_syntax=mut_list_i (* demoList was obtained from mut_list_i *).
  unfold demoList_syntax.
  unfold mut_list_i.
    f_equal.
    f_equal.
    unfold one_list_i.
    f_equal.
    f_equal.
    f_equal.
    unfold mkImpl.
    f_equal.
Abort. (* extra cast *)

Run TemplateProgram (printTerm "Coq.Arith.PeanoNat.Nat.add").
Inductive NonRec (A:Set) (C: A -> Set): Set := 
| SS : forall (f:A), C f -> NonRec A C.

Run TemplateProgram (printTerm "NonRec").

Monomorphic Definition Funtm (A B: Type) := A->B.
Polymorphic Definition Funtp@{i} (A B: Type@{i}) := A->B.
Run TemplateProgram (printTerm "Top.Funtp").
Run TemplateProgram (printTerm "Top.Funtm").

Polymorphic Definition Funtp2@{i j} 
   (A: Type@{i}) (B: Type@{j}) := A->B.

Run TemplateProgram (printTerm "Top.Funtp2").

(*(Some
   (inl
      (tLambda (nNamed "A") (tSort (sType "Var(0)"))
         (tLambda (nNamed "B") (tSort (sType "Var(1)"))
            (tProd nAnon (tRel 1) (tRel 1))))))
*)





