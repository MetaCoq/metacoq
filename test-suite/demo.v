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

Require Import Template.Ast.
Require Import List.
Import ListNotations.


(*

Inductive nat_R : nat -> nat -> Set :=
    nat_R_O_R : nat_R 0 0
  | nat_R_S_R : forall H H0 : nat,
                nat_R H H0 -> nat_R (S H) (S H0)

By snooping on the paramcoq plugin (using coq/dev/top_printer.ml)
when it created the above translation for nat,
The two entries of mind_entry_lc were determined to be:


App(Rel(1),[|MutConstruct((Coq.Init.Datatypes.nat,0),,1);MutConstruct((Coq.Init.Datatypes.nat,0),,1)|])

Prod(Anonymous,MutInd(Coq.Init.Datatypes.nat,0,),Prod(Anonymous,MutInd(Coq.Init.Datatypes.nat,0,),Prod(Anonymous,App(Rel(3),[|Rel(2);Rel(1)|])
,App(Rel(4),[|App(MutConstruct((Coq.Init.Datatypes.nat,0),,2),[|Rel(3)|])
;App(MutConstruct((Coq.Init.Datatypes.nat,0),,2),[|Rel(2)|])
|])
)
)
)

*)

Definition one_i : one_inductive_entry :=
{|
  mind_entry_typename := "demoBool";
  mind_entry_arity := tSort sSet;
  mind_entry_template := false;
  mind_entry_consnames := ["demoTrue"; "demoFalse"];
  mind_entry_lc := [tRel 0; tRel 0];
|}.

Definition mut_i : mutual_inductive_entry :=
{|
  mind_entry_record := None;
  mind_entry_params := [];
  mind_entry_inds := [one_i];
  mind_entry_polymorphic := false;
  mind_entry_private := None;
|}.




Make Inductive dummy := ltac:(let t:= eval compute in mut_i in exact t).

Print demoBool.

(*
Inductive demoBool : Set :=  demoTrue : demoBool | demoFalse : demoBool
*)




(** Another way **)
Quote Definition d' := (fun x : nat => x).

(** To quote existing definitions **)
Definition id_nat : nat -> nat := fun x => x.

Quote Definition d'' := Eval compute in id_nat.

Print d''.

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
Quote Definition natq := nat.
Print natq.
Quote Recursively Definition plus_syntax := plus.

Print plus_syntax.


Make Definition addss := ltac:(let t:= eval compute in d'' in exact t).




(* the name Falsssss is ignored *)
Print demoInd.
(*
Inductive demoInd : Prop :=  
*)


Quote Definition add'_syntax := Eval compute in add'.

(** Reflecting definitions **)

Make Definition zero_from_syntax := (Ast.tConstruct (Ast.mkInd "Coq.Init.Datatypes.nat" 0) 0).



Make Definition two_from_syntax := (Ast.tApp (Ast.tConstruct (Ast.mkInd "Coq.Init.Datatypes.nat" 0) 1)
   (Ast.tApp (Ast.tConstruct (Ast.mkInd "Coq.Init.Datatypes.nat" 0) 1)
      (Ast.tConstruct (Ast.mkInd "Coq.Init.Datatypes.nat" 0) 0 :: nil) :: nil)).


Quote Recursively Definition mult_syntax := mult.
