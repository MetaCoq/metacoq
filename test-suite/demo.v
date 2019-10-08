Require Import List Arith String.
Require Import MetaCoq.Template.All.
Import ListNotations MonadNotation.

Local Open Scope string_scope.

(** This is just printing **)
MetaCoq Test Quote (fun x : nat => x).

MetaCoq Test Quote (fun (f : nat -> nat) (x : nat) => f x).

MetaCoq Test Quote (let x := 2 in x).

MetaCoq Test Quote (let x := 2 in
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
MetaCoq Quote Definition d' := (fun x : nat => x).

(** To quote existing definitions **)
Definition id_nat : nat -> nat := fun x => x.

MetaCoq Quote Definition d'' := Eval compute in id_nat.
MetaCoq Quote Definition d3 := Eval cbn in id_nat.
MetaCoq Quote Definition d4 := Eval unfold id_nat in id_nat.


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

MetaCoq Quote Definition add_syntax := Eval compute in add.

MetaCoq Quote Definition eo_syntax := Eval compute in even.

MetaCoq Quote Definition add'_syntax := Eval compute in add'.

(** Reflecting definitions **)
MetaCoq Unquote Definition zero_from_syntax := (Ast.tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 0 []).

(* the function unquote_kn in reify.ml4 is not yet implemented *)
MetaCoq Unquote Definition add_from_syntax := add_syntax.

MetaCoq Unquote Definition eo_from_syntax := eo_syntax.
Print eo_from_syntax.

MetaCoq Unquote Definition two_from_syntax := (Ast.tApp (Ast.tConstruct (BasicAst.mkInd "Coq.Init.Datatypes.nat" 0) 1 nil)
   (Ast.tApp (Ast.tConstruct (BasicAst.mkInd "Coq.Init.Datatypes.nat" 0) 1 nil)
      (Ast.tConstruct (BasicAst.mkInd "Coq.Init.Datatypes.nat" 0) 0 nil :: nil) :: nil)).

MetaCoq Quote Recursively Definition plus_syntax := plus.

MetaCoq Quote Recursively Definition mult_syntax := mult.

MetaCoq Unquote Definition d''_from_syntax := d''.


(** Primitive Projections. *)

Set Primitive Projections.
Record prod' A B : Type :=
  pair' { fst' : A ; snd' : B }.
Arguments fst' {A B} _.
Arguments snd' {A B} _.

MetaCoq Test Quote ((pair' _ _ true 4).(snd')).
MetaCoq Unquote Definition x := (tProj (mkInd "prod'" 0, 2, 1)
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
  mind_entry_universes := Monomorphic_ctx (LevelSet.empty, ConstraintSet.empty);
  mind_entry_private := None;
|}.

MetaCoq Unquote Inductive mut_i.


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
  mind_entry_universes := Monomorphic_ctx (LevelSet.empty, ConstraintSet.empty);
  mind_entry_private := None;
|}.


MetaCoq Unquote Inductive mut_list_i.

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
  mind_entry_universes := Monomorphic_ctx (LevelSet.empty, ConstraintSet.empty);
  mind_entry_private := None;
|}.

MetaCoq Unquote Inductive mut_pt_i.


(*
Inductive demoList (A : Set) : Set :=
    demoNil : demoList A | demoCons : A -> demoList A -> demoList A
*)


(** Putting the above commands in monadic program *)
Notation inat :=
  {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |}.
MetaCoq Run (tmBind (tmQuote (3 + 3)) tmPrint).

MetaCoq Run (tmBind (tmQuoteRec add) tmPrint).

Definition printInductive (name  : ident): TemplateMonad unit :=
  (tmBind (tmQuoteInductive name) tmPrint).

MetaCoq Run (printInductive "Coq.Init.Datatypes.nat").
MetaCoq Run (printInductive "nat").

CoInductive cnat : Set :=  O :cnat | S : cnat -> cnat.
MetaCoq Run (printInductive "cnat").

MetaCoq Run (tmBind (tmQuoteConstant "add" false) tmPrint).
Fail MetaCoq Run (tmBind (tmQuoteConstant "nat" false) tmPrint).

Definition six : nat.
  exact (3 + 3).
Qed.
MetaCoq Run ((tmQuoteConstant "six" true) >>= tmPrint).
MetaCoq Run ((tmQuoteConstant "six" false) >>= tmPrint).

MetaCoq Run (t <- tmLemma "foo4" nat ;;
                     tmDefinition "foo5" (t + t + 2)).
Next Obligation.
  exact 3.
Defined.
Print foo5.


MetaCoq Run (t <- tmLemma "foo44" nat ;;
                     qt <- tmQuote t ;;
                     t <- tmEval all t ;;
                     tmPrint qt ;; tmPrint t).
Next Obligation.
  exact (3+2).
Defined.



(* MetaCoq Run (tmQuoteInductive "demoList" *)
(*                        >>= tmDefinition "demoList_syntax"). *)
(* Example unquote_quote_id1: demoList_syntax=mut_list_i *)
(* (* demoList was obtained from mut_list_i *). *)
(*   unfold demoList_syntax. *)
(*   unfold mut_list_i. *)
(*     f_equal. *)
(* Qed. *)

MetaCoq Run (tmDefinition "foo4'" nat >>= tmPrint).

(* We can chain the definition. In the following,
 foo5' = 12 and foo6' = foo5' *)
MetaCoq Run (t <- tmDefinition "foo5'" 12 ;;
                     tmDefinition "foo6'" t).

MetaCoq Run (tmLemma "foo51" nat ;;
                     tmLemma "foo61" bool).
Next Obligation.
  exact 3.
Defined.
Next Obligation.
  exact true.
Qed.




Definition printConstant (name  : ident): TemplateMonad unit :=
  X <- tmUnquote (tConst name []) ;;
  X' <- tmEval all (my_projT2 X) ;;
 tmPrint X'.

Fail MetaCoq Run (printInductive "Coq.Arith.PeanoNat.Nat.add").
MetaCoq Run (printConstant "Coq.Arith.PeanoNat.Nat.add").


(* Fail MetaCoq Run (tmUnquoteTyped (nat -> nat) add_syntax >>= *)
(*                           tmPrint). *)
MetaCoq Run (tmUnquoteTyped (nat -> nat -> nat) add_syntax >>=
                     tmPrint).




Inductive NonRec (A:Set) (C: A -> Set): Set := 
| SS : forall (f:A), C f -> NonRec A C.

MetaCoq Run (printInductive "NonRec").


Set Printing Universes.
Monomorphic Definition Funtm (A B: Type) := A->B.
Polymorphic Definition Funtp@{i} (A B: Type@{i}) := A->B.
(* MetaCoq Run (printConstant "Top.demo.Funtp"). *)
(* Locate Funtm. *)
(* MetaCoq Run (printConstant "Top.Funtm"). *)

Polymorphic Definition Funtp2@{i j} 
   (A: Type@{i}) (B: Type@{j}) := A->B.
(* MetaCoq Run (printConstant "Top.demo.Funtp2"). *) (* TODOO *)

MetaCoq Run (tmEval cbn add_syntax >>= tmMkDefinition "foo1").

MetaCoq Run ((tmFreshName "foo") >>= tmPrint).
MetaCoq Run (tmAxiom "foo0" (nat -> nat) >>= tmPrint).
MetaCoq Run (tmAxiom "foo0'" (nat -> nat) >>=
                     fun t => tmDefinition "foo0''" t).
MetaCoq Run (tmFreshName "foo" >>= tmPrint).

MetaCoq Run (tmBind (tmAbout "foo") tmPrint).
MetaCoq Run (tmBind (tmAbout "qlsnkqsdlfhkdlfh") tmPrint).
MetaCoq Run (tmBind (tmAbout "eq") tmPrint).
MetaCoq Run (tmBind (tmAbout "Logic.eq") tmPrint).
MetaCoq Run (tmBind (tmAbout "eq_refl") tmPrint).

MetaCoq Run (tmCurrentModPath tt >>= tmPrint).

MetaCoq Run (tmBind (tmEval all (3 + 3)) tmPrint).
MetaCoq Run (tmBind (tmEval hnf (3 + 3)) tmPrint).

Fail MetaCoq Run (tmFail "foo" >>= tmQuoteInductive).


(* Definition duplicateDefn (name newName : ident): TemplateMonad unit := *)
(*   (tmBind (tmQuote name false) (fun body => *)
(*     match body with *)
(*     | Some (inl (DefinitionEntry {| definition_entry_body := bd |})) => *)
(*         (tmBind (tmPrint body) (fun _ => tmMkDefinition newName bd)) *)
(*     | _ => tmReturn tt *)
(*     end)) *)
(*     . *)

(* MetaCoq Run (duplicateDefn "add" "addUnq"). *)
(* Check (eq_refl: add=addUnq). *)



(** Universes *)

Set Printing Universes.
MetaCoq Test Quote Type.
MetaCoq Test Quote Set.
MetaCoq Test Quote Prop.

Inductive T : Type :=
  | toto : Type -> T.
MetaCoq Quote Recursively Definition TT := T.

Unset Strict Unquote Universe Mode.
MetaCoq Unquote Definition t := (tSort (NEL.sing (Level.Level "Top.20000", false))).
MetaCoq Unquote Definition t' := (tSort fresh_universe).
MetaCoq Unquote Definition myProp := (tSort (Universe.make' (Level.lProp, false))).
MetaCoq Unquote Definition myProp' := (tSort Universe.type0m).
MetaCoq Unquote Definition mySet := (tSort (Universe.make Level.lSet)).

(** Cofixpoints *)
CoInductive streamn : Set :=
  scons : nat -> streamn -> streamn.

CoFixpoint ones : streamn := scons 1 ones.

MetaCoq Quote Definition ones_syntax := Eval compute in ones.

MetaCoq Unquote Definition ones' := ones_syntax.

Check eq_refl : ones = ones'.


(* Too long *)
(* MetaCoq Run (tmQuoteUniverses tt >>= tmDefinition "universes"). *)
(* Print universes. *)
(* Definition tyu := Eval vm_compute in universes. *)


Definition kername_of_qualid (q : qualid) : TemplateMonad kername :=
  gr <- tmAbout q ;;
  match gr with
  | Some (ConstRef kn)  => ret kn
  | Some (IndRef ind) => ret ind.(inductive_mind)
  | Some (ConstructRef ind _) => ret ind.(inductive_mind)
  | None => tmFail  ("tmLocate: " ++ q ++ " not found")
  end.

MetaCoq Run (kername_of_qualid "add" >>= tmPrint).
MetaCoq Run (kername_of_qualid "BinNat.N.add" >>= tmPrint).
MetaCoq Run (kername_of_qualid "Coq.NArith.BinNatDef.N.add" >>= tmPrint).
Fail MetaCoq Run (kername_of_qualid "N.add" >>= tmPrint).
Fail MetaCoq Run (kername_of_qualid "qlskf" >>= tmPrint).
