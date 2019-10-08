Require Import Recdef.
Require Import Coq.omega.Omega.
Require Import Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Import ListNotations.

Require Import MetaCoq.Template.All.
Require Import MetaCoq.Checker.All.

Unset Template Cast Propositions.

MetaCoq Quote Recursively Definition idq := @Coq.Classes.Morphisms.Proper.

Existing Instance config.default_checker_flags.
Existing Instance Checker.default_fuel.

Eval vm_compute in typecheck_program idq.

Definition timpl x y := tProd nAnon x (LiftSubst.lift0 1 y).

MetaCoq Quote Recursively Definition four := (2 + 2).
Unset Printing Matching.

Ltac typecheck := try red; cbn; intros;
  match goal with
    |- ?Σ ;;; ?Γ |- ?t : ?T =>
    refine (infer_correct Σ _ _ Γ t T _ _); [reflexivity|constructor|vm_compute; reflexivity]
  end.
Ltac infer := try red;
  match goal with
    |- ?Σ ;;; ?Γ |- ?t : ?T =>
    refine (infer_correct Σ _ _ Γ t T _ _); [reflexivity|constructor|
      let t' := eval vm_compute in (infer' Σ Γ t) in
          change (t' = Checked T); reflexivity]
  end.

MetaCoq Quote Definition natr := nat.

Definition type_program (p : program) (ty : term) :=
  let Σ := empty_ext (fst p) in
  Σ ;;; [] |- snd p : ty.

Example typecheck_four : type_program four natr:= ltac:(typecheck).

Goal { ty & type_program four ty }.
Proof.
  eexists. infer.
Qed.

(* Uase template-coq to make a [program] from function defined above *)

(* Eval native_compute in typecheck_program p_Plus1. *)

Definition test_reduction (p : program) :=
    let Σ := empty_ext (fst p) in
    reduce (fst Σ) [] (snd p).

Definition string_of_env_error e :=
  match e with
  | IllFormedDecl s e => ("IllFormedDecl " ++ s ++ "\nType error: " ++ string_of_type_error e)%string
  | AlreadyDeclared s => ("Alreadydeclared " ++ s)%string
  end.

Definition out_typing c :=
  match c with
  | Checked t => t
  | TypeError e => tVar ("Typing error")%string
  end.

Definition out_check c :=
  match c with
  | CorrectDecl t => t
  | EnvError e => tVar ("Check error: " ++ string_of_env_error e)%string
  end.

Ltac interp_red c :=
  let t:= eval vm_compute in (out_typing (test_reduction c)) in exact t.

Ltac interp_infer c :=
  let t:= eval vm_compute in (out_check (typecheck_program c)) in exact t.

Ltac term_type c :=
  let X := type of c in exact X.

Ltac quote_type c :=
  let X := type of c in
  quote_term X ltac:(fun Xast => exact Xast).

Notation convertible x y := (@eq_refl _ x : x = y).

Module Test1.
  Definition term := (Nat.mul 2 62).
  Load "test_term.v".
End Test1.

Module Test2.
  Definition term := (fun (f : nat -> nat) (x : nat) => f (f x)).
  Load "test_term.v".
End Test2.

Module Test3.
  (* Definition term := (id 0). *)
  (* Load "test_term.v". *)
End Test3.

Module Test4.
  Definition term := @id.
  Set Printing Universes.
  Load "test_term.v".
End Test4.

Module Test5.

  (** A function defined using measure or well-founded relation **)
  Function Plus1 (n: nat) {measure id n} : nat :=
    match n with
    | 0 => 1
    | S p => S (Plus1 p)
    end.
  - intros. unfold id. abstract omega.
  Defined.

  (* Time Template Check Plus1. *)
  (* Time Template Check Coq.ZArith.BinInt.Z.succ_pred. (* -> 16 s *) *)
  (* MetaCoq Quote Recursively Definition plop := Coq.ZArith.BinInt.Z.succ_pred. *)
  (* Eval native_compute in (typecheck_program plop). (* -> 31 min!! *) *)


  (* (* Too long with universes on *) *)
  (* MetaCoq Quote Recursively Definition p_Plus1 := Plus1. *)
  
  (* Definition term := Plus1. *)
  (* Definition ast := p_Plus1. *)
  (* Set Printing Universes. *)
  (* (** Check typing *) *)
  
  (* (* Yay! Typechecking an actually non-trivial term. (173s) *) *)
 
  (* Make Definition inferred_type := ltac:(interp_infer ast). *)
  (* Definition inferred_type' := Eval cbv delta in inferred_type. *)
  (* Print inferred_type'. *)
  (* Check convertible ltac:(term_type term) inferred_type. *)
End Test5.

Universe i j.

Definition f1 := (forall (A:Type@{i}) (B: Prop), A -> B -> A).
(* : Type@{Set+1, i+1} *)

Definition f2 := (forall (A:Type@{i}) (B: Prop), A -> B -> B).
(* : Prop *)

MetaCoq Quote Definition f1' := (forall (A:Type@{i}) (B: Prop), A -> B -> A). 

Eval lazy in infer' (empty_ext []) nil f1'.

MetaCoq Quote Definition f2' := (forall (A:Type@{i}) (B: Prop), A -> B -> B). 

Eval lazy in infer' (empty_ext []) nil f2'.

Definition f := (forall (A:Type@{i}) (B: Type@{j}), A -> B -> A).
(* : Type@{i+1, j+1} *)

MetaCoq Quote Definition f' := (forall (A:Type@{i}) (B:Type@{j}), A -> B -> A). 

MetaCoq Quote Definition f'' := (forall (B: Type@{j}), B -> B). 

Eval lazy in infer' (empty_ext []) nil f'.
