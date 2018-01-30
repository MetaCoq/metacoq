Require Import Recdef.
Require Import Coq.omega.Omega.
Require Import Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Import ListNotations.

Require Import Template.TemplateCoqChecker.
Require Import Template.Typing.
Require Import Template.Checker.
Require Import Template.Ast.
Require Import Template.Template.

Quote Recursively Definition idq := @Coq.Classes.Morphisms.Proper.

Eval vm_compute in typecheck_program idq.

Unset Template Cast Propositions.

Definition timpl x y := tProd nAnon x (LiftSubst.lift0 1 y).

Quote Recursively Definition four := (2 + 2).
Unset Printing Matching.

Ltac typecheck := cbn; intros; constructor;
  match goal with
    |- ?Σ ;;; ?Γ |- ?t : ?T =>
    eapply (infer_correct Σ Γ t T); vm_compute; reflexivity
  end.
Ltac infer := cbn; intros; constructor;
  match goal with
    |- ?Σ ;;; ?Γ |- ?t : ?T =>
    eapply (infer_correct Σ Γ t T);
      let t' := eval vm_compute in (infer Σ Γ t) in
          change (t' = Checked T); reflexivity
  end.

Example typecheck_four : type_program four natr := ltac:(typecheck).

Goal exists ty, type_program four ty.
Proof.
  eexists. infer.
Qed.

(* Uase template-coq to make a [program] from function defined above *)

(* Eval native_compute in typecheck_program p_Plus1. *)

Definition test_reduction (p : program) :=
    let '(Σ, t) := decompose_program p ([], init_graph) in
    reduce (fst Σ) [] t.

Definition string_of_env_error e :=
  match e with
  | IllFormedDecl s _ => ("IllFormedDecl " ++ s)%string
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
  Definition term := (id 0).
  Load "test_term.v".
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

  Time Template Check Plus1.
  (* Too long  *)
  Quote Recursively Definition p_Plus1 := Plus1.
  
  Definition term := Plus1.
  Definition ast := p_Plus1.
  Set Printing Universes.
  (** Check typing *)
  
  (* Yay! Typechecking an actually non-trivial term. (173s) *)
 
  Make Definition inferred_type := ltac:(interp_infer ast).
  Definition inferred_type' := Eval cbv delta in inferred_type.
  Print inferred_type'.
  Check convertible ltac:(term_type term) inferred_type.
End Test5.

