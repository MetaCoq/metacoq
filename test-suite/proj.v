From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

Set Primitive Projections.

Record Eq (A : Type) := { eq : A -> A -> bool; eq_proof : forall x y, eq x y = true <-> x = y }.

Record Sigma (A : Type) (B : A -> Type) : Type :=
  { fst : A ; snd : B fst }.
Arguments fst {A B}.
Arguments snd {A B}.

MetaCoq Quote Recursively Definition foo := (fst, snd).

Program Definition eqnat : Eq nat := {| eq x y := true |}.
Next Obligation. Admitted.

MetaCoq Quote Recursively Definition eqnatr := eqnat.

Goal forall {A} {e : Eq A} x y, e.(eq _) x y = eq _ e x y.
Proof.
  intros.
  match goal with
   |- ?T => quote_term T (fun x => pose (qgoal:=x))
  end.
  match goal with
    H:= context [Ast.tProj {| proj_ind := Kernames.mkInd _ 0; proj_npars := 1; proj_arg := 0 |} _] |- _ => idtac
  end.
  reflexivity.
Qed.

Record prod' A B : Type :=
  pair' { fst' : A ; snd' : B }.
Arguments fst' {A B} _.
Arguments snd' {A B} _.

MetaCoq Test Quote ((pair' _ _ true 4).(snd')).

MetaCoq Test Quote prod'.

Require Import List String.
Import ListNotations.


Definition qprod' := mkInd (MPfile ["proj"; "TestSuite"; "MetaCoq"], "prod'") 0.
Definition qnat := mkInd (MPfile ["Datatypes"; "Init"; "Stdlib"], "nat") 0.
Definition qbool := mkInd (MPfile ["Datatypes"; "Init"; "Stdlib"], "bool") 0.

MetaCoq Unquote Definition x := (tProj (mkProjection qprod' 2 1)
   (tApp (tConstruct qprod' 0 nil)
      [tInd qbool nil;
      tInd qnat nil;
      tConstruct qbool 0 nil;
      tApp (tConstruct qnat 1 nil)
        [tApp (tConstruct qnat 1 nil)
           [tApp (tConstruct qnat 1 nil)
              [tApp (tConstruct qnat 1 nil)
                 [tConstruct qnat 0 nil]]]]])).

Check (eq_refl : x = snd' {| fst' := true; snd' := 4 |}).
Check (eq_refl : x = 4).
