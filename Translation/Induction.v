(* Induction principle on SAst *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast LiftSubst.
From Translation Require Import SAst.

Open Scope type_scope.

Inductive ForallT {A : Type} (P : A -> Type) : list A -> Type :=
| ForallT_nil : ForallT P []
| ForallT_cons x l : P x -> ForallT P l -> ForallT P (x :: l).

Definition sCaseBrsT (P : sterm -> Type) (brs : list (nat * sterm)) :=
  ForallT (fun x => P (snd x)) brs.

Lemma sterm_rect_list :
  forall P : sterm -> Type,
    (forall n : nat, P (sRel n)) ->
    (forall s : sort, P (sSort s)) ->
    (forall (nx : name) (A : sterm), P A -> forall B : sterm, P B -> P (sProd nx A B)) ->
    (forall (nx : name) (A : sterm), P A -> forall B : sterm, P B -> forall t : sterm, P t ->
       P (sLambda nx A B t)) ->
    (forall u : sterm, P u ->
     forall (nx : name) (A : sterm), P A ->
     forall B : sterm, P B ->
     forall v : sterm, P v ->
       P (sApp u nx A B v)) ->
    (forall A : sterm, P A -> forall u : sterm, P u -> forall v : sterm, P v -> P (sEq A u v)) ->
    (forall A : sterm, P A -> forall u : sterm, P u -> P (sRefl A u)) ->
    (forall A : sterm, P A ->
     forall u : sterm, P u ->
     forall P0 : sterm, P P0 ->
     forall w : sterm, P w ->
     forall v : sterm, P v ->
     forall p : sterm, P p ->
       P (sJ A u P0 w v p)) ->
    (forall T1 : sterm, P T1 ->
     forall T2 : sterm, P T2 ->
     forall p : sterm, P p ->
     forall t : sterm, P t ->
       P (sTransport T1 T2 p t)) ->
    (forall A : sterm, P A ->
     forall a : sterm, P a ->
     forall B : sterm, P B ->
     forall b : sterm, P b ->
       P (sHeq A a B b)) ->
    (forall p : sterm, P p -> P (sHeqToEq p)) ->
    (forall A : sterm, P A -> forall a : sterm, P a -> P (sHeqRefl A a)) ->
    (forall p : sterm, P p -> P (sHeqSym p)) ->
    (forall p : sterm, P p -> forall q : sterm, P q -> P (sHeqTrans p q)) ->
    (forall p : sterm, P p -> forall t : sterm, P t -> P (sHeqTransport p t)) ->
    (forall B1 : sterm, P B1 ->
     forall B2 : sterm, P B2 ->
     forall pA : sterm, P pA ->
     forall pB : sterm, P pB ->
       P (sCongProd B1 B2 pA pB)) ->
    (forall B1 : sterm, P B1 ->
     forall B2 : sterm, P B2 ->
     forall t1 : sterm, P t1 ->
     forall t2 : sterm, P t2 ->
     forall pA : sterm, P pA ->
     forall pB : sterm, P pB ->
     forall pt : sterm, P pt ->
       P (sCongLambda B1 B2 t1 t2 pA pB pt)) ->
    (forall B1 : sterm, P B1 ->
     forall B2 : sterm, P B2 ->
     forall pu : sterm, P pu ->
     forall pA : sterm, P pA ->
     forall pB : sterm, P pB ->
     forall pv : sterm, P pv ->
       P (sCongApp B1 B2 pu pA pB pv)) ->
    (forall pA : sterm, P pA -> forall pu : sterm, P pu -> forall pv : sterm, P pv ->
       P (sCongEq pA pu pv)) ->
    (forall pA : sterm, P pA -> forall pu : sterm, P pu -> P (sCongRefl pA pu)) ->
    (forall p : sterm, P p -> P (sEqToHeq p)) ->
    (forall p : sterm, P p -> P (sHeqTypeEq p)) ->
    (forall A1 : sterm, P A1 -> forall A2 : sterm, P A2 -> P (sPack A1 A2)) ->
    (forall p : sterm, P p -> P (sProjT1 p)) ->
    (forall p : sterm, P p -> P (sProjT2 p)) ->
    (forall p : sterm, P p -> P (sProjTe p)) ->
    (forall ind : inductive, P (sInd ind)) ->
    (forall (ind : inductive) (n : nat), P (sConstruct ind n)) ->
    (forall (indn : inductive * nat) (p : sterm), P p ->
     forall c : sterm, P c ->
     forall brs : list (nat * sterm), sCaseBrsT P brs ->
       P (sCase indn p c brs)) ->
    forall t : sterm, P t.
Proof.
  intros until t. revert t.
  fix auxt 1.
  move auxt at top.
  destruct t ;
  match goal with
  | H : _ |- _ => apply H
  end ; auto.
  revert brs.
  fix auxbrs' 1.
  destruct brs ; constructor ; [| apply auxbrs' ].
  apply auxt.
Defined.