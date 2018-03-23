(* Quotations of terms *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast LiftSubst Typing Checker Template.
(* From Translation Require Import SAst SLiftSubst SCommon ITyping. *)

Definition J (A : Type) (u : A) (P : forall (x : A), u = x -> Type)
           (w : P u (@eq_refl A u)) (v : A) (p : u = v) : P v p :=
  match p with
  | eq_refl => w
  end.

Definition transport {T1 T2 : Type} (p : T1 = T2) (t : T1) : T2 :=
  J Type T1 (fun X e => T1 -> X) (fun x => x) T2 p t.

Axiom K : forall {A} {x : A} (p : x = x), p = eq_refl.
Axiom funext : forall {A B} {f g : forall (x : A), B x}, (forall x, f x = g x) -> f = g.

Quote Definition tEq := @eq.
Quote Definition tRefl := @eq_refl.
Quote Definition tJ := J.
Quote Definition tTransport := @transport.
Quote Definition tK := @K.
Quote Definition tFunext := @funext.

Definition mkEq (A u v : term) : term :=
  tApp tEq [ A ; u ; v ].

Definition mkRefl (A u : term) : term :=
  tApp tRefl [A ; u].

Definition mkJ (A u P w v p : term) : term :=
  tApp tJ [ A ; u ; P ; w ; v ; p ].

Definition mkTransport (T1 T2 p t : term) : term :=
  tApp tTransport [ T1 ; T2 ; p ; t ].

Definition mkK (A u p : term) : term :=
  tApp tK [ A ; u ; p ].

Definition mkFunext (A B f g e : term) : term :=
  tApp tFunext [ A ; B ; f ; g ; e ].

Inductive heq {A} (a : A) {B} (b : B) :=
  heqPair (p : A = B) (e : transport p a = b).

Notation "A ≅ B" := (heq A B) (at level 20).

Lemma heq_to_eq :
  forall {A} {u v : A},
    u ≅ v -> u = v.
Proof.
  intros A u v h.
  destruct h as [e p].
  assert (e = eq_refl) by (apply K). subst.
  reflexivity.
Defined.

Lemma heq_refl : forall {A} (a : A), a ≅ a.
Proof.
  intros A a.
  exists eq_refl.
  reflexivity.
Defined.

Lemma heq_sym :
  forall {A} (a : A) {B} (b : B),
    a ≅ b -> b ≅ a.
Proof.
  intros A a B b h.
  destruct h as [p e].
  destruct p. simpl in e.
  exists eq_refl. now symmetry.
Defined.

Lemma heq_trans :
  forall {A} (a : A) {B} (b : B) {C} (c : C),
    a ≅ b -> b ≅ c -> a ≅ c.
Proof.
  intros A a B b C c e1 e2.
  destruct e1 as [p1 e1]. destruct e2 as [p2 e2].
  destruct p1. destruct p2.
  exists eq_refl. simpl in *.
  now transitivity b.
Defined.

Lemma heq_transport :
  forall {T T'} (p : T = T') (t : T),
    t ≅ transport p t.
Proof.
  intros T T' p t.
  exists p. reflexivity.
Defined.

Record Pack A1 A2 := pack {
  ProjT1 : A1 ;
  ProjT2 : A2 ;
  ProjTe : ProjT1 ≅ ProjT2
}.

Arguments pack {_ _} _ _ _.
Arguments ProjT1 {_ _} _.
Arguments ProjT2 {_ _} _.
Arguments ProjTe {_ _} _.

Lemma cong_prod :
  forall (A1 A2 : Type) (B1 : A1 -> Type) (B2 : A2 -> Type),
    A1 ≅ A2 ->
    (forall (p : Pack A1 A2), B1 (ProjT1 p) ≅ B2 (ProjT2 p)) ->
    (forall x, B1 x) ≅ (forall y, B2 y).
Proof.
  intros A1 A2 B1 B2 hA hB.
  exists eq_refl. simpl.
  destruct hA as [pT pA]. rewrite (K pT) in pA.
  simpl in pA. clear pT. destruct pA. rename A1 into A.
  assert (pB : B1 = B2).
  { apply funext. intro x.
    destruct (hB (pack x x (heq_refl x))) as [pT pB]. cbn in pB.
    rewrite (K pT) in pB. simpl in pB. clear pT.
    exact pB.
  }
  now destruct pB.
Defined.

Lemma cong_lambda :
  forall (A1 A2 : Type) (B1 : A1 -> Type) (B2 : A2 -> Type)
    (f1 : forall x, B1 x) (f2 : forall x, B2 x),
    A1 ≅ A2 ->
    (forall (p : Pack A1 A2), B1 (ProjT1 p) ≅ B2 (ProjT2 p)) ->
    (forall (p : Pack A1 A2), f1 (ProjT1 p) ≅ f2 (ProjT2 p)) ->
    (fun x => f1 x) ≅ (fun x => f2 x).
Proof.
  intros A1 A2 B1 B2 f1 f2 pA hB hf.
  destruct pA as [pT pA].
  rewrite (K pT) in pA. simpl in pA. clear pT.
  destruct pA. rename A1 into A.
  assert (pB : B1 = B2).
  { apply funext. intro x.
    destruct (hB (pack x x (heq_refl x))) as [pT pB].
    rewrite (K pT) in pB. simpl in pB. clear pT.
    exact pB.
  }
  destruct pB. rename B1 into B. clear hB.
  exists eq_refl. simpl.
  apply funext. intro x.
  destruct (hf (pack x x (heq_refl x))) as [p pf].
  now rewrite (K p) in pf.
Defined.

Lemma cong_app :
  forall (A1 A2 : Type) (B1 : A1 -> Type) (B2 : A2 -> Type)
    (f1 : forall x, B1 x) (f2 : forall x, B2 x)
    (u1 : A1) (u2 : A2),
    A1 ≅ A2 ->
    (forall (p : Pack A1 A2), B1 (ProjT1 p) ≅ B2 (ProjT2 p)) ->
    f1 ≅ f2 ->
    u1 ≅ u2 ->
    f1 u1 ≅ f2 u2.
Proof.
  intros A1 A2 B1 B2 f1 f2 u1 u2 pA hB pf pu.
  destruct pA as [pT pA].
  rewrite (K pT) in pA. simpl in pA. clear pT.
  destruct pA. rename A1 into A.
  assert (pB : B1 = B2).
  { apply funext. intro x.
    destruct (hB (pack x x (heq_refl x))) as [pT pB].
    rewrite (K pT) in pB. simpl in pB. clear pT.
    exact pB.
  }
  destruct pB. rename B1 into B. clear hB.
  destruct pf as [p pf].
  rewrite (K p) in pf. simpl in pf. clear p.
  destruct pf. rename f1 into f.
  destruct pu as [p pu].
  rewrite (K p) in pu. simpl in pu. clear p.
  destruct pu. rename u1 into u.
  now apply heq_refl.
Defined.

Lemma cong_eq :
  forall (A1 A2 : Type) (u1 v1 : A1) (u2 v2 : A2),
    A1 ≅ A2 -> u1 ≅ u2 -> v1 ≅ v2 -> (u1 = v1) ≅ (u2 = v2).
Proof.
  intros A1 A2 u1 v1 u2 v2 pA pu pv.
  destruct pA as [pT pA].
  rewrite (K pT) in pA. simpl in pA. clear pT.
  destruct pA. rename A1 into A.
  destruct pu as [pA pu].
  rewrite (K pA) in pu. simpl in pu. clear pA.
  destruct pu. rename u1 into u.
  destruct pv as [pA pv].
  rewrite (K pA) in pv. simpl in pv. clear pA.
  destruct pv. rename v1 into v.
  apply heq_refl.
Defined.

Lemma cong_refl :
  forall (A1 A2 : Type) (u1 : A1) (u2 : A2),
    A1 ≅ A2 ->
    u1 ≅ u2 ->
    @eq_refl A1 u1 ≅ @eq_refl A2 u2.
Proof.
  intros A1 A2 u1 u2 pA pu.
  destruct pA as [pT pA].
  rewrite (K pT) in pA. simpl in pA. clear pT.
  destruct pA. rename A1 into A.
  destruct pu as [pA pu].
  rewrite (K pA) in pu. simpl in pu. clear pA.
  destruct pu.
  now apply heq_refl.
Defined.

Lemma eq_to_heq :
  forall {A} {u v : A},
    u = v -> u ≅ v.
Proof.
  intros A u v p.
  exists eq_refl. exact p.
Defined.

Lemma heq_type_eq :
  forall {A} {u : A} {B} {v : B},
    u ≅ v -> A = B.
Proof.
  intros A u B v e.
  now destruct e.
Defined.

Quote Definition tHeq := @heq.
Quote Definition tHeqToEq := @heq_to_eq.
Quote Definition tHeqRefl := @heq_refl.
Quote Definition tHeqSym := @heq_sym.
Quote Definition tHeqTrans := @heq_trans.
Quote Definition tHeqTransport := @heq_transport.
Quote Definition tPack := @Pack.
Quote Definition tProjT1 := @ProjT1.
Quote Definition tProjT2 := @ProjT2.
Quote Definition tProjTe := @ProjTe.
Quote Definition tCongProd := @cong_prod.
Quote Definition tCongLambda := @cong_lambda.
Quote Definition tCongApp := @cong_app.
Quote Definition tCongEq := @cong_eq.
Quote Definition tCongRefl := @cong_refl.
Quote Definition tEqToHeq := @eq_to_heq.
Quote Definition tHeqTypeEq := @heq_type_eq.

Definition mkHeq (A a B b : term) : term :=
  tApp tHeq [ A ; a ; B ; b ].

Definition mkHeqToHeq (A u v p : term) : term :=
  tApp tHeqToEq [ A ; u ; v ; p ].

Definition mkHeqRefl (A a : term) : term :=
  tApp tHeqRefl [ A ; a ].

Definition mkHeqSym (A a B b p : term) : term :=
  tApp tHeqSym [ A ; a ; B ; b ; p ].

Definition mkHeqTrans (A a B b C c p q : term) : term :=
  tApp tHeqTrans [ A ; a ; B ; b ; C ; c ; p ; q ].

Definition mkHeqTransport (A B p t : term) : term :=
  tApp tHeqTransport [ A ; B ; p ; t ].

Definition mkPack (A1 A2 : term) : term :=
  tApp tPack [ A1 ; A2 ].

Definition mkProjT1 (A1 A2 p : term) : term :=
  tApp tProjT1 [ A1 ; A2 ; p ].

Definition mkProjT2 (A1 A2 p : term) : term :=
  tApp tProjT2 [ A1 ; A2 ; p ].

Definition mkProjTe (A1 A2 p : term) : term :=
  tApp tProjTe [ A1 ; A2 ; p ].

Definition mkCongProd (A1 A2 B1 B2 pA pB : term) :=
  tApp tCongProd [
    A1 ;
    A2 ;
    (tLambda nAnon A1 B1) ;
    (tLambda nAnon A2 B2) ;
    pA ;
    (tLambda nAnon (mkPack A1 A2) pB)
  ].

Definition mkCongLambda (A1 A2 B1 B2 t1 t2 pA pB pt : term) :=
  tApp tCongProd [
    A1 ;
    A2 ;
    (tLambda nAnon A1 B1) ;
    (tLambda nAnon A2 B2) ;
    (tLambda nAnon A1 t1) ;
    (tLambda nAnon A2 t2) ;
    pA ;
    (tLambda nAnon (mkPack A1 A2) pB) ;
    (tLambda nAnon (mkPack A1 A2) pt)
  ].

Definition mkCongApp (A1 A2 B1 B2 t1 t2 u1 u2 pA pB pt pu : term) :=
  tApp tCongProd [
    A1 ;
    A2 ;
    (tLambda nAnon A1 B1) ;
    (tLambda nAnon A2 B2) ;
    t1 ;
    t2 ;
    u1 ;
    u2 ;
    pA ;
    (tLambda nAnon (mkPack A1 A2) pB) ;
    pt ;
    pu
  ].

Definition mkCongEq (A1 A2 u1 v1 u2 v2 pA pu pv : term) : term :=
  tApp tCongEq [ A1 ; A2 ; u1 ; v1 ; u2 ; v2 ; pA ; pu ; pv ].

Definition mkCongRefl (A1 A2 u1 u2 pA pu : term) : term :=
  tApp tCongRefl [ A1 ; A2 ; u1 ; u2 ; pA ; pu ].

Definition mkEqToHeq (A u v p : term) : term :=
  tApp tEqToHeq [ A ; u ; v ; p ].

Definition mkHeqTypeEq (A u B v p : term) : term :=
  tApp tHeqTypeEq [ A ; u ; B ; v ; p ].


(* For examples *)

Inductive vec A : nat -> Type :=
| vnil : vec A 0
| vcons : A -> forall n, vec A n -> vec A (S n).

Arguments vnil {_}.
Arguments vcons {_} _ _ _.