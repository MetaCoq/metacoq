From Coq Require Import List Bool Arith ssreflect Program Lia.
From MetaCoq.Template Require Import MCList MCRelations MCProd MCOption.

Import ListNotations.

Local Ltac inv H := inversion_clear H.
Local Coercion is_true : bool >-> Sortclass.


(** Combinators *)

(** Forall combinators in Type to allow building them by recursion *)
Inductive All {A} (P : A -> Type) : list A -> Type :=
    All_nil : All P []
  | All_cons : forall (x : A) (l : list A),
                  P x -> All P l -> All P (x :: l).
Arguments All_nil {_ _}.
Arguments All_cons {_ _ _ _}.

Inductive Alli {A} (P : nat -> A -> Type) (n : nat) : list A -> Type :=
| Alli_nil : Alli P n []
| Alli_cons hd tl : P n hd -> Alli P (S n) tl -> Alli P n (hd :: tl).
Arguments Alli_nil {_ _ _}.
Arguments Alli_cons {_ _ _ _ _}.

Inductive All2 {A B : Type} (R : A -> B -> Type) : list A -> list B -> Type :=
  All2_nil : All2 R [] []
| All2_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
    R x y -> All2 R l l' -> All2 R (x :: l) (y :: l').
Arguments All2_nil {_ _ _}.
Arguments All2_cons {_ _ _ _ _ _ _}.

Section Forallb2.
  Context {A} (f : A -> A -> bool).

  Fixpoint forallb2 l l' :=
    match l, l' with
    | hd :: tl, hd' :: tl' => f hd hd' && forallb2 tl tl'
    | [], [] => true
    | _, _ => false
    end.

End Forallb2.

Lemma forallb2_refl :
  forall A (R : A -> A -> bool),
    (forall x, R x x) ->
    forall l, forallb2 R l l.
Proof.
  intros A R R_refl l.
  induction l.
  - reflexivity.
  - simpl. rewrite R_refl. assumption.
Qed.

Lemma forallb2_map :
  forall A B (R : A -> A -> bool) f g (l : list B) (l' : list B),
    forallb2 (fun x y => R (f x) (g y)) l l' ->
    forallb2 R (map f l) (map g l').
Proof.
  intros A B R f g l l' h.
  induction l in l', h |- *.
  - destruct l'. 2: discriminate. reflexivity.
  - destruct l'. 1: discriminate. simpl in *.
    apply andb_true_iff in h as [e1 e2]. rewrite e1. simpl.
    eapply IHl. assumption.
Qed.

Lemma forall_map_spec {A B} {l} {f g : A -> B} :
  Forall (fun x => f x = g x) l <->
  map f l = map g l.
Proof.
  split.
  induction 1; simpl; trivial.
  now rewrite IHForall H.
  induction l => /= // [=] Ha Hl; constructor; auto.
Qed.

Lemma forall_map_id_spec {A} {l} {f : A -> A} :
  Forall (fun x => f x = x) l <-> map f l = l.
Proof.
  rewrite -{3}(map_id l). apply forall_map_spec.
Qed.

Lemma forallb_Forall {A} (p : A -> bool) l
  : Forall p l <-> is_true (forallb p l).
Proof.
  split.
  induction 1; rewrite /= // H IHForall //.
  induction l; rewrite /= //. move/andP => [pa pl].
  constructor; auto.
Qed.


Lemma map_eq_inj {A B} (f g : A -> B) l: map f l = map g l ->
                                         All (fun x => f x = g x) l.
Proof.
  induction l. simpl. constructor. simpl. intros [=]. constructor; auto.
Qed.

(** Generic strategy for dealing with Forall/forall, etc:

    1) Move all boolean foralls into All/All2 (in the goal and the context).
    2) Merge all context Foralls into one
    3) Apply Forall implication
    4) optionally simplify and call eauto.
*)

Lemma Forall_mix {A} (P Q : A -> Prop) : forall l, Forall P l -> Forall Q l -> Forall (fun x => P x /\ Q x) l.
Proof.
  intros l Hl Hq. induction Hl; inv Hq; constructor; auto.
Qed.

Lemma Forall_skipn {A} (P : A -> Prop) n l : Forall P l -> Forall P (skipn n l).
Proof.
  intros H. revert n; induction H; intros n. rewrite skipn_nil; auto.
  destruct n; simpl.
  - rewrite /skipn. constructor; auto.
  - now auto.
Qed.

Lemma Forall_firstn {A} (P : A -> Prop) n l : Forall P l -> Forall P (firstn n l).
Proof.
  intros H. revert n; induction H; intros n. rewrite firstn_nil; auto.
  destruct n; simpl.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma forallb2_All2 {A : Type} {p : A -> A -> bool}
      {l l' : list A} :
  is_true (forallb2 p l l') -> All2 (fun x y => is_true (p x y)) l l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; intros; try congruence.
  - constructor.
  - constructor. revert H; rewrite andb_and; intros [px pl]. auto.
    apply IHl. revert H; rewrite andb_and; intros [px pl]. auto.
Qed.

Lemma All2_forallb2 {A : Type} {p : A -> A -> bool}
      {l l' : list A} :
  All2 (fun x y => is_true (p x y)) l l' -> is_true (forallb2 p l l').
Proof.
  induction 1; simpl; intros; try congruence.
  rewrite andb_and. intuition auto.
Qed.

Lemma forallb2_app {A} (p : A -> A -> bool) l l' q q' :
  is_true (forallb2 p l l' && forallb2 p q q')
  -> is_true (forallb2 p (l ++ q) (l' ++ q')).
Proof.
  induction l in l' |- *; destruct l'; simpl; try congruence.
  move=> /andP[/andP[pa pl] pq]. now rewrite pa IHl // pl pq.
Qed.

Lemma All2_map {A B C D} (R : C -> D -> Type) (f : A -> C) (g : B -> D) l l' :
  All2 (fun x y => R (f x) (g y)) l l' -> All2 R (map f l) (map g l').
Proof. induction 1; simpl; constructor; try congruence. Qed.

Lemma All2_map_inv {A B C D} (R : C -> D -> Type) (f : A -> C) (g : B -> D) l l' :
  All2 R (map f l) (map g l') -> All2 (fun x y => R (f x) (g y)) l l'.
Proof. induction l in l' |- *; destruct l'; simpl;
         move=> H;inv H; try constructor; try congruence. eauto.
Qed.

(* Lemma All2_List_Forall_mix_left {A : Type} {P : A -> Prop} {Q : A -> A -> Prop} *)
(*       {l l' : list A} : *)
(*     Forall P l -> All2 Q l l' -> All2 (fun x y => P x /\ Q x y) l l'. *)
(* Proof. *)
(*   induction 2; simpl; intros; constructor. *)
(*   inv H; intuition auto. *)
(*   apply IHX. inv H; intuition auto. *)
(* Qed. *)

(* Lemma All2_List_Forall_mix_right {A : Type} {P : A -> Prop} {Q : A -> A -> Prop} *)
(*       {l l' : list A} : *)
(*     Forall P l' -> All2 Q l l' -> All2 (fun x y => P y /\ Q x y) l l'. *)
(* Proof. *)
(*   induction 2; simpl; intros; constructor. *)
(*   inv H; intuition auto. *)
(*   apply IHX. inv H; intuition auto. *)
(* Qed. *)

Lemma All2_All_mix_left {A B} {P : A -> Type} {Q : A -> B -> Type}
      {l : list A} {l' : list B} :
  All P l -> All2 Q l l' -> All2 (fun x y => (P x * Q x y)%type) l l'.
Proof.
  induction 2; simpl; intros; constructor.
  inv X; intuition auto.
  apply IHX0. inv X; intuition auto.
Qed.

Lemma All2_All_mix_right {A B} {P : B -> Type} {Q : A -> B -> Type}
      {l : list A} {l' : list B} :
  All P l' -> All2 Q l l' -> All2 (fun x y => (Q x y * P y)%type) l l'.
Proof.
  induction 2; simpl; intros; constructor.
  inv X; intuition auto.
  apply IHX0. inv X; intuition auto.
Qed.

Lemma Forall_All {A : Type} (P : A -> Prop) l :
  Forall P l -> All P l.
Proof.
  induction l; intros H; constructor; auto. inv H. auto.
  apply IHl. inv H; auto.
Qed.

Lemma All_Forall {A : Type} (P : A -> Prop) l :
  All P l -> Forall P l.
Proof. induction 1; constructor; auto. Qed.

Lemma forallb_All {A} (p : A -> bool) l : is_true (forallb p l) -> All p l.
Proof.
  move/forallb_Forall. apply Forall_All.
Qed.

Lemma All_forallb {A} (p : A -> bool) l : All p l -> is_true (forallb p l).
Proof.
  move/All_Forall. apply forallb_Forall.
Qed.

Lemma All_firstn {A} {P : A -> Type} {l} {n} : All P l -> All P (firstn n l).
Proof. intros HPL; induction HPL in n |- * ; simpl; destruct n; try econstructor; eauto. Qed.

Lemma All_skipn {A} {P : A -> Type} {l} {n} : All P l -> All P (skipn n l).
Proof. intros HPL; induction HPL in n |- * ; simpl; destruct n; try econstructor; eauto. Qed.

Lemma All_app {A} {P : A -> Type} {l l'} : All P (l ++ l') -> All P l * All P l'.
Proof.
  induction l; simpl; auto. intros. constructor; auto. constructor.
  intros. inv X. intuition auto. constructor; auto.
Qed.

Lemma All_app_inv {A} (P : A -> Type) l l' : All P l -> All P l' -> All P (l ++ l').
Proof.
  intros Hl Hl'. induction Hl. apply Hl'.
  constructor; intuition auto.
Qed.

Lemma All_mix {A} {P : A -> Type} {Q : A -> Type} {l} :
  All P l -> All Q l -> All (fun x => (P x * Q x)%type) l.
Proof. induction 1; intros Hq; inv Hq; constructor; auto. Qed.

Lemma All2_All_left {A B} {P : A -> B -> Type} {Q : A -> Type} {l l'} :
  All2 P l l' ->
  (forall x y, P x y -> Q x) ->
  All Q l.
Proof.
  intros HF H. induction HF; constructor; eauto.
Qed.

Lemma All2_All_right {A B} {P : A -> B -> Type} {Q : B -> Type} {l l'} :
  All2 P l l' ->
  (forall x y, P x y -> Q y) ->
  All Q l'.
Proof.
  intros HF H. induction HF; constructor; eauto.
Qed.

Lemma All2_right {A B} {P : B -> Type} {l : list A} {l'} :
  All2 (fun x y => P y) l l' -> All P l'.
Proof.
  induction 1; constructor; auto.
Qed.

Hint Constructors All All2 : core.

Lemma All_rev_map {A B} (P : A -> Type) f (l : list B) : All (compose P f) l -> All P (rev_map f l).
Proof. induction 1. constructor. rewrite rev_map_cons. apply All_app_inv; auto. Qed.

Lemma All_rev (A : Type) (P : A -> Type) (l : list A) : All P l -> All P (List.rev l).
Proof.
  induction l using rev_ind. constructor. rewrite rev_app_distr.
  simpl. intros X; apply All_app in X as [? ?]. depelim a0; intuition auto.
Qed.

Lemma All_rev_inv {A} (P : A -> Type) (l : list A) : All P (List.rev l) -> All P l.
Proof.
  induction l using rev_ind. constructor.
  intros. rewrite rev_app_distr in X. simpl.
  apply All_app in X as [Allx Alll]. inv Allx.
   apply All_app_inv; intuition eauto.
Qed.

Lemma All_impl {A} {P Q} {l : list A} : All P l -> (forall x, P x -> Q x) -> All Q l.
Proof. induction 1; try constructor; intuition auto. Qed.

Lemma Alli_impl {A} {P Q} (l : list A) {n} : Alli P n l -> (forall n x, P n x -> Q n x) -> Alli Q n l.
Proof. induction 1; try constructor; intuition auto. Defined.

Lemma All_map {A B} {P : B -> Type} {f : A -> B} {l : list A} :
  All (compose P f) l -> All P (map f l).
Proof. induction 1; constructor; auto. Qed.

Lemma All_map_inv {A B} (P : B -> Prop) (f : A -> B) l : All P (map f l) -> All (compose P f) l.
Proof. induction l; intros Hf; inv Hf; try constructor; eauto. Qed.

Lemma All_nth_error :
  forall A P l i x,
    @All A P l ->
    nth_error l i = Some x ->
    P x.
Proof.
  intros A P l i x h e.
  induction h in i, x, e |- *.
  - destruct i. all: discriminate.
  - destruct i.
    + simpl in e. inversion e. subst. clear e.
      assumption.
    + simpl in e. eapply IHh in e.
      assumption.
Qed.

Lemma Alli_mix {A} {P : nat -> A -> Type} {Q : nat -> A -> Type} {n l} :
  Alli P n l -> Alli Q n l -> Alli (fun n x => (P n x * Q n x)%type) n l.
Proof. induction 1; intros Hq; inv Hq; constructor; auto. Qed.

Lemma Alli_All {A} {P : nat -> A -> Type} {Q : A -> Type} {l n} :
  Alli P n l ->
  (forall n x, P n x -> Q x) ->
  All Q l.
Proof. induction 1; constructor; eauto. Qed.

Lemma Alli_app {A} (P : nat -> A -> Type) n l l' : Alli P n (l ++ l') -> Alli P n l * Alli P (length l + n) l'.
Proof.
  induction l in n, l' |- *; intros H. split; try constructor. apply H.
  inversion_clear H. split; intuition auto. constructor; auto. eapply IHl; eauto.
  simpl. replace (S (#|l| + n)) with (#|l| + S n) by lia.
  eapply IHl; eauto.
Qed.

Lemma Alli_nth_error :
  forall A P k l i x,
    @Alli A P k l ->
    nth_error l i = Some x ->
    P (k + i) x.
Proof.
  intros A P k l i x h e.
  induction h in i, x, e |- *.
  - destruct i. all: discriminate.
  - destruct i.
    + simpl in e. inversion e. subst. clear e.
      replace (n + 0) with n by lia.
      assumption.
    + simpl in e. eapply IHh in e.
      replace (n + S i) with (S n + i) by lia.
      assumption.
Qed.

Lemma forall_nth_error_All :
  forall {A} (P : A -> Type) l,
    (forall i x, nth_error l i = Some x -> P x) ->
    All P l.
Proof.
  intros A P l h.
  induction l.
  - constructor.
  - constructor.
    + specialize (h 0 a eq_refl). assumption.
    + eapply IHl. intros i x e. eapply (h (S i)). assumption.
Qed.

Lemma forall_nth_error_Alli :
  forall {A} (P : nat -> A -> Type) k l,
    (forall i x, nth_error l i = Some x -> P (k + i) x) ->
    Alli P k l.
Proof.
  intros A P k l h.
  induction l in k, h |- *.
  - constructor.
  - constructor.
    + specialize (h 0 a eq_refl). now rewrite Nat.add_0_r in h.
    + apply IHl. intros. specialize (h (S i) x H).
      simpl. now replace (S (k + i)) with (k + S i) by lia.
Qed.

Lemma Alli_mapi {A B} {P : nat -> B -> Type} (f : nat -> A -> B) k l :
  CRelationClasses.iffT (Alli (fun n a => P n (f n a)) k l)
                        (Alli P k (mapi_rec f l k)).
Proof.
  split.
  { induction 1. simpl. constructor.
    simpl. constructor; eauto. }
  { induction l in k |- *. simpl. constructor.
    simpl. intros. depelim X. constructor; eauto. }
Qed.

Lemma Alli_shift {A} {P : nat -> A -> Type} k l :
  Alli (fun x => P (S x)) k l ->
  Alli P (S k) l.
Proof.
  induction 1; simpl; constructor; auto.
Qed.

Lemma Alli_rev {A} {P : nat -> A -> Type} k l :
  Alli P k l ->
  Alli (fun k' => P (pred #|l| - k' + k)) 0 (List.rev l).
Proof.
  revert k.
  induction l using rev_ind; simpl; intros; try constructor.
  eapply Alli_app in X. intuition.
  rewrite rev_app_distr. rewrite app_length.
  simpl. constructor.
  replace (pred (#|l| + 1) - 0) with #|l| by lia.
  depelim b. eauto. specialize (IHl _ a).
  eapply Alli_shift. eapply Alli_impl. eauto.
  simpl; intros.
  now replace (pred (#|l| + 1) - S n) with (pred #|l| - n) by lia.
Qed.

Lemma Alli_All_mix {A} {P : nat -> A -> Type} (Q : A -> Type) k l :
  Alli P k l -> All Q l -> Alli (fun k x => (P k x) * Q x)%type k l.
Proof.
  induction 1; constructor; try depelim X0; intuition auto.
Qed.


Inductive OnOne2 {A : Type} (P : A -> A -> Type) : list A -> list A -> Type :=
| OnOne2_hd hd hd' tl : P hd hd' -> OnOne2 P (hd :: tl) (hd' :: tl)
| OnOne2_tl hd tl tl' : OnOne2 P tl tl' -> OnOne2 P (hd :: tl) (hd :: tl').

Lemma OnOne2_All_mix_left {A} {P : A -> A -> Type} {Q : A -> Type} {l l'} :
  All Q l -> OnOne2 P l l' -> OnOne2 (fun x y => (P x y * Q x)%type) l l'.
Proof.
  intros H; induction 1; constructor; try inv H; intuition.
Qed.

Lemma OnOne2_app {A} (P : A -> A -> Type) l tl tl' : OnOne2 P tl tl' -> OnOne2 P (l ++ tl) (l ++ tl').
Proof. induction l; simpl; try constructor; auto. Qed.

Lemma OnOne2_length {A} {P} {l l' : list A} : OnOne2 P l l' -> #|l| = #|l'|.
Proof. induction 1; simpl; congruence. Qed.

Lemma OnOne2_mapP {A B} {P} {l l' : list A} (f : A -> B) :
  OnOne2 (on_rel P f) l l' -> OnOne2 P (map f l) (map f l').
Proof. induction 1; simpl; constructor; try congruence. apply p. Qed.

Lemma OnOne2_map {A B} {P : B -> B -> Type} {l l' : list A} (f : A -> B) :
  OnOne2 (on_Trel P f) l l' -> OnOne2 P (map f l) (map f l').
Proof. induction 1; simpl; constructor; try congruence. apply p. Qed.

Lemma OnOne2_sym {A} (P : A -> A -> Type) l l' : OnOne2 (fun x y => P y x) l' l -> OnOne2 P l l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma OnOne2_exist {A} (P : A -> A -> Type) (Q : A -> A -> Type) l l' :
  OnOne2 P l l' ->
  (forall x y, P x y -> ∑ z, Q x z × Q y z) ->
  ∑ r, (OnOne2 Q l r × OnOne2 Q l' r).
Proof.
  intros H HPQ. induction H.
  - destruct (HPQ _ _ p). destruct p0.
    now exists (x :: tl); intuition constructor.
               - destruct IHOnOne2 as [r [? ?]].
                 now exists (hd :: r); intuition constructor.
Qed.

(* Induction principle on OnOne2 when the relation also depends
     on one of the lists, and should not change.
   *)
Lemma OnOne2_ind_l :
  forall A (R : list A -> A -> A -> Type)
    (P : forall L l l', OnOne2 (R L) l l' -> Type),
    (forall L x y l (r : R L x y), P L (x :: l) (y :: l) (OnOne2_hd _ _ _ l r)) ->
    (forall L x l l' (h : OnOne2 (R L) l l'),
        P L l l' h ->
        P L (x :: l) (x :: l') (OnOne2_tl _ x _ _ h)
    ) ->
    forall l l' h, P l l l' h.
Proof.
  intros A R P hhd htl l l' h. induction h ; eauto.
Qed.

Lemma OnOne2_impl_exist_and_All :
  forall A (l1 l2 l3 : list A) R1 R2 R3,
    OnOne2 R1 l1 l2 ->
    All2 R2 l3 l2 ->
    (forall x x' y, R1 x y -> R2 x' y -> ∑ z : A, R3 x z × R2 x' z) ->
    ∑ l4, OnOne2 R3 l1 l4 × All2 R2 l3 l4.
Proof.
  intros A l1 l2 l3 R1 R2 R3 h1 h2 h.
  induction h1 in l3, h2 |- *.
  - destruct l3.
    + inversion h2.
    + inversion h2. subst.
    specialize (h _ _ _ p X) as hh.
    destruct hh as [? [? ?]].
    eexists. constructor.
      * constructor. eassumption.
      * constructor ; eauto.
  - destruct l3.
    + inversion h2.
    + inversion h2. subst.
    specialize (IHh1 _ X0). destruct IHh1 as [? [? ?]].
    eexists. constructor.
      * eapply OnOne2_tl. eassumption.
      * constructor ; eauto.
Qed.

Lemma OnOne2_impl_exist_and_All_r :
  forall A (l1 l2 l3 : list A) R1 R2 R3,
    OnOne2 R1 l1 l2 ->
    All2 R2 l2 l3 ->
    (forall x x' y, R1 x y -> R2 y x' -> ∑ z : A, R3 x z × R2 z x') ->
    ∑ l4, ( OnOne2 R3 l1 l4 × All2 R2 l4 l3 ).
Proof.
  intros A l1 l2 l3 R1 R2 R3 h1 h2 h.
  induction h1 in l3, h2 |- *.
  - destruct l3.
    + inversion h2.
    + inversion h2. subst.
      specialize (h _ _ _ p X) as hh.
      destruct hh as [? [? ?]].
      eexists. split.
      * constructor. eassumption.
      * constructor ; eauto.
  - destruct l3.
    + inversion h2.
    + inversion h2. subst.
      specialize (IHh1 _ X0). destruct IHh1 as [? [? ?]].
      eexists. split.
      * eapply OnOne2_tl. eassumption.
      * constructor ; eauto.
Qed.

Lemma OnOne2_split :
  forall A (P : A -> A -> Type) l l',
    OnOne2 P l l' ->
    ∑ x y u v,
      P x y ×
      (l = u ++ x :: v /\
      l' = u ++ y :: v).
Proof.
  intros A P l l' h.
  induction h.
  - exists hd, hd', [], tl.
    intuition eauto.
  - destruct IHh as [x [y [u [v ?]]]].
    exists x, y, (hd :: u), v.
    intuition eauto. all: subst. all: reflexivity.
Qed.

Lemma OnOne2_impl {A} {P Q} {l l' : list A} :
  OnOne2 P l l' ->
  (forall x y, P x y -> Q x y) ->
  OnOne2 Q l l'.
Proof.
  induction 1; constructor; intuition eauto.
Qed.

Ltac toAll :=
  match goal with
  | H : is_true (forallb _ _) |- _ => apply forallb_All in H

  | |- is_true (forallb _ _) => apply All_forallb

  | H : Forall _ ?x |- _ => apply Forall_All in H

  | |- Forall _ _ => apply All_Forall

  | H : is_true (forallb2 _ _ _) |- _ => apply forallb2_All2 in H

  | |- is_true (forallb2 _ _ _) => apply All2_forallb2

  | H : All _ ?x, H' : All _ ?x |- _ =>
    apply (All_mix H) in H'; clear H

  | H : Alli _ _ ?x, H' : Alli _ _ ?x |- _ =>
    apply (Alli_mix H) in H'; clear H

  | H : All _ ?x, H' : All2 _ ?x _  |- _ =>
    apply (All2_All_mix_left H) in H'; clear H

  | H : All _ ?x, H' : All2 _ _ ?x  |- _ =>
    apply (All2_All_mix_right H) in H'; clear H

  | |- All _ (map _ _) => apply All_map

  | H : All _ (map _ _) |- _ => apply All_map_inv in H

  | |- All _ (rev_map _ _) => apply All_rev_map

  | |- All _ (List.rev _) => apply All_rev

  | |- All2 _ (map _ _) (map _ _) => apply All2_map
  end.

Lemma All_map_eq {A B} {l} {f g : A -> B} :
  All (fun x => f x = g x) l ->
  map f l = map g l.
Proof.
  induction 1; simpl; trivial.
  now rewrite IHX p.
Qed.

Lemma All_map_id {A} {l} {f : A -> A} :
  All (fun x => f x = x) l ->
  map f l = l.
Proof.
  induction 1; simpl; trivial.
  now rewrite IHX p.
Qed.

Ltac All_map :=
  match goal with
    |- map _ _ = map _ _ => apply All_map_eq
  | |- map _ _ = _ => apply All_map_id
  end.

Lemma forall_forallb_map_spec {A B : Type} {P : A -> Prop} {p : A -> bool}
      {l : list A} {f g : A -> B} :
    Forall P l -> is_true (forallb p l) ->
    (forall x : A, P x -> is_true (p x) -> f x = g x) -> map f l = map g l.
Proof.
  induction 1; simpl; trivial.
  rewrite andb_and. intros [px pl] Hx.
  f_equal. now apply Hx. now apply IHForall.
Qed.

Lemma forall_forallb_forallb_spec {A : Type} {P : A -> Prop} {p : A -> bool}
      {l : list A} {f : A -> bool} :
    Forall P l -> is_true (forallb p l) ->
    (forall x : A, P x -> is_true (p x) -> is_true (f x)) -> is_true (forallb f l).
Proof.
  induction 1; simpl; trivial.
  rewrite !andb_and. intros [px pl] Hx. eauto.
Qed.


Lemma Forall_map {A B} (P : B -> Prop) (f : A -> B) l : Forall (Program.Basics.compose P f) l -> Forall P (map f l).
Proof.
  induction 1; constructor; auto.
Qed.

Lemma Forall_map_inv {A B} (P : B -> Prop) (f : A -> B) l : Forall P (map f l) -> Forall (compose P f) l.
Proof. induction l; intros Hf; inv Hf; try constructor; eauto. Qed.

Lemma Forall_impl {A} {P Q : A -> Prop} {l} :
  Forall P l -> (forall x, P x -> Q x) -> Forall Q l.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma All2_impl {A B} {P Q : A -> B -> Type} {l l'} :
    All2 P l l' ->
    (forall x y, P x y -> Q x y) ->
    All2 Q l l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma Forall_app {A} (P : A -> Prop) l l' : Forall P (l ++ l') -> Forall P l /\ Forall P l'.
Proof.
  induction l; intros H. split; try constructor. apply H.
  inversion_clear H. split; intuition auto.
Qed.


Lemma All_safe_nth {A} {P : A -> Type} {Γ n} (isdecl : n < length Γ) : All P Γ ->
   P (safe_nth Γ (exist _ n isdecl)).
Proof.
  induction 1 in n, isdecl |- *. simpl. bang.
  destruct n. simpl. auto.
  simpl in *. eapply IHX.
Qed.


Definition size := nat.

(* Lemma Alli_mapi {A B} (P : nat -> B -> Type) (f : nat -> A -> B) (l : list A) n : *)
(*   Alli (fun n x => P n (f n x)) n l -> Alli P n (mapi f l). *)
(* Proof. induction 1; constructor; auto. Qed. *)

Section All_size.
  Context {A} (P : A -> Type) (fn : forall x1, P x1 -> size).
  Fixpoint all_size {l1 : list A} (f : All P l1) : size :=
  match f with
  | All_nil => 0
  | All_cons px pl => fn _ px + all_size pl
  end.
End All_size.

Section Alli_size.
  Context {A} (P : nat -> A -> Type) (fn : forall n x1, P n x1 -> size).
  Fixpoint alli_size {l1 : list A} {n} (f : Alli P n l1) : size :=
  match f with
  | Alli_nil => 0
  | Alli_cons px pl => fn _ _ px + alli_size pl
  end.
End Alli_size.

Section All2_size.
  Context {A} (P : A -> A -> Type) (fn : forall x1 x2, P x1 x2 -> size).
  Fixpoint all2_size {l1 l2 : list A} (f : All2 P l1 l2) : size :=
  match f with
  | All2_nil => 0
  | All2_cons rxy rll' => fn _ _ rxy + all2_size rll'
  end.
End All2_size.

Ltac close_Forall :=
  match goal with
  | H : Forall _ _ |- Forall _ _ => apply (Forall_impl H); clear H; simpl
  | H : All _ _ |- All _ _ => apply (All_impl H); clear H; simpl
  | H : OnOne2 _ _ _ |- OnOne2 _ _ _ => apply (OnOne2_impl H); clear H; simpl
  | H : All2 _ _ _ |- All2 _ _ _ => apply (All2_impl H); clear H; simpl
  | H : All2 _ _ _ |- All _ _ =>
    (apply (All2_All_left H) || apply (All2_All_right H)); clear H; simpl
  end.

Lemma All2_non_nil {A B} (P : A -> B -> Type) (l : list A) (l' : list B) :
  All2 P l l' -> l <> nil -> l' <> nil.
Proof.
  induction 1; congruence.
Qed.


Lemma nth_error_forall {A} {P : A -> Prop} {l : list A} {n x} :
  nth_error l n = Some x -> Forall P l -> P x.
Proof.
  intros Hnth HPl. induction HPl in n, Hnth |- *. destruct n; discriminate.
  revert Hnth. destruct n. now intros [= ->].
  intros H'; eauto.
Qed.

Lemma nth_error_all {A} {P : A -> Type} {l : list A} {n x} :
  nth_error l n = Some x -> All P l -> P x.
Proof.
  intros Hnth HPl. induction HPl in n, Hnth |- *. destruct n; discriminate.
  revert Hnth. destruct n. now intros [= ->].
  intros H'; eauto.
Qed.

Lemma nth_error_alli {A} {P : nat -> A -> Type} {l : list A} {n x} {k} :
  nth_error l n = Some x -> Alli P k l -> P (k + n) x.
Proof.
  intros Hnth HPl. induction HPl in n, Hnth |- *.
  destruct n; discriminate.
  revert Hnth. destruct n. intros [= ->]. now rewrite Nat.add_0_r.
  intros H'; eauto. rewrite <- Nat.add_succ_comm. eauto.
Qed.

Lemma nth_error_Some' {A} l n : (exists x : A, nth_error l n = Some x) <-> n < length l.
Proof.
  revert n. induction l; destruct n; simpl.
  - split; [now destruct 1 | inversion 1].
  - split; [now destruct 1 | inversion 1].
  - split; now intuition eauto with arith.
  - rewrite IHl; split; auto with arith.
Qed.

Lemma nth_error_forallb {A} P l n :
  @forallb A P l -> on_Some_or_None P (nth_error l n).
Proof.
  induction l in n |- *.
  - intros _. destruct n; constructor.
  - intro H. apply forallb_Forall in H.
    inv H. destruct n; cbn; auto.
    now apply forallb_Forall in H1; eauto.
Qed.

Lemma All_map_id' {A} {P : A -> Type} {l} {f} :
  All P l ->
  (forall x, P x -> f x = x) ->
  map f l = l.
Proof.
  induction 1; simpl; f_equal; intuition auto.
  f_equal; auto.
Qed.

Lemma Alli_mapi_spec {A B} {P : nat -> A -> Type} {l} {f g : nat -> A -> B} {n} :
  Alli P n l -> (forall n x, P n x -> f n x = g n x) ->
  mapi_rec f l n = mapi_rec g l n.
Proof.
  induction 1; simpl; trivial.
  intros Heq. rewrite Heq; f_equal; auto.
Qed.

Lemma Alli_mapi_id {A} {P : nat -> A -> Type} {l} {f} {n} :
  Alli P n l ->
  (forall n x, P n x -> f n x = x) ->
  mapi_rec f l n = l.
Proof.
  induction 1; simpl; f_equal; intuition auto.
  f_equal; eauto.
Qed.

Lemma Alli_map_id {A} {P : nat -> A -> Type} {l} {f} {n} :
  Alli P n l ->
  (forall n x, P n x -> f x = x) ->
  map f l = l.
Proof.
  induction 1; simpl; f_equal; intuition auto.
  f_equal; eauto.
Qed.

Lemma forallb_map {A B} (f : A -> B) (l : list A) p :
  forallb p (map f l) = forallb (compose p f) l.
Proof.
  induction l in p, f |- *; unfold compose; simpl; rewrite ?andb_and;
    intuition (f_equal; auto). apply IHl.
Qed.

Lemma All_forallb' {A} P (l : list A) (p : A -> bool) :
  All P l ->
  (forall x, P x -> is_true (p x)) ->
  is_true (forallb p l).
Proof.
  induction 1 in p |- *; unfold compose; simpl; rewrite ?andb_and;
    intuition auto.
Qed.

Lemma forallb_Forall' {A} (P : A -> Prop) (l : list A) p :
  is_true (forallb p l) ->
  (forall x, is_true (p x) -> P x) ->
  Forall P l.
Proof.
  induction l in p |- *; unfold compose; simpl. constructor.
  intros. constructor; eauto; rewrite -> andb_and in H; intuition eauto.
Qed.

Lemma forallb_skipn {A} (p : A -> bool) n l :
  is_true (forallb p l) ->
  is_true (forallb p (skipn n l)).
Proof.
  induction l in n |- *; destruct n; simpl; try congruence.
  intros. apply IHl. rewrite -> andb_and in H; intuition.
Qed.

Lemma Forall_forallb_eq_forallb {A} (P : A -> Prop) (p q : A -> bool) l :
  Forall P l ->
  (forall x, P x -> p x = q x) ->
  forallb p l = forallb q l.
Proof.
  induction 1; simpl; intuition (f_equal; auto).
Qed.

Lemma forallb2_length {A} (p : A -> A -> bool) l l' : is_true (forallb2 p l l') -> length l = length l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; try congruence.
  rewrite !andb_and. intros [Hp Hl]. erewrite IHl; eauto.
Qed.

Lemma Alli_map_option_out_mapi_Some_spec {A B} (f g : nat -> A -> option B) l t P :
  Alli P 0 l ->
  (forall i x t, P i x -> f i x = Some t -> g i x = Some t) ->
  map_option_out (mapi f l) = Some t ->
  map_option_out (mapi g l) = Some t.
Proof.
  unfold mapi. generalize 0.
  move => n Ha Hfg. move: t.
  induction Ha; try constructor; auto.
  move=> t /=. case E: (f n hd) => [b|]; try congruence.
  rewrite (Hfg n _ _ p E).
  case E' : map_option_out => [b'|]; try congruence.
  move=> [= <-]. now rewrite (IHHa _ E').
Qed.

(* todo: move *)
Lemma All_mapi {A B} P f l k :
  Alli (fun i x => P (f i x)) k l -> All P (@mapi_rec A B f l k).
Proof.
  induction 1; simpl; constructor; auto.
Qed.

Lemma All_Alli {A} {P : A -> Type} {Q : nat -> A -> Type} {l n} :
  All P l ->
  (forall n x, P x -> Q n x) ->
  Alli Q n l.
Proof.
  intro H. revert n. induction H; constructor; eauto.
Qed.

Lemma All2_All_left_pack {A B} {P : A -> B -> Type} {l l'} :
  All2 P l l' -> Alli (fun i x => ∑ y, (nth_error l i = Some x /\ nth_error l' i = Some y) * P x y) 0 l.
Proof.
  intros HF. induction HF; constructor; intuition eauto.
  exists y; intuition eauto. clear -IHHF.
  revert IHHF. generalize l at 1 3. intros. apply Alli_shift.
  now simpl.
Qed.

Lemma map_option_out_All {A} P (l : list (option A)) l' :
  (All (on_Some_or_None P) l) ->
  map_option_out l = Some l' ->
  All P l'.
Proof.
  induction 1 in l' |- *; cbn; inversion 1; subst; try constructor.
  destruct x; [|discriminate].
  case_eq (map_option_out l); [|intro e; rewrite e in H1; discriminate].
  intros l0 e; rewrite e in H1; inversion H1; subst.
  constructor; auto.
Qed.

Lemma Forall_forallb {A} P (l : list A) (p : A -> bool) :
  Forall P l ->
  (forall x, P x -> is_true (p x)) ->
  is_true (forallb p l).
Proof.
  induction 1 in p |- *; unfold compose; simpl; rewrite ?andb_and;
    intuition auto.
Qed.

Lemma Forall2_right {A B} (P : B -> Prop) (l : list A) (l' : list B) :
  Forall2 (fun x y => P y) l l' -> List.Forall (fun x => P x) l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma Forall2_non_nil {A B} (P : A -> B -> Prop) (l : list A) (l' : list B) :
  Forall2 P l l' -> l <> nil -> l' <> nil.
Proof.
  induction 1; congruence.
Qed.

Lemma Forall2_length {A B} {P : A -> B -> Prop} {l l'} : Forall2 P l l' -> #|l| = #|l'|.
Proof. induction 1; simpl; auto. Qed.

Lemma Forall2_app_r {A} (P : A -> A -> Prop) l l' r r' : Forall2 P (l ++ [r]) (l' ++ [r']) ->
                                                         (Forall2 P l l') /\ (P r r').
Proof.
  induction l in l', r |- *; simpl; intros; destruct l'; simpl in *; inversion H; subst.
  - intuition.
  - destruct l'; cbn in *.
    + inversion H5.
    + inversion H5.
  - destruct l; cbn in *.
    + inversion H5.
    + inversion H5.
  - specialize (IHl _ _ H5). intuition auto.
Qed.

Lemma Forall2_map_inv :
  forall {A B A' B'} (R : A' -> B' -> Prop) (f : A -> A')
    (g : B -> B') (l : list A) (l' : list B),
    Forall2 R (map f l) (map g l') ->
    Forall2 (fun x => R (f x) ∘ g) l l'.
Proof.
  intros A B A' B' R f g l l' h.
  induction l in l', h |- * ; destruct l' ; try solve [ inversion h ].
  - constructor.
  - constructor.
    + inversion h. subst. assumption.
    + eapply IHl. inversion h. assumption.
Qed.

Lemma All2_app_inv : forall (A B : Type) (R : A -> B -> Type),
    forall l l1 l2, All2 R (l1 ++ l2) l -> { '(l1',l2') : _ & (l = l1' ++ l2')%list * (All2 R l1 l1') * (All2 R l2 l2')}%type.
Proof.
  intros. revert l2 l X. induction l1; intros; cbn in *.
  - exists ([], l). eauto.
  - inversion X. subst.
    eapply IHl1 in X1 as ( [] & ? & ?). destruct p.  subst.
    eexists (y :: l, l0). repeat split; eauto.
Qed.

Lemma All2_ind_rev : forall (A B : Type) (R : A -> B -> Type) (P : forall (l : list A) (l0 : list B), Prop),
    P [] [] ->
    (forall (x : A) (y : B) (l : list A) (l' : list B) (r : R x y) (a : All2 R l l'),
        P l l' -> P (l ++ [x])%list (l' ++ [y]))%list ->
    forall (l : list A) (l0 : list B) (a : All2 R l l0), P l l0.
Proof.
  intros. revert l0 a. induction l using rev_ind; cbn; intros.
  - inv a. eauto.
  - eapply All2_app_inv in a as ([] & [[]]). subst.
    inv a0. inv X0. eauto.
Qed.


Lemma All2_app :
  forall (A B : Type) (R : A -> B -> Type),
  forall l1 l2 l1' l2',
    All2 R l1 l1' ->
    All2 R l2 l2' ->
    All2 R (l1 ++ l2) (l1' ++ l2').
Proof.
  induction 1 ; cbn ; eauto.
Qed.

Lemma All2_impl_In {A B} {P Q : A -> B -> Type} {l l'} :
  All2 P l l' ->
  (forall x y, In x l -> In y l' -> P x y -> Q x y) ->
  All2 Q l l'.
Proof.
  revert l'. induction l; intros; inversion X.
  - econstructor.
  - subst. econstructor.  eapply X0. firstorder. firstorder. eauto.
    eapply IHl. eauto. intros.
    eapply X0. now right. now right. eauto.
Qed.

Lemma Forall2_skipn A B (P : A -> B -> Prop) l l' n:
  Forall2 P l l' -> Forall2 P (skipn n l) (skipn n l').
Proof.
  revert l l'; induction n; intros.
  - unfold skipn. eauto.
  - cbv [skipn]. fold (@skipn A n). fold (@skipn B n).
    inversion H; subst. econstructor.
    eauto.
Qed.

Lemma All2_Forall2 {A B} {P : A -> B -> Prop} {l l'} :
  All2 P l l' -> Forall2 P l l'.
Proof.
  induction 1; eauto.
Qed.

Lemma Forall2_nth_error_Some {A B} {P : A -> B -> Prop} {l l'} n t :
  Forall2 P l l' ->
  nth_error l n = Some t ->
  exists t' : B, (nth_error l' n = Some t') /\ P t t'.
Proof.
  intros Hall. revert n.
  induction Hall; destruct n; simpl; try congruence. intros [= ->]. exists y. intuition auto.
  eauto.
Qed.

Lemma Forall2_impl {A B} {P Q : A -> B -> Prop} {l l'} :
    Forall2 P l l' ->
    (forall x y, P x y -> Q x y) ->
    Forall2 Q l l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma app_Forall :
  forall A P (l1 l2 : list A),
    Forall P l1 ->
    Forall P l2 ->
    Forall P (l1 ++ l2).
Proof.
  intros A P l1 l2 h1 h2.
  revert l2 h2.
  induction h1 ; intros l2 h2.
  - assumption.
  - cbn. constructor ; try assumption.
    eapply IHh1. assumption.
Qed.

Lemma rev_Forall :
  forall A P l,
    Forall P l ->
    Forall P (@List.rev A l).
Proof.
  intros A P l h.
  induction l.
  - cbn. constructor.
  - cbn. dependent destruction h.
    specialize (IHl ltac:(assumption)).
    eapply app_Forall ; try assumption.
    repeat constructor. assumption.
Qed.

Lemma Forall2_impl' {A B} {P Q : A -> B -> Prop} {l l'} :
    Forall2 P l l' ->
    Forall (fun x => forall y, P x y -> Q x y) l ->
    Forall2 Q l l'.
Proof.
  induction 1; constructor;
    inversion H1; intuition.
Qed.

Lemma Forall2_Forall {A R l} : @Forall2 A A R l l -> Forall (fun x => R x x) l.
Proof.
  induction l. constructor.
  inversion 1; constructor; intuition.
Qed.

Lemma All2_All {A R l} : @All2 A A R l l -> All (fun x => R x x) l.
Proof.
  induction l. constructor.
  inversion 1; constructor; intuition.
Qed.

Lemma Forall_Forall2 {A R l} : Forall (fun x => R x x) l -> @Forall2 A A R l l.
Proof.
  induction l. constructor.
  inversion 1; constructor; intuition.
Qed.

Lemma Forall_True {A} {P : A -> Prop} l : (forall x, P x) -> Forall P l.
Proof.
  intro H. induction l; now constructor.
Qed.

Lemma Forall2_True {A B} {R : A -> B -> Prop} l l'
  : (forall x y, R x y) -> #|l| = #|l'| -> Forall2 R l l'.
Proof.
  intro H. revert l'; induction l; simpl;
    intros [] e; try discriminate e; constructor.
  easy.
  apply IHl. now apply eq_add_S.
Qed.

Lemma Forall2_map {A B A' B'} (R : A' -> B' -> Prop) (f : A -> A') (g : B -> B') l l'
  : Forall2 (fun x y => R (f x) (g y)) l l' -> Forall2 R (map f l) (map g l').
Proof.
  induction 1; constructor; auto.
Qed.


Lemma Forall2_and {A B} (R R' : A -> B -> Prop) l l'
  : Forall2 R l l' -> Forall2 R' l l' -> Forall2 (fun x y => R x y /\ R' x y) l l'.
Proof.
  induction 1.
  intro; constructor.
  inversion_clear 1.
  constructor; intuition.
Defined.

Lemma Forall_Forall2_and {A B} {R : A -> B -> Prop} {P l l'}
  : Forall2 R l l' -> Forall P l -> Forall2 (fun x y => P x /\ R x y) l l'.
Proof.
  induction 1.
  intro; constructor.
  inversion_clear 1.
  constructor; intuition.
Defined.

Lemma Forall_Forall2_and' {A B} {R : A -> B -> Prop} {P l l'}
  : Forall2 R l l' -> Forall P l' -> Forall2 (fun x y => R x y /\ P y) l l'.
Proof.
  induction 1.
  intro; constructor.
  inversion_clear 1.
  constructor; intuition.
Defined.

Lemma Forall2_nth :
  forall A B P l l' n (d : A) (d' : B),
    Forall2 P l l' ->
    P d d' ->
    P (nth n l d) (nth n l' d').
Proof.
  intros A B P l l' n d d' h hd.
  induction n in l, l', h |- *.
  - destruct h.
    + assumption.
    + assumption.
  - destruct h.
    + assumption.
    + simpl. apply IHn. assumption.
Qed.

Lemma Forall2_nth_error_Some_l :
  forall A B (P : A -> B -> Prop) l l' n t,
    nth_error l n = Some t ->
    Forall2 P l l' ->
    exists t',
      nth_error l' n = Some t' /\
      P t t'.
Proof.
  intros A B P l l' n t e h.
  induction n in l, l', t, e, h |- *.
  - destruct h.
    + cbn in e. discriminate.
    + cbn in e. inversion e. subst.
      exists y. split ; auto.
  - destruct h.
    + cbn in e. discriminate.
    + cbn in e. apply IHn with (l' := l') in e ; assumption.
Qed.

Lemma Forall2_nth_error_None_l :
  forall A B (P : A -> B -> Prop) l l' n,
    nth_error l n = None ->
    Forall2 P l l' ->
    nth_error l' n = None.
Proof.
  intros A B P l l' n e h.
  induction n in l, l', e, h |- *.
  - destruct h.
    + reflexivity.
    + cbn in e. discriminate e.
  - destruct h.
    + reflexivity.
    + cbn in e. cbn. eapply IHn ; eauto.
Qed.

Lemma Forall2_trans :
  forall A (P : A -> A -> Prop),
    RelationClasses.Transitive P ->
    RelationClasses.Transitive (Forall2 P).
Proof.
  intros A P hP l1 l2 l3 h1 h2.
  induction h1 in l3, h2 |- *.
  - inversion h2. constructor.
  - inversion h2. constructor.
    + eapply hP ; eauto.
    + eapply IHh1 ; eauto.
Qed.

Lemma Forall2_rev :
  forall A B R l l',
    @Forall2 A B R l l' ->
    Forall2 R (List.rev l) (List.rev l').
Proof.
  intros A B R l l' h.
  induction h.
  - constructor.
  - cbn. eapply Forall2_app ; eauto.
Qed.

(* Weak, would need some Forall2i *)
Lemma Forall2_mapi :
  forall A B A' B' (R : A' -> B' -> Prop) (f : nat -> A -> A') (g : nat -> B -> B') l l',
    Forall2 (fun x y => forall i, R (f i x) (g i y)) l l' ->
    Forall2 R (mapi f l) (mapi g l').
Proof.
  intros A B A' B' R f g l l' h.
  unfold mapi. generalize 0. intro i.
  induction h in i |- *.
  - constructor.
  - cbn. constructor ; eauto.
Qed.

Lemma All2_trans {A} (P : A -> A -> Type) :
  CRelationClasses.Transitive P ->
  CRelationClasses.Transitive (All2 P).
Proof.
  intros HP x y z H. induction H in z |- *.
  intros Hyz. inv Hyz. constructor.
  intros Hyz. inv Hyz. constructor; auto.
  now transitivity y.
Qed.

Lemma All2_nth :
  forall A B P l l' n (d : A) (d' : B),
    All2 P l l' ->
    P d d' ->
    P (nth n l d) (nth n l' d').
Proof.
  intros A B P l l' n d d' h hd.
  induction n in l, l', h |- *.
  - destruct h.
    + assumption.
    + assumption.
  - destruct h.
    + assumption.
    + simpl. apply IHn. assumption.
Qed.

Lemma All2_mapi :
  forall A B A' B' (R : A' -> B' -> Type) (f : nat -> A -> A') (g : nat -> B -> B') l l',
    All2 (fun x y => forall i, R (f i x) (g i y)) l l' ->
    All2 R (mapi f l) (mapi g l').
Proof.
  intros A B A' B' R f g l l' h.
  unfold mapi. generalize 0. intro i.
  induction h in i |- *.
  - constructor.
  - cbn. constructor ; eauto.
Qed.

Lemma All2_skipn :
  forall A B R l l' n,
    @All2 A B R l l' ->
    @All2 A B R (skipn n l) (skipn n l').
Proof.
  intros A B R l l' n h.
  induction h in n |- *.
  all: destruct n ; try econstructor ; eauto.
Qed.

Lemma All2_rev (A : Type) (P : A -> A -> Type) (l l' : list A) :
  All2 P l l' ->
  All2 P (List.rev l) (List.rev l').
Proof.
  induction 1. constructor.
  simpl. eapply All2_app; auto.
Qed.

Lemma All2_right_triv {A B} {l : list A} {l' : list B} P :
  All P l' -> #|l| = #|l'| -> All2 (fun _ b => P b) l l'.
Proof.
  induction 1 in l |- *.
  all: cbn.
  all: intros.
  all: destruct l.
  all: cbn in *.
  all: try (exfalso ; lia).
  all: try solve [ econstructor; eauto ].
Qed.

Lemma All_repeat {A} {n P} x :
  P x -> @All A P (repeat x n).
Proof.
  induction n; cbn; econstructor; eauto.
Qed.

Lemma All2_map_left {A B C} (P : A -> C -> Type) l l' (f : B -> A) :
  All2 (fun x y => P (f x) y) l l' -> All2 P  (map f l) l'.
Proof. intros. rewrite <- (map_id l'). eapply All2_map; eauto. Qed.

Lemma All2_map_right {A B C} (P : A -> C -> Type) l l' (f : B -> C) :
  All2 (fun x y => P x (f y)) l l' -> All2 P  l (map f l').
Proof. intros. rewrite <- (map_id l). eapply All2_map; eauto. Qed.

Lemma Forall2_Forall_right {A B} {P : A -> B -> Prop} {Q : B -> Prop} {l l'} :
  Forall2 P l l' ->
  (forall x y, P x y -> Q y) ->
  Forall Q l'.
Proof.
  intros HF H. induction HF; constructor; eauto.
Qed.

Lemma All2_from_nth_error A B L1 L2 (P : A -> B -> Type) :
  #|L1| = #|L2| ->
                (forall n x1 x2, n < #|L1| -> nth_error L1 n = Some x1
                                      -> nth_error L2 n = Some x2
                                      -> P x1 x2) ->
                All2 P L1 L2.
Proof.
  revert L2; induction L1; cbn; intros.
  - destruct L2; inv H. econstructor.
  - destruct L2; inversion H. econstructor.
    eapply (X 0); cbn; eauto. lia.
    eapply IHL1. eauto.
    intros. eapply (X (S n)); cbn; eauto. lia.
Qed.

Lemma All2_nth_error {A B} {P : A -> B -> Type} {l l'} n t t' :
  All2 P l l' ->
  nth_error l n = Some t ->
  nth_error l' n = Some t' ->
  P t t'.
Proof.
  intros Hall. revert n.
  induction Hall; destruct n; simpl; try congruence.
  eauto.
Qed.

Require Import MCSquash.

Lemma All_In X (P : X -> Type) (l : list X) x : All P l -> In x l -> squash (P x).
Proof.
  induction 1; cbn; intros; destruct H.
  - subst. econstructor. eauto.
  - eauto.
Qed.

Lemma All2_swap :
  forall A B R l l',
    @All2 A B R l l' ->
    All2 (fun x y => R y x) l' l.
Proof.
  intros A B R l l' h.
  induction h ; eauto.
Qed.

Lemma All2_firstn :
  forall A B R l l' n,
    @All2 A B R l l' ->
    @All2 A B R (firstn n l) (firstn n l').
Proof.
  intros A B R l l' n h.
  induction h in n |- *.
  all: destruct n ; try econstructor ; eauto.
Qed.


Lemma All2_app_inv_r :
  forall A B R l r1 r2,
    @All2 A B R l (r1 ++ r2) ->
    ∑ l1 l2,
      (l = l1 ++ l2)%list ×
      All2 R l1 r1 ×
      All2 R l2 r2.
Proof.
  intros A B R l r1 r2 h.
  exists (firstn #|r1| l), (skipn #|r1| l).
  split ; [| split].
  - rewrite firstn_skipn. reflexivity.
  - apply All2_firstn with (n := #|r1|) in h.
    rewrite firstn_app in h. rewrite firstn_all in h.
    replace (#|r1| - #|r1|) with 0 in h by lia. cbn in h.
    rewrite app_nil_r in h. assumption.
  - apply All2_skipn with (n := #|r1|) in h.
    rewrite skipn_all_app in h. assumption.
Qed.

Lemma All2_impl' {A B} {P Q : A -> B -> Type} {l : list A} {l' : list B}
  : All2 P l l' -> All (fun x => forall y, P x y -> Q x y) l -> All2 Q l l'.
Proof.
  induction 1. constructor.
  intro XX; inv XX.
  constructor; auto.
Defined.

Lemma All_All2 {A} {P : A -> A -> Type} {Q} {l : list A} :
  All Q l ->
  (forall x, Q x -> P x x) ->
  All2 P l l.
Proof.
  induction 1; constructor; auto.
Qed.

(* Should be All2_nth_error_Some_l *)
Lemma All2_nth_error_Some {A B} {P : A -> B -> Type} {l l'} n t :
  All2 P l l' ->
  nth_error l n = Some t ->
  { t' : B & (nth_error l' n = Some t') * P t t'}%type.
Proof.
  intros Hall. revert n.
  induction Hall; destruct n; simpl; try congruence.
  intros [= ->]. exists y. intuition auto.
  eauto.
Qed.

Lemma All2_nth_error_Some_r {A B} {P : A -> B -> Type} {l l'} n t' :
  All2 P l l' ->
  nth_error l' n = Some t' ->
  ∑ t, nth_error l n = Some t × P t t'.
Proof.
  intros Hall. revert n.
  induction Hall; destruct n; simpl; try congruence.
  intros [= ->]. exists x. intuition auto.
  eauto.
Qed.

Lemma All2_nth_error_None {A B} {P : A -> B -> Type} {l l'} n :
  All2 P l l' ->
  nth_error l n = None ->
  nth_error l' n = None.
Proof.
  intros Hall. revert n.
  induction Hall; destruct n; simpl; try congruence. auto.
Qed.

Lemma All2_length {A B} {P : A -> B -> Type} l l' : All2 P l l' -> #|l| = #|l'|.
Proof. induction 1; simpl; auto. Qed.

Lemma All2_same {A} (P : A -> A -> Type) l : (forall x, P x x) -> All2 P l l.
Proof. induction l; constructor; auto. Qed.


Lemma All2_prod {A} P Q (l l' : list A) : All2 P l l' -> All2 Q l l' -> All2 (Trel_conj P Q) l l'.
Proof.
  induction 1; inversion 1; subst; auto.
Defined.

Lemma All2_prod_inv :
  forall A (P : A -> A -> Type) Q l l',
    All2 (Trel_conj P Q) l l' ->
    All2 P l l' × All2 Q l l'.
Proof.
  intros A P Q l l' h.
  induction h.
  - auto.
  - destruct IHh. destruct r.
    split ; constructor ; auto.
Qed.

Lemma All2_sym {A} (P : A -> A -> Type) l l' :
  All2 P l l' -> All2 (fun x y => P y x) l' l.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma All2_symP {A} (P : A -> A -> Type) :
  CRelationClasses.Symmetric P ->
  CRelationClasses.Symmetric (All2 P).
Proof.
  intros hP x y h. induction h.
  - constructor.
  - constructor ; eauto.
Qed.

Lemma All_All2_All2_mix {A B} (P : B -> B -> Type) (Q R : A -> B -> Type) l l' l'' :
  All (fun x => forall y z, Q x y -> R x z -> ∑ v, P y v * P z v) l -> All2 Q l l' -> All2 R l l'' ->
  ∑ l''', All2 P l' l''' * All2 P l'' l'''.
Proof.
  intros H; induction H in l', l'' |- *;
  intros H' H''; depelim H'; depelim H''; try solve [econstructor; eauto; constructor].
  simpl. destruct (IHAll _ _ H' H''). destruct (p _ _ q r).
  exists (x1 :: x0). split; constructor; intuition auto.
Qed.

Lemma All_forallb_map_spec {A B : Type} {P : A -> Type} {p : A -> bool}
      {l : list A} {f g : A -> B} :
    All P l -> forallb p l ->
    (forall x : A, P x -> p x -> f x = g x) -> map f l = map g l.
Proof.
  induction 1; simpl; trivial.
  rewrite andb_and. intros [px pl] Hx.
  f_equal. now apply Hx. now apply IHX.
Qed.

Lemma All_forallb_forallb_spec {A : Type} {P : A -> Type} {p : A -> bool}
      {l : list A} {f : A -> bool} :
    All P l -> forallb p l ->
    (forall x : A, P x -> p x -> f x) -> forallb f l.
Proof.
  induction 1; simpl; trivial.
  rewrite !andb_and. intros [px pl] Hx. eauto.
Qed.


Lemma forallb_nth {A} (l : list A) (n : nat) P d :
  forallb P l -> n < #|l| -> exists x, (nth n l d = x) /\ P x.
Proof.
  induction l in n |- *; destruct n; simpl; auto; try easy.
  move/andP => [pa pl] pn. exists a; easy.
  move/andP => [pa pl] pn. specialize (IHl n pl).
  apply IHl; lia.
Qed.

Lemma forallb_nth' {A} {l : list A} {P} n d :
  forallb P l -> {exists x, (nth n l d = x) /\ P x} + {nth n l d = d}.
Proof.
  intro H. destruct (le_lt_dec #|l| n) as [HH|HH].
  - rewrite nth_overflow; try assumption; now right.
  - left. eapply forallb_nth; assumption.
Qed.

Lemma forallb_impl {A} (p q : A -> bool) l :
  (forall x, In x l -> p x -> q x) -> forallb p l -> forallb q l.
Proof.
  intros H0 H1. eapply forallb_forall. intros x H2.
  eapply forallb_forall in H1; try eassumption.
  now eapply H0.
Qed.

Lemma forallb_iff {A} (p q : A -> bool) l :
  (forall x, In x l -> p x <-> q x) -> forallb p l = forallb q l.
Proof.
  intros H0. eapply Forall_forallb_eq_forallb with (P:=fun x => In x l).
  - now apply Forall_forall.
  - intros; eapply eq_true_iff_eq; eauto.
Qed.

Lemma All2_eq :
  forall A (l l' : list A),
    All2 eq l l' ->
    l = l'.
Proof.
  intros A l l' h.
  induction h ; eauto. subst. reflexivity.
Qed.


Lemma All_prod_inv :
  forall A P Q l,
    All (fun x : A => P x × Q x) l ->
    All P l × All Q l.
Proof.
  intros A P Q l h.
  induction h.
  - split ; auto.
  - destruct IHh, p.
    split ; constructor ; auto.
Qed.


Lemma All_prod :
  forall A P Q l,
    All P l ->
    All Q l ->
    All (fun x : A => P x × Q x) l.
Proof.
  intros A P Q l h1 h2.
  induction h1 in h2 |- *.
  - constructor.
  - dependent destruction h2.
    specialize (IHh1 h2). auto.
Qed.


Inductive All2i {A B : Type} (R : nat -> A -> B -> Type) (n : nat)
  : list A -> list B -> Type :=
| All2i_nil : All2i R n [] []
| All2i_cons :
    forall x y l r,
      R n x y ->
      All2i R (S n) l r ->
      All2i R n (x :: l) (y :: r).

Lemma All2i_impl :
  forall A B R R' n l l',
    @All2i A B R n l l' ->
    (forall i x y, R i x y -> R' i x y) ->
    All2i R' n l l'.
Proof.
  intros A B R R' n l l' ha h.
  induction ha. 1: constructor.
  constructor. 2: assumption.
  eapply h. assumption.
Qed.

Lemma All2i_mapi :
  forall A B C D R f g l l',
    @All2i A B (fun i x y => R i (f i x) (g i y)) 0 l l' ->
    @All2i C D R 0 (mapi f l) (mapi g l').
Proof.
  intros A B C D R f g l l' h.
  unfold mapi.
  revert h.
  generalize 0. intros n h.
  induction h. 1: constructor.
  simpl. constructor. all: assumption.
Qed.

Lemma All2i_app :
  forall A B R n l1 l2 r1 r2,
    @All2i A B R n l1 r1 ->
    All2i R (n + #|l1|) l2 r2 ->
    All2i R n (l1 ++ l2) (r1 ++ r2).
Proof.
  intros A B R n l1 l2 r1 r2 h1 h2.
  induction h1 in r2, l2, h2 |- *.
  - simpl in *. replace (n + 0)%nat with n in h2 by lia. assumption.
  - simpl in *. constructor. 1: assumption.
    eapply IHh1. replace (S (n + #|l|))%nat with (n + S #|l|)%nat by lia.
    assumption.
Qed.

(* Lemma All2i_fnat :
  forall A B R n l r f,
    (forall n, f (S n) = S (f n)) ->
    @All2i A B R (f n) l r ->
    All2i (fun i x y => R (f i) x y) n l r.
Proof.
  intros A B R n l r f hf h.
  remember (f n) as m eqn:e.
  induction h in n, e |- *. 1: constructor.
  constructor.
  - rewrite <- e. assumption.
  - eapply IHh. rewrite hf. auto.

  (* dependent induction h. 1: constructor.
  constructor. 1: assumption.
  eapply IHh. *)
Qed. *)

Lemma All2i_rev :
  forall A B R l l' n,
    @All2i A B R n l l' ->
    All2i (fun i x y => R (n + #|l| - (S i)) x y) 0 (List.rev l) (List.rev l').
Proof.
  intros A B R l l' n h.
  induction h. 1: constructor.
  simpl. apply All2i_app.
  - eapply All2i_impl. 1: eassumption.
    simpl. intros ? ? ? ?.
    replace (n + S #|l| - S i) with (n + #|l| - i) by lia.
    assumption.
  - simpl. constructor. 2: constructor.
    rewrite List.rev_length.
    replace (n + S #|l| - S #|l|) with n by lia.
    assumption.
Qed.

Lemma All_sq {A} {P : A -> Type} {l}
  : All (fun x => ∥ P x ∥) l -> ∥ All P l ∥.
Proof.
  induction 1.
  - repeat constructor.
  - sq; now constructor.
Qed.

Lemma All2_sq {A B} {R : A -> B -> Type} {l1 l2}
  : All2 (fun x y => ∥ R x y ∥) l1 l2 -> ∥ All2 R l1 l2 ∥.
Proof.
  induction 1.
  - repeat constructor.
  - sq; now constructor.
Qed.

Lemma All_All2_refl {A : Type} {R} {l : list A} :
  All (fun x : A => R x x) l -> All2 R l l.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma All2_app_r {A} (P : A -> A -> Type) l l' r r' :
  All2 P (l ++ [r]) (l' ++ [r']) -> (All2 P l l') * (P r r').
Proof.
  induction l in l', r |- *. simpl. intros. destruct l'. simpl in *.
  depelim X; intuition auto.
  depelim X. destruct l'; depelim X.
  intros.
  depelim l'; depelim X. destruct l; depelim X.
  specialize (IHl _ _ X). intuition auto.
Qed.

Lemma Forall2_eq {A} l l'
  : @Forall2 A A eq l l' -> l = l'.
Proof.
  induction 1; congruence.
Qed.

Lemma Forall2_map' {A B A' B'} (R : A' -> B' -> Prop) (f : A -> A') (g : B -> B') l l'
  : Forall2 R (map f l) (map g l') -> Forall2 (fun x y => R (f x) (g y)) l l'.
Proof.
  induction l in l' |- *.
  - destruct l'; inversion 1. constructor.
  - destruct l'; inversion 1. constructor; auto.
Qed.

Lemma Forall2_same :
  forall A (P : A -> A -> Prop) l,
    (forall x, P x x) ->
    Forall2 P l l.
Proof.
  intros A P l h.
  induction l.
  - constructor.
  - constructor.
    + eapply h.
    + assumption.
Qed.

Lemma Forall2_sym :
  forall A (P : A -> A -> Prop) l l',
    Forall2 P l l' ->
    Forall2 (fun x y => P y x) l' l.
Proof.
  intros A P l l' h.
  induction h.
  - constructor.
  - constructor. all: auto.
Qed.

Lemma forallb2_Forall2 :
  forall A (p : A -> A -> bool) l l',
    forallb2 p l l' ->
    Forall2 (fun x y => p x y) l l'.
Proof.
  intros A p l l' h.
  induction l in l', h |- *.
  - destruct l'. 2: discriminate.
    constructor.
  - destruct l'. 1: discriminate.
    simpl in h. apply andP in h as [? ?].
    constructor. all: auto.
Qed.
