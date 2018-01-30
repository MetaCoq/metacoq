From Template Require Import Template Ast univ.
Require Import List Program.
Require Import BinPos.
Require Import Coq.Arith.Compare_dec Bool.
Set Asymmetric Patterns.

Arguments dname {term} _.
Arguments dtype {term} _.
Arguments dbody {term} _.
Arguments rarg {term} _.

Definition on_snd {A B} (f : B -> B) (p : A * B) :=
  (fst p, f (snd p)).

Definition map_def {term : Set} (f : term -> term) (d : def term) :=
  {| dname := d.(dname); dtype := f d.(dtype); dbody := f d.(dbody); rarg := d.(rarg) |}.

Definition test_snd {A B} (f : B -> bool) (p : A * B) :=
  f (snd p).

Definition test_def {term : Set} (f : term -> bool) (d : def term) :=
  f d.(dtype) && f d.(dbody).

Lemma on_snd_on_snd {A B} (f g : B -> B) (d : A * B) :
  on_snd f (on_snd g d) = on_snd (fun x => f (g x)) d.
Proof.
  destruct d; reflexivity.
Qed.

Lemma compose_on_snd {A B} (f g : B -> B) :
  compose (A:=A * B) (on_snd f) (on_snd g) = on_snd (compose f g).
Proof.
  reflexivity.
Qed.


Lemma map_def_map_def {term : Set} (f g : term -> term) (d : def term) :
  map_def f (map_def g d) = map_def (fun x => f (g x)) d.
Proof.
  destruct d; reflexivity.
Qed.

Lemma compose_map_def {term : Set} (f g : term -> term) :
  compose (A:=def term) (map_def f) (map_def g) = map_def (compose f g).
Proof. reflexivity. Qed.

Lemma combine_map_id {A B} (l : list (A * B)) :
 l = combine (map fst l) (map snd l).
Proof.
  induction l ; simpl; try easy.
  destruct a. now f_equal.
Qed.

Lemma map_map_compose :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (l : list A),
    map g (map f l) = map (compose g f) l.
Proof. apply map_map. Qed.
Hint Unfold compose : terms.

Lemma map_id_f {A} (l : list A) (f : A -> A) :
  (forall x, f x = x) ->
  map f l = l.
Proof.
  induction l; intros; simpl; try easy.
  rewrite H. f_equal. eauto.
Qed.

Lemma map_def_id {t : Set} : map_def (@id t) = id.
Proof. extensionality p. now destruct p. Qed.
Hint Rewrite @map_def_id @map_id.

(** Custom induction principle on syntax, dealing with the various lists appearing in terms. *)

Definition tCaseBrsProp (P : term -> Prop) (l : list (nat * term)) :=
  Forall (fun x => P (snd x)) l.

Definition tFixProp (P : term -> Prop) (m : mfixpoint term) :=
  Forall (fun x : def term => P x.(dtype) /\ P x.(dbody)) m.

Lemma term_forall_list_ind :
  forall P : term -> Prop,
    (forall n : nat, P (tRel n)) ->
    (forall i : ident, P (tVar i)) ->
    (forall n : nat, P (tMeta n)) ->
    (forall (n : nat) (l : list term), Forall P l -> P (tEvar n l)) ->
    (forall s, P (tSort s)) ->
    (forall t : term, P t -> forall (c : cast_kind) (t0 : term), P t0 -> P (tCast t c t0)) ->
    (forall (n : name) (t : term), P t -> forall t0 : term, P t0 -> P (tProd n t t0)) ->
    (forall (n : name) (t : term), P t -> forall t0 : term, P t0 -> P (tLambda n t t0)) ->
    (forall (n : name) (t : term),
        P t -> forall t0 : term, P t0 -> forall t1 : term, P t1 -> P (tLetIn n t t0 t1)) ->
    (forall t : term, P t -> forall l : list term, Forall P l -> P (tApp t l)) ->
    (forall (s : String.string) (u : list Level.t), P (tConst s u)) ->
    (forall (i : inductive) (u : list Level.t), P (tInd i u)) ->
    (forall (i : inductive) (n : nat) (u : list Level.t), P (tConstruct i n u)) ->
    (forall (p : inductive * nat) (t : term),
        P t -> forall t0 : term, P t0 -> forall l : list (nat * term),
            tCaseBrsProp P l -> P (tCase p t t0 l)) ->
    (forall (s : projection) (t : term), P t -> P (tProj s t)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P m -> P (tFix m n)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P m -> P (tCoFix m n)) ->
    forall t : term, P t.
Proof.
  intros until t. revert t.
  fix auxt 1.
  move auxt at top. 
  destruct t; match goal with
                 H : _ |- _ => apply H
              end; auto.
  revert l.
  fix auxl' 1.
  destruct l; constructor; [|apply auxl'].
  apply auxt.
  revert l.
  fix auxl' 1.
  destruct l; constructor; [|apply auxl'].
  apply auxt.
  revert l.
  fix auxl' 1.
  destruct l; constructor; [|apply auxl'].
  apply auxt.

  revert m.
  fix auxm 1.
  destruct m; constructor; [|apply auxm].
  split; apply auxt.
  revert m.
  fix auxm 1.
  destruct m; constructor; [|apply auxm].
  split; apply auxt.
Defined.

Lemma forall_map_spec {A} {P : A -> Prop} {l} {f g : A -> A} :
  Forall P l -> (forall x, P x -> f x = g x) ->
  map f l = map g l.
Proof.
  induction 1; simpl; trivial.
  intros Heq. rewrite Heq. f_equal. apply IHForall. apply Heq. apply H.
Qed.

Lemma on_snd_spec {A B} (P : B -> Prop) (f g : B -> B) (x : A * B) :
  P (snd x) -> (forall x, P x -> f x = g x) ->
  on_snd f x = on_snd g x.
Proof.
  intros. destruct x. unfold on_snd. simpl.
  now rewrite H0; auto.
Qed.

Lemma map_def_spec (P : term -> Prop) (f g : term -> term) (x : def term) :
  P x.(dbody) -> P x.(dtype) -> (forall x, P x -> f x = g x) ->
  map_def f x = map_def g x.
Proof.
  intros. destruct x. unfold map_def. simpl.
  rewrite !H1; auto. 
Qed.

Lemma case_brs_map_spec {P : term -> Prop} {l} {f g : term -> term} :
  tCaseBrsProp P l -> (forall x, P x -> f x = g x) ->
  map (on_snd f) l = map (on_snd g) l.
Proof.
  intros.
  eapply (forall_map_spec H).
  intros.
  eapply on_snd_spec; eauto.
Qed.

Lemma tfix_map_spec {P : term -> Prop} {l} {f g : term -> term} :
  tFixProp P l -> (forall x, P x -> f x = g x) ->
  map (map_def f) l = map (map_def g) l.
Proof.
  intros.
  eapply (forall_map_spec H).
  intros. destruct H1;
  eapply map_def_spec; eauto.
Qed.


Lemma forall_forallb_map_spec {A : Type} {P : A -> Prop} {p : A -> bool}
      {l : list A} {f g : A -> A} :
    Forall P l -> forallb p l = true ->
    (forall x : A, P x -> p x = true -> f x = g x) -> map f l = map g l.
Proof.
  induction 1; simpl; trivial.
  rewrite andb_true_iff. intros [px pl] Hx.
  f_equal. now apply Hx. now apply IHForall. 
Qed.

Lemma on_snd_test_spec {A B} (P : B -> Prop) (p : B -> bool) (f g : B -> B) (x : A * B) :
  P (snd x) -> (forall x, P x -> p x = true -> f x = g x) ->
  test_snd p x = true ->
  on_snd f x = on_snd g x.
Proof.
  intros. destruct x. unfold on_snd. simpl.
  now rewrite H0; auto.
Qed.

Lemma map_def_test_spec (P : term -> Prop) p (f g : term -> term) (x : def term) :
  P x.(dbody) -> P x.(dtype) -> (forall x, P x -> p x = true -> f x = g x) ->
  test_def p x = true ->
  map_def f x = map_def g x.
Proof.
  intros. destruct x. unfold map_def. simpl.
  unfold test_def in H2; simpl in H2. rewrite andb_true_iff in H2.
  rewrite !H1; intuition auto. 
Qed.

Lemma case_brs_forallb_map_spec {P : term -> Prop} {p : term -> bool}
      {l} {f g : term -> term} :
  tCaseBrsProp P l -> 
  forallb (test_snd p) l = true ->
  (forall x, P x -> p x = true -> f x = g x) ->
  map (on_snd f) l = map (on_snd g) l.
Proof.
  intros.
  eapply (forall_forallb_map_spec H H0).
  intros.
  eapply on_snd_test_spec; eauto.
Qed.

Lemma tfix_forallb_map_spec {P : term -> Prop} {p} {l} {f g : term -> term} :
  tFixProp P l -> 
  forallb (test_def p) l = true ->
  (forall x, P x -> p x = true -> f x = g x) ->
  map (map_def f) l = map (map_def g) l.
Proof.
  intros.
  eapply (forall_forallb_map_spec H H0).
  intros. destruct H2.
  eapply map_def_test_spec; eauto.
Qed.

Ltac apply_spec :=
  match goal with
  | H : Forall _ _, H' : forallb _ _ = _ |- map _ _ = map _ _ =>
    eapply (forall_forallb_map_spec H H')
  | H : Forall _ _ |- map _ _ = map _ _ =>
    eapply (forall_map_spec H)
  | H : tCaseBrsProp _ _, H' : forallb _ _ = _ |- map _ _ = map _ _ =>
    eapply (case_brs_forallb_map_spec H H')
  | H : tCaseBrsProp _ _ |- map _ _ = map _ _ =>
    eapply (case_brs_map_spec H)
  | H : tFixProp _ _, H' : forallb _ _ = _ |- map _ _ = map _ _ =>
    eapply (tfix_forallb_map_spec H H')
  | H : tFixProp _ _ |- map _ _ = map _ _ =>
    eapply (tfix_map_spec H)
  end.
