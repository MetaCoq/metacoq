From Coq Require Import Ascii String Bool OrderedType Lia List Program Arith.
From MetaCoq.Template Require Import utils Ast AstUtils.
From MetaCoq.Erasure Require Import EAst.
Import List.ListNotations.
Require Import FunctionalExtensionality.
Require Import ssreflect ssrbool.

Set Asymmetric Patterns.

Fixpoint decompose_app_rec t l :=
  match t with
  | tApp f a => decompose_app_rec f (a :: l)
  | f => (f, l)
  end.

Definition decompose_app f := decompose_app_rec f [].

Lemma decompose_app_rec_mkApps f l l' :
  decompose_app_rec (mkApps f l) l' = decompose_app_rec f (l ++ l').
Proof.
  induction l in f, l' |- *; simpl; auto; rewrite IHl ?app_nil_r; auto.
Qed.

Lemma decompose_app_mkApps f l :
  isApp f = false -> decompose_app (mkApps f l) = (f, l).
Proof.
  intros Hf. unfold decompose_app. rewrite decompose_app_rec_mkApps. rewrite app_nil_r.
  destruct f; simpl in *; (discriminate || reflexivity).
Qed.


Lemma mkApps_app t l l' : mkApps t (l ++ l') = mkApps (mkApps t l) l'.
Proof.
  induction l in t, l' |- *; simpl; auto.
Qed.

Lemma mkApps_nested f l l' : mkApps (mkApps f l) l' = mkApps f (l ++ l').
Proof.
  induction l in f, l' |- *; destruct l'; simpl; rewrite ?app_nil_r; auto.
  rewrite <- IHl. simpl. reflexivity.
Qed.

Lemma decompose_app_rec_inv {t l' f l} :
  decompose_app_rec t l' = (f, l) ->
  mkApps t l' = mkApps f l.
Proof.
  induction t in f, l', l |- *; try intros [= <- <-]; try reflexivity.
  simpl. apply/IHt1.
Qed.

Lemma decompose_app_inv {t f l} :
  decompose_app t = (f, l) -> t = mkApps f l.
Proof. by apply/decompose_app_rec_inv. Qed.

Lemma nApp_decompose_app t l : ~~ isApp t -> decompose_app_rec t l = pair t l.
Proof. destruct t; simpl; congruence. Qed.

Lemma mkApps_eq_decompose_app_rec {f args t l} :
  mkApps f args = t ->
  ~~ isApp f ->
  match decompose_app_rec t l with
  | (f', args') => f' = f /\ mkApps t l = mkApps f' args'
  end.
Proof.
  revert f t l.
  induction args using rev_ind; simpl.
  - intros * -> **. rewrite nApp_decompose_app; auto.
  - intros. rewrite mkApps_app in H.
    specialize (IHargs f).
    destruct (isApp t) eqn:Heq.
    destruct t; try discriminate.
    simpl in Heq. inv H. simpl.
    specialize (IHargs (mkApps f args) (t2 :: l) eq_refl H0).
    destruct decompose_app_rec. intuition.
    subst t.
    simpl in Heq. discriminate.
Qed.

Lemma decompose_app_eq_right t l l' : decompose_app_rec t l = decompose_app_rec t l' -> l = l'.
Proof.
  induction t in l, l' |- *; simpl; intros [=]; auto.
  specialize (IHt1 _ _ H0). now inv IHt1.
Qed.

Lemma mkApps_eq_right t l l' : mkApps t l = mkApps t l' -> l = l'.
Proof.
  intros. eapply (f_equal decompose_app) in H. unfold decompose_app in H.
  rewrite !decompose_app_rec_mkApps in H. apply decompose_app_eq_right in H.
  now rewrite !app_nil_r in H.
Qed.

Lemma mkApps_eq_decompose' {f args t} :
  mkApps f args = t ->
  ~~ isApp f ->
  match decompose_app t with
  | (f', args') => f' = f /\ args' = args /\ t = mkApps f' args'
  end.
Proof.
  intros.
  have H' := (@mkApps_eq_decompose_app_rec f args t [] H H0).
  rewrite /decompose_app. destruct (decompose_app_rec t []).
  intuition subst; auto. simpl in H2. now eapply mkApps_eq_right in H2.
Qed.


Lemma decompose_app_rec_notApp :
  forall t l u l',
    decompose_app_rec t l = (u, l') ->
    ~~ isApp u.
Proof.
  intros t l u l' e.
  induction t in l, u, l', e |- *.
  all: try (cbn in e ; inversion e ; reflexivity).
  cbn in e. eapply IHt1. eassumption.
Qed.

Lemma decompose_app_notApp :
  forall t u l,
    decompose_app t = (u, l) ->
    ~~ isApp u.
Proof.
  intros t u l e.
  eapply decompose_app_rec_notApp. eassumption.
Qed.

Inductive mkApps_spec : term -> list term -> term -> list term -> term -> Type :=
| mkApps_intro f l n :
    ~~ isApp f ->
    mkApps_spec f l (mkApps f (firstn n l)) (skipn n l) (mkApps f l).

Lemma decompose_app_rec_eq f l :
  ~~ isApp f ->
  decompose_app_rec f l = (f, l).
Proof.
  destruct f; simpl; try discriminate; congruence.
Qed.
Close Scope string_scope.

Lemma firstn_add {A} x y (args : list A) : firstn (x + y) args = firstn x args ++ firstn y (skipn x args).
Proof.
  induction x in y, args |- *. simpl. reflexivity.
  simpl. destruct args. simpl.
  now rewrite firstn_nil.
  rewrite IHx. now rewrite app_comm_cons.
Qed.

Lemma decompose_app_rec_inv' f l hd args :
  decompose_app_rec f l = (hd, args) ->
  ∑ n, ~~ isApp hd /\ l = skipn n args /\ f = mkApps hd (firstn n args).
Proof.
  destruct (isApp f) eqn:Heq.
  revert l args hd.
  induction f; try discriminate. intros.
  simpl in H.
  destruct (isApp f1) eqn:Hf1.
  2:{ rewrite decompose_app_rec_eq in H => //. now apply negbT.
      revert Hf1.
      inv H. exists 1. simpl. intuition auto. now eapply negbT. }
  destruct (IHf1 eq_refl _ _ _ H).
  clear IHf1.
  exists (S x); intuition auto. eapply (f_equal (skipn 1)) in H2.
  rewrite [l]H2. now rewrite skipn_skipn Nat.add_1_r.
  rewrite -Nat.add_1_r firstn_add H3 -H2.
  now rewrite -[tApp _ _](mkApps_app hd _ [f2]).
  rewrite decompose_app_rec_eq; auto. now apply negbT.
  move=> [] H ->. subst f. exists 0. intuition auto.
  now apply negbT.
Qed.

Lemma mkApps_elim_rec t l l' :
  let app' := decompose_app_rec (mkApps t l) l' in
  mkApps_spec app'.1 app'.2 t (l ++ l') (mkApps t (l ++ l')).
Proof.
  destruct app' as [hd args] eqn:Heq.
  subst app'.
  rewrite decompose_app_rec_mkApps in Heq.
  have H := decompose_app_rec_inv' _ _ _ _ Heq.
  destruct H. simpl. destruct a as [isapp [Hl' Hl]].
  subst t.
  have H' := mkApps_intro hd args x. rewrite Hl'.
  rewrite -mkApps_app. now rewrite firstn_skipn.
Qed.

Lemma mkApps_elim t l  :
  let app' := decompose_app (mkApps t l) in
  mkApps_spec app'.1 app'.2 t l (mkApps t l).
Proof.
  have H := @mkApps_elim_rec t l [].
  now rewrite app_nil_r in H.
Qed.

Lemma mkApps_eq_inj {t t' l l'} :
  mkApps t l = mkApps t' l' ->
  ~~ isApp t -> ~~ isApp t' -> t = t' /\ l = l'.
Proof.
  intros Happ Ht Ht'. eapply (f_equal decompose_app) in Happ. unfold decompose_app in Happ.
  rewrite !decompose_app_rec_mkApps in Happ. rewrite !nApp_decompose_app in Happ; auto.
  rewrite !app_nil_r in Happ. intuition congruence.
Qed.

Ltac solve_discr :=
  match goal with
    H : mkApps _ _ = mkApps ?f ?l |- _ =>
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence
  | H : ?t = mkApps ?f ?l |- _ =>
    change t with (mkApps t []) in H ;
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence
  | H : mkApps ?f ?l = ?t |- _ =>
    change t with (mkApps t []) in H ;
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence
  end.

Definition isEvar t :=
  match t with
  | tEvar _ _ => true
  | _ => false
  end.

Definition isFix t :=
  match t with
  | tFix _ _ => true
  | _ => false
  end.

Definition isCoFix t :=
  match t with
  | tCoFix _ _ => true
  | _ => false
  end.

Definition isConstruct t :=
  match t with
  | tConstruct _ _ => true
  | _ => false
  end.

Definition isBox t :=
  match t with
  | tBox => true
  | _ => false
  end.

Local Open Scope string_scope.

Definition string_of_def {A : Set} (f : A -> string) (def : def A) :=
  "(" ++ string_of_name (dname def) ++ "," ++ f (dbody def) ++ ","
      ++ string_of_nat (rarg def) ++ ")".

Fixpoint string_of_term (t : term) : string :=
  match t with
  | tBox => "∎"
  | tRel n => "Rel(" ++ string_of_nat n ++ ")"
  | tVar n => "Var(" ++ n ++ ")"
  | tEvar ev args => "Evar(" ++ string_of_nat ev ++ "[]" (* TODO *)  ++ ")"
  | tLambda na t => "Lambda(" ++ string_of_name na ++ "," ++ string_of_term t ++ ")"
  | tLetIn na b t => "LetIn(" ++ string_of_name na ++ "," ++ string_of_term b ++ "," ++ string_of_term t ++ ")"
  | tApp f l => "App(" ++ string_of_term f ++ "," ++ string_of_term l ++ ")"
  | tConst c => "Const(" ++ c ++ ")"
  | tConstruct i n => "Construct(" ++ string_of_inductive i ++ "," ++ string_of_nat n ++ ")"
  | tCase (ind, i) t brs =>
    "Case(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_term t ++ ","
            ++ string_of_list (fun b => string_of_term (snd b)) brs ++ ")"
  | tProj (ind, i, k) c =>
    "Proj(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_nat k ++ ","
            ++ string_of_term c ++ ")"
  | tFix l n => "Fix(" ++ (string_of_list (string_of_def string_of_term) l) ++ "," ++ string_of_nat n ++ ")"
  | tCoFix l n => "CoFix(" ++ (string_of_list (string_of_def string_of_term) l) ++ "," ++ string_of_nat n ++ ")"
  end.
