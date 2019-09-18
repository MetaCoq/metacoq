(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaCoq.Template Require Import config utils Ast AstUtils.
Require Import ssreflect ssrbool.

(** * Inversion lemmas for the well-formedness judgement *)

Fixpoint wf_Inv (t : term) :=
  match t with
  | tRel _ | tVar _ | tSort _ => True
  | tEvar n l => Forall wf l
  | tCast t k t' => wf t /\ wf t'
  | tProd na t b => wf t /\ wf b
  | tLambda na t b => wf t /\ wf b
  | tLetIn na t b b' => wf t /\ wf b /\ wf b'
  | tApp t u => isApp t = false /\ u <> nil /\ wf t /\ Forall wf u
  | tConst _ _ | tInd _ _ | tConstruct _ _ _ => True
  | tCase ci p c brs => wf p /\ wf c /\ Forall (Program.Basics.compose wf snd) brs
  | tProj p t => wf t
  | tFix mfix k => Forall (fun def => wf def.(dtype) /\ wf def.(dbody) /\ isLambda def.(dbody) = true) mfix
  | tCoFix mfix k => Forall (fun def => wf def.(dtype) /\ wf def.(dbody)) mfix
  end.

Lemma wf_inv t (w : Ast.wf t) : wf_Inv t.
Proof.
  induction w; simpl; auto.
Defined.

Lemma decompose_app_mkApps f l :
  ~~ isApp f -> decompose_app (mkApps f l) = (f, l).
Proof.
  intros Hf. rewrite /decompose_app.
  destruct l. simpl. destruct f; try discriminate; auto.
  remember (mkApps f (t :: l)) eqn:Heq. simpl in Heq.
  destruct f; simpl in *; subst; auto. discriminate.
Qed.

Lemma atom_decompose_app t : ~~ isApp t -> decompose_app t = (t, []).
Proof. destruct t; simpl; congruence. Qed.

Lemma mkApps_eq_inj {t t' l l'} :
  mkApps t l = mkApps t' l' ->
  ~~ isApp t -> ~~ isApp t' -> t = t' /\ l = l'.
Proof.
  intros Happ Ht Ht'. eapply (f_equal decompose_app) in Happ.
  rewrite !decompose_app_mkApps in Happ => //. intuition congruence.
Qed.

Inductive mkApps_spec : term -> list term -> term -> list term -> term -> Type :=
| mkApps_intro f l n :
    ~~ isApp f ->
    mkApps_spec f l (mkApps f (firstn n l)) (skipn n l) (mkApps f l).

Lemma firstn_add {A} x y (args : list A) : firstn (x + y) args = firstn x args ++ firstn y (skipn x args).
Proof.
  induction x in y, args |- *. simpl. reflexivity.
  simpl. destruct args. simpl.
  now rewrite firstn_nil.
  rewrite IHx. now rewrite app_comm_cons.
Qed.
Definition is_empty {A} (l : list A) :=
  if l is nil then true else false.

Lemma is_empty_app {A} (l l' : list A) : is_empty (l ++ l') = is_empty l && is_empty l'.
Proof.
  induction l; simpl; auto.
Qed.

Fixpoint wf_term (t : term) : bool :=
  match t with
  | tRel _ | tVar _ => true
  | tEvar n l => forallb wf_term l
  | tSort u => true
  | tCast t k t' => wf_term t && wf_term t'
  | tProd na t b => wf_term t && wf_term b
  | tLambda na t b => wf_term t && wf_term b
  | tLetIn na t b b' => wf_term t && wf_term b && wf_term b'
  | tApp t u => ~~ isApp t && ~~ is_empty u && wf_term t && forallb wf_term u
  | tConst _ _ | tInd _ _ | tConstruct _ _ _ => true
  | tCase ci p c brs => wf_term p && wf_term c && forallb (Program.Basics.compose wf_term snd) brs
  | tProj p t => wf_term t
  | tFix mfix k =>
    forallb (fun def => wf_term def.(dtype) && wf_term def.(dbody) && isLambda def.(dbody)) mfix
  | tCoFix mfix k =>
    forallb (fun def => wf_term def.(dtype) && wf_term def.(dbody)) mfix
  end.

Lemma mkApps_tApp f args :
  ~~ isApp f ->
  ~~ is_empty args ->
  tApp f args = mkApps f args.
Proof.
  intros.
  destruct args, f; try discriminate; auto.
Qed.

Lemma decompose_app_inv' f l hd args : wf_term f ->
                                       decompose_app (mkApps f l) = (hd, args) ->
                                       ∑ n, ~~ isApp hd /\ l = skipn n args /\ f = mkApps hd (firstn n args).
Proof.
  destruct (isApp f) eqn:Heq.
  revert l args hd.
  induction f; try discriminate. intros.
  simpl in H.
  move/andP: H => [/andP [/andP [isAppf Hargs] wff] wfargs].
  rewrite mkApps_tApp in H0 => //. rewrite mkApps_nested in H0.
  rewrite decompose_app_mkApps in H0; auto. inversion H0. subst.
  exists #|args|; split; auto. rewrite skipn_all_app.
  rewrite firstn_app. rewrite firstn_all2. lia.
  rewrite Nat.sub_diag firstn_O app_nil_r. split; auto.
  now rewrite mkApps_tApp.

  intros wff fl.
  rewrite decompose_app_mkApps in fl; auto. now apply negbT.
  inversion fl. subst; exists 0.
  split; auto. now eapply negbT.
Qed.

Lemma mkApps_elim t l : wf_term t ->
                        let app' := decompose_app (mkApps t l) in
                        mkApps_spec app'.1 app'.2 t l (mkApps t l).
Proof.
  destruct app' as [hd args] eqn:Heq.
  subst app'.
  have H' := decompose_app_inv' _ _ _ _ H Heq.
  destruct H'. simpl. destruct a as [isapp [Hl' Hl]].
  subst t.
  have H' := mkApps_intro hd args x. rewrite Hl'.
  rewrite mkApps_nested. now rewrite firstn_skipn.
Qed.

Lemma nApp_mkApps {t l} : ~~ isApp (mkApps t l) -> ~~ isApp t /\ l = [].
Proof.
  induction l in t |- *; simpl; auto.
  intros. destruct (isApp t) eqn:Heq. destruct t; try discriminate.
  destruct t; try discriminate.
Qed.

Lemma mkApps_nisApp {t t' l} : mkApps t l = t' -> ~~ isApp t' -> t = t' /\ l = [].
Proof.
  intros <-. intros. eapply nApp_mkApps in H. intuition auto.
  now subst.
Qed.

Ltac solve_discr' :=
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
