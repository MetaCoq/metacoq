(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICSize.
Require Import List Program Lia.
Require Import BinPos.
Require Import Coq.Arith.Compare_dec Bool.
Set Asymmetric Patterns.

(** * Deriving a compact induction principle for terms

  Allows to get the right induction principle on lists of terms appearing
  in the term syntax (in evar, applications, branches of cases and (co-)fixpoints. *)

Notation prim_ind P p := (P (tPrim p)).

(** Custom induction principle on syntax, dealing with the various lists appearing in terms. *)

Lemma term_forall_list_ind :
  forall P : term -> Type,
    (forall n : nat, P (tRel n)) ->
    (forall i : ident, P (tVar i)) ->
    (forall (n : nat) (l : list term), All P l -> P (tEvar n l)) ->
    (forall s, P (tSort s)) ->
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tProd n t t0)) ->
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tLambda n t t0)) ->
    (forall (n : aname) (t : term),
        P t -> forall t0 : term, P t0 -> forall t1 : term, P t1 -> P (tLetIn n t t0 t1)) ->
    (forall t u : term, P t -> P u -> P (tApp t u)) ->
    (forall s (u : list Level.t), P (tConst s u)) ->
    (forall (i : inductive) (u : list Level.t), P (tInd i u)) ->
    (forall (i : inductive) (n : nat) (u : list Level.t), P (tConstruct i n u)) ->
    (forall (ind : case_info) (p : predicate term),
        tCasePredProp P P p -> forall c : term, P c -> forall l : list (branch term),
        tCaseBrsProp P l -> P (tCase ind p c l)) ->
    (forall (s : projection) (t : term), P t -> P (tProj s t)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P P m -> P (tFix m n)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P P m -> P (tCoFix m n)) ->
    (forall p, prim_ind P p) ->
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
  split.
  generalize (pparams p).
  fix auxl' 1.
  destruct l; constructor; [|apply auxl']. apply auxt.
  apply auxt.

  revert brs.
  fix auxl' 1.
  destruct brs; constructor; [|apply auxl'].
  apply auxt.

  revert mfix.
  fix auxm 1.
  destruct mfix; constructor; [|apply auxm].
  split; apply auxt.
  revert mfix.
  fix auxm 1.
  destruct mfix; constructor; [|apply auxm].
  split; apply auxt.
Defined.


Inductive ForallT {A} (P : A -> Type) : list A -> Type :=
| ForallT_nil : ForallT P []
| ForallT_cons : forall (x : A) (l : list A), P x -> ForallT P l -> ForallT P (x :: l).

Definition tCaseBrsType {A} (P : A -> Type) (l : list (nat * A)) :=
  ForallT (fun x => P (snd x)) l.

Definition tFixType {A : Set} (P P' : A -> Type) (m : mfixpoint A) :=
  ForallT (fun x : def A => P x.(dtype) * P' x.(dbody))%type m.

Lemma size_decompose_app_rec t L :
  list_size size L + size t = size (decompose_app_rec t L).1 + list_size size (decompose_app_rec t L).2.
Proof.
  induction t in L |- *; cbn; try lia.
  rewrite <- IHt1. cbn. lia.
Qed.    

Lemma size_decompose_app t :
  size t = size (decompose_app t).1 + list_size size (decompose_app t).2.
Proof.
  unfold decompose_app.
  eapply (size_decompose_app_rec t []).
Qed.

Lemma decompose_app_rec_length_mono t L1 L2 :
  length L1 <= length L2 ->
  length (decompose_app_rec t L1).2 <= length (decompose_app_rec t L2).2.
Proof.
  intros. induction t in L1, L2, H |- *; cbn; try lia.
  eapply IHt1. cbn. lia.
Qed.

Lemma decompose_app_rec_length t L :
  length (decompose_app_rec t L).2 >= length L.
Proof.
  induction t in L |- * ; cbn; try lia.
  unfold ge. etransitivity. eapply IHt1.
  eapply decompose_app_rec_length_mono. cbn. lia.
Qed.

Lemma decompose_app_size_tApp1 t1 t2 :
  size (decompose_app (tApp t1 t2)).1 < size (tApp t1 t2).
Proof.
  rewrite size_decompose_app with (t := tApp t1 t2). cbn.
  pose proof (decompose_app_rec_length t1 [t2]). cbn in H.
  pose proof (list_size_length size (decompose_app_rec t1 [t2]).2).
  lia.
Qed.

Lemma decompose_app_size_tApp2 t1 t2 :
  Forall (fun t => size t < size (tApp t1 t2)) (decompose_app (tApp t1 t2)).2.
Proof.
  destruct decompose_app eqn:da.
  eapply decompose_app_inv in da. rewrite da. simpl. clear da.
  induction l using rev_ind; try constructor.
  eapply app_Forall; [|constructor].
  eapply Forall_impl; eauto; simpl; intros.
  rewrite <- mkApps_nested; simpl. lia.
  rewrite <- mkApps_nested; simpl. lia.
  constructor.
Qed.

Definition mkApps_decompose_app_rec t l :
  mkApps t l = mkApps  (fst (decompose_app_rec t l)) (snd (decompose_app_rec t l)).
Proof.
  revert l; induction t; try reflexivity.
  intro l; cbn in *.
  transitivity (mkApps t1 ((t2 ::l))). reflexivity.
  now rewrite IHt1.
Defined.

Definition mkApps_decompose_app t :
  t = mkApps  (fst (decompose_app t)) (snd (decompose_app t))
  := mkApps_decompose_app_rec t [].

  Section Reverse_Induction.

    Variable A : Type.

    Lemma rev_list_ind : forall P:list A-> Type,
      P [] ->
      (forall (a:A) (l:list A), P (rev l) -> P (rev (a :: l))) ->
      forall l:list A, P (rev l).
    Proof.
      induction l; auto.
    Defined.

    Let app_nil_r : forall l:list A, l ++ [] = l.
    Proof.
      induction l; simpl; f_equal; auto.
    Defined.

    Let app_assoc : forall l m n:list A, l ++ m ++ n = (l ++ m) ++ n.
    Proof.
      intros l m n; induction l; simpl; f_equal; auto.
    Defined.

    Let rev_app_distr : forall x y:list A, rev (x ++ y) = rev y ++ rev x.
    Proof.
      induction x as [| a l IHl].
      destruct y as [| a l].
      simpl.
      auto.

      simpl.
      rewrite app_nil_r; auto.

      intro y.
      simpl.
      rewrite (IHl y).
      rewrite app_assoc; trivial.
    Defined.

    Let rev_unit : forall (l:list A) (a:A), rev (l ++ [a]) = a :: rev l.
    Proof.
      intros.
      apply (rev_app_distr l [a]); simpl; auto.
    Defined.

    Let rev_involutive : forall l:list A, rev (rev l) = l.
    Proof.
      induction l as [| a l IHl].
      simpl; auto.

      simpl.
      rewrite (rev_unit (rev l) a).
      rewrite IHl; auto.
    Defined.

    Theorem rev_rec : forall P:list A -> Type,
      P [] ->
      (forall (x:A) (l:list A), P l -> P (l ++ [x])) -> forall l:list A, P l.
    Proof.
      intros.
      generalize (rev_involutive l).
      intros E; rewrite <- E.
      apply (rev_list_ind P).
      - auto.
      - simpl.
        intros.
        apply (X0 a (rev l0)).
        auto.
    Defined.

  End Reverse_Induction.

From Equations Require Import Equations.

Lemma term_forall_mkApps_ind :
  forall P : term -> Type,
    (forall n : nat, P (tRel n)) ->
    (forall i : ident, P (tVar i)) ->
    (forall (n : nat) (l : list term), All P l -> P (tEvar n l)) ->
    (forall s, P (tSort s)) ->
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tProd n t t0)) ->
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tLambda n t t0)) ->
    (forall (n : aname) (t : term),
        P t -> forall t0 : term, P t0 -> forall t1 : term, P t1 -> P (tLetIn n t t0 t1)) ->
    (forall t : term, forall v, ~ isApp t -> P t -> All P v -> P (mkApps t v)) ->
    (forall (s : kername) (u : list Level.t), P (tConst s u)) ->
    (forall (i : inductive) (u : list Level.t), P (tInd i u)) ->
    (forall (i : inductive) (n : nat) (u : list Level.t), P (tConstruct i n u)) ->
    (forall (ind : case_info) (p : predicate term),
        tCasePredProp P P p ->
        forall c : term, P c -> forall l : list (branch term),
            tCaseBrsProp P l -> P (tCase ind p c l)) ->
    (forall (s : projection) (t : term), P t -> P (tProj s t)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P P m -> P (tFix m n)) ->
    (forall (m : mfixpoint term) (n : nat), tFixProp P P m -> P (tCoFix m n)) ->
    (forall i, prim_ind P i) ->
    forall t : term, P t.
Proof.
  intros until t.
  rename X14 into Pprim.
  assert (Acc (MR lt size) t) by eapply measure_wf, Wf_nat.lt_wf.
  induction H. rename X14 into auxt. clear H. rename x into t.
  move auxt at top.
  
  destruct t; try now repeat (match goal with
                 H : _ |- _ => apply H; try (hnf; cbn; lia)
              end).

  - eapply X1. revert l auxt. unfold MR; cbn. fix auxt' 1.
    destruct l; constructor. apply auxt. hnf; cbn; lia. apply auxt'. intros. apply auxt.
    hnf in *; cbn in *. lia. 

  - rewrite mkApps_decompose_app.
    destruct decompose_app eqn:E. cbn.
    eapply X6.
    + eapply decompose_app_notApp in E. eauto.
    + eapply auxt. cbn. hnf. pose proof (decompose_app_size_tApp1 t1 t2). rewrite E in *. hnf in *; cbn in *. lia.
    + induction l using rev_rec in E, auxt, t1, t2, t |- *.
      * econstructor.
      * eapply All_app_inv.
        2:{ 
        econstructor. eapply auxt. hnf; cbn.
        pose proof (decompose_app_size_tApp2 t1 t2). rewrite E in *. cbn in H. clear E.
        eapply Forall_All, All_app in H as [H H1]. inv H1. lia. econstructor. }
        destruct (isApp t1) eqn:Et1.
        -- destruct t1; try now inv Et1.
           pose proof E as E'.
           eapply IHl.
           2:{ 
           eapply decompose_app_inv in E. rewrite <- mkApps_nested in E.
           cbn in E. noconf E. rewrite H.
                                               rewrite decompose_app_mkApps. reflexivity.
                                               eapply decompose_app_notApp in E'.
                                               now rewrite E'.
           }
           eapply decompose_app_inv in E. rewrite <- mkApps_nested in E.
           cbn in E. noconf E. 
           intros. eapply auxt.
           red. red in H0. cbn in *. lia.
        -- destruct l.
           econstructor.
           exfalso.
           pose proof (decompose_app_mkApps t1 [t2]). cbn in H.
           cbn in E. rewrite H in E.
           inversion E. destruct l; inv H3.
           now rewrite Et1.
  - eapply X10; [|apply auxt; hnf; cbn; lia.. | ].
    split; [|apply auxt; hnf; cbn; lia].
    unfold MR in auxt. simpl in auxt. revert auxt.
    generalize (pparams p).
    fix auxt' 1.
    destruct l; constructor. apply auxt. hnf; cbn; lia. apply auxt'. intros. apply auxt.
    hnf in *; cbn in *. lia. 
    rename brs into l.
    revert l auxt. unfold MR; cbn. fix auxt' 1.
    destruct l; constructor. apply auxt. hnf; cbn; lia. apply auxt'. intros. apply auxt.
    hnf in *; cbn in *. lia. 
  - eapply X12; [apply auxt; hnf; cbn; lia.. | ]. rename mfix into l.
    revert l auxt. unfold MR; cbn. fix auxt' 1.
    destruct l; constructor. split.
    apply auxt. hnf; cbn. unfold def_size. lia.
    apply auxt. hnf; cbn. unfold def_size. lia.   
    apply auxt'. intros. apply auxt.
    hnf in *; cbn in *. unfold mfixpoint_size, def_size in *. lia. 

  - eapply X13; [apply auxt; hnf; cbn; lia.. | ]. rename mfix into l.
    revert l auxt. unfold MR; cbn. fix auxt' 1.
    destruct l; constructor. split.
    apply auxt. hnf; cbn. unfold def_size. lia.
    apply auxt. hnf; cbn. unfold def_size. lia.   
    apply auxt'. intros. apply auxt.
    hnf in *; cbn in *. unfold mfixpoint_size, def_size in *. lia. 
Defined.

Lemma ctx_length_ind (P : context -> Type) (p0 : P [])
  (pS : forall d Γ, (forall Γ', #|Γ'| <= #|Γ|  -> P Γ') -> P (d :: Γ)) 
  Γ : P Γ.
Proof.
  generalize (le_n #|Γ|).
  generalize #|Γ| at 2.
  induction n in Γ |- *.
  destruct Γ; [|simpl; intros; elimtype False; lia].
  intros. apply p0.
  intros.
  destruct Γ; simpl in *.
  apply p0. apply pS. intros. apply IHn. simpl. lia.
Qed.

Lemma ctx_length_rev_ind (P : context -> Type) (p0 : P [])
  (pS : forall d Γ, (forall Γ', #|Γ'| <= #|Γ|  -> P Γ') -> P (Γ ++ [d])) 
  Γ : P Γ.
Proof.
  generalize (le_n #|Γ|).
  generalize #|Γ| at 2.
  induction n in Γ |- *.
  destruct Γ using MCList.rev_ind; [|simpl; rewrite app_length; simpl; intros; elimtype False; try lia].
  intros. apply p0.
  destruct Γ using MCList.rev_ind; simpl in *; rewrite ?app_length; simpl; intros Hlen.
  intros. apply p0.
  apply pS. intros. apply IHn. simpl. lia.
Qed.
